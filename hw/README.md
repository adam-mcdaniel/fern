# bf CPU

A small CPU that runs the brainfuck extension from `src/lib.rs` directly, with
`,` and `.` wired to a UART.

```
hw/bf_cpu.v           the core (program and tape memories are external ports)
hw/uart.v             8N1 UART transmitter/receiver + RX FIFO
hw/bf_chip.v          core + UART with memory pins: the top level for an ASIC
hw/bf_soc.v           bf_chip + block-RAM memories: the top level for an FPGA
hw/tb.v               simulation testbench (drives RX from a file, decodes TX)
hw/sim.sh             compile a .bf program and run it in Icarus Verilog
hw/test.sh            run hw/tests/*.bf on the CPU and the C backend, compare
hw/schematic/gates.sh gate-level schematics (one sheet per register)
hw/asic/              LibreLane config and render scripts for a SkyWater 130 nm layout
```

## Quick start

```sh
brew install icarus-verilog
hw/sim.sh hw/tests/hello.bf                      # -> Hello, UART!
hw/sim.sh hw/tests/echo.bf hw/tests/echo.in      # second arg is stdin
XLEN=16 hw/sim.sh hw/tests/hello.bf              # 16-bit variant
hw/test.sh                                       # differential tests
```

`bfc --hex [--xlen N] prog.bf > program.hex` produces the program image (one
byte per line, for `$readmemh`).

## Architecture

Harvard machine with `XLEN`-bit cells (default 64):

| State | Width | Purpose |
|---|---|---|
| `A` | `XLEN` | accumulator |
| `P` | `XLEN` | tape pointer, as a cell index |
| `PC` | `IMEM_AW` | program counter, as a byte address |
| `O` | `XLEN` | operand register, built by prefix bytes |
| pointer stack | 2^`PSTACK_AW` × `XLEN` | saved `P` for `*` / `&` |
| return stack | 2^`RSTACK_AW` × `IMEM_AW` | return addresses for `!` / `;` |

The tape is word-addressed, so `?` yields a cell index and pointer arithmetic
on it lines up with `>`/`<` (unlike the C backend, where `?` gives a byte
address).

## Cell width

`XLEN` can be anything from 8 to 64. All arithmetic wraps modulo 2^`XLEN`,
`#` treats cells as signed `XLEN`-bit values, and `.` sends the low byte.
Machine code doesn't depend on the width, because the prefix scheme builds
operands modulo the register size. `bfc --xlen N` uses that to pick shorter
encodings (on a 16-bit core `0xFFFF` is encoded as -1) and rejects programs
too large for `N`-bit code addresses. Code and tape addresses pass through `A`
and `P`, so the core refuses to elaborate unless `IMEM_AW` and `DMEM_AW` are
at most `XLEN`. An 8-bit core can therefore hold 256 bytes of program and 256
cells.

## Timing

Every instruction takes two clocks. FETCH latches the instruction byte, `M[P]`
and the top of both stacks from block RAM; EXEC executes. `,` waits for a
received byte and `.` waits for the transmitter to be free.

## Instruction set

Each instruction is one byte: a 4-bit opcode and a 4-bit operand nibble `n`.
The effective operand is `O | n`. `PFX`/`NFX` build wider operands in `O`
(the Transputer scheme), and every other instruction clears `O`.

| Opcode | Name | Effect |
|---|---|---|
| `0` | `PFX n` | `O = (O \| n) << 4` |
| `1` | `NFX n` | `O = ~(O \| n) << 4` (negative operands) |
| `2` | `LIT k` | `A = k` |
| `3` | `MOV k` | `P = P + k` |
| `4` | `JZ k` | if `A == 0`: `PC = PC + 1 + k` |
| `5` | `JNZ k` | if `A != 0`: `PC = PC + 1 + k` |
| `6` | `OPR k` | zero-operand op `k`, below |
| `7`–`F` | | illegal: halts |

| `OPR` | Source | Effect |
|---|---|---|
| `0` | (end of program) | halt |
| `1` | `$` | `A = M[P]` |
| `2` | `=` | `M[P] = A` |
| `3` | `+` | `A = A + M[P]` |
| `4` | `-` | `A = -A` |
| `5` | `#` | `A = (A > 0)`, signed |
| `6` | `?` | `A = P` |
| `7` | `*` | push `P`; `P = M[P]` |
| `8` | `&` | `P = pop` |
| `9` | `!` | push `PC + 1`; `PC = A` |
| `A` | `;` | `PC = pop` |
| `B` | `,` | `A = byte from UART RX` (blocks) |
| `C` | `.` | send `A[7:0]` to UART TX (blocks) |

How the compiler maps the source:

- `>>>` → `MOV 3`, `<<` → `MOV -2`, `123` / `0x7b` / `0o173` → `LIT`.
- `@f` → `LIT <address of f>`. `!` calls whatever address is in `A`, so
  every label is called the same way.
- `[ body ]` → `JZ end; body; JNZ start`: loops test `A`, matching
  `while (acc)` in the C backend.
- Top-level code comes first and ends in `HALT`; function bodies follow, each
  ending in `RET`.
- Operands for labels and branches are sized by relaxation, so most branches
  and calls are 1–3 bytes.

## Using it on an FPGA

`bf_soc` is the top level:

| Port | |
|---|---|
| `clk` | system clock |
| `rst` | active-high, synchronous |
| `uart_rx`, `uart_tx` | to a USB-serial bridge, 8N1 |
| `halted` | high after the program ends (or hits an illegal instruction) |

| Parameter | Default | |
|---|---|---|
| `XLEN` | 64 | cell and register width, 8 to 64 |
| `CLKS_PER_BIT` | 104 | clock Hz / baud, e.g. 12 MHz / 115200 |
| `IMEM_INIT` | `"program.hex"` | program image from `bfc --hex` |
| `IMEM_AW` | 12 | 4 KiB of program |
| `DMEM_AW` | 12 | 4096 tape cells |
| `PSTACK_AW`, `RSTACK_AW` | 6 | 64-entry stacks |
| `RX_FIFO_AW` | 4 | 16-byte input buffer; bytes arriving when full are dropped |

Yosys synthesis results (all without warnings; 4096-cell tape unless noted):

| Target | `XLEN` | LUT4 | FFs | Block RAM |
|---|---|---|---|---|
| ECP5 | 16 | ~600 | ~165 | 6 DP16KD |
| ECP5 | 32 | ~630 | ~200 | 11 DP16KD |
| ECP5 | 64 | ~825 | ~290 | 20 DP16KD |
| iCE40 | 16 | ~470 | ~190 | 25 SB_RAM40_4K |
| iCE40 | 32 | ~690 | ~270 | 42 SB_RAM40_4K |
| iCE40 (`DMEM_AW=10`) | 64 | ~970 | ~430 | 28 SB_RAM40_4K |

An iCE40 HX8K has 32 block RAMs, so a 32-bit build needs `DMEM_AW=11`.

The program is baked into the bitstream through `$readmemh`, so changing it
means re-running synthesis. The program must fit in 2^`IMEM_AW` bytes: check
with `bfc --hex prog.bf | wc -l`.

## Memories

`bf_cpu` reads its program and tape through ports and expects synchronous
memories: data for an address arrives one clock later, and a write happens at
the clock edge when `dmem_we` is high. `bf_soc` provides these as block RAM.
`bf_chip` brings them out as pins (`imem_addr`/`imem_rdata`,
`dmem_addr`/`dmem_rdata`/`dmem_wdata`/`dmem_we`) for external synchronous
SRAM. The two stacks and the UART FIFO stay inside the chip.

## Schematics and chip layout

`hw/schematic/gates.sh` synthesizes `bf_chip` (16-bit by default) to AND, OR,
XOR, NOT and 2-input MUX gates plus D flip-flops, and draws it with
netlistsvg: one complete sheet plus one sheet per register, with cross-sheet
wires labelled by signal name. Needs `yosys`, `node` and `python3`.

`hw/asic/config.json` builds `bf_chip` at `XLEN=16` and 25 MHz in the
SkyWater 130 nm process with [LibreLane](https://github.com/librelane/librelane):

```sh
pip install librelane          # plus Docker, running
cd hw/asic
librelane --dockerized --run-tag final config.json
./render.sh final              # die, close-up and block-map images
```

The result is a 465 × 475 µm block with 72 pins. Most of its area is the
two stacks, which become flip-flops because the process has no small RAM
blocks.

## Differences from the C backend

- **The C backend always uses 64-bit cells.** Use `--xlen` / `XLEN` to match
  a narrower CPU. `hw/test.sh` compares against the C backend unless a test
  provides `<name>.<xlen>.out`.
- **No external functions.** Every `@label` must be defined in the program;
  `bfc --hex` rejects undefined labels such as `@putint` from `link.c`.
- **`,` has no EOF.** It blocks until a byte arrives.
- **Memory wraps instead of faulting.** `P` indexes the tape modulo its size,
  and the stacks wrap on overflow and underflow.
- **The tape starts zeroed.** The C backend `malloc`s it uninitialized.
