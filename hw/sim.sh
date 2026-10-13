#!/bin/sh
# Usage: [XLEN=16] hw/sim.sh <program.bf> [stdin-file]
# Compiles the program for the CPU and runs it in Icarus Verilog.
# XLEN sets the cell width in bits (8 to 64, default 64).
set -e
here=$(cd "$(dirname "$0")" && pwd)
build="$here/build"
mkdir -p "$build"
xlen=${XLEN:-64}

cargo run --quiet --manifest-path "$here/../Cargo.toml" -- --hex --xlen "$xlen" "$1" > "$build/program.hex"

# Size instruction memory to fit the program (at least 4 KiB, but no more
# than the cells can address), and fill the rest with HALT so $readmemh sees
# exactly one word per byte of memory.
size=$(wc -l < "$build/program.hex")
aw=$((xlen < 12 ? xlen : 12))
while [ $((1 << aw)) -lt "$size" ]; do aw=$((aw + 1)); done
yes 60 | head -n $(((1 << aw) - size)) >> "$build/program.hex"

iverilog -g2012 -o "$build/tb.vvp" \
    -P tb.PROG="\"$build/program.hex\"" -P tb.IMEM_AW=$aw \
    -P tb.XLEN=$xlen -P tb.DMEM_AW=$((xlen < 12 ? xlen : 12)) \
    "$here/tb.v" "$here/bf_soc.v" "$here/bf_chip.v" "$here/bf_cpu.v" "$here/uart.v"
vvp -n "$build/tb.vvp" ${2:+"+in=$2"}
