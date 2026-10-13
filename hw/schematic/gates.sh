#!/bin/sh
# Usage: [XLEN=16] [RAMS=gates] hw/schematic/gates.sh
# Synthesizes bf_chip to AND/OR/XOR/NOT/MUX gates and D flip-flops, then
# draws it with netlistsvg: one complete sheet plus one sheet per register.
# The stacks and FIFO are drawn as RAM blocks unless RAMS=gates, which
# expands them into flip-flops and multiplexers too.
# Output: hw/schematic/build/ or build-gates/  (needs yosys, node, netlistsvg)
set -e
here=$(cd "$(dirname "$0")" && pwd)
hw="$here/.."
if [ "${RAMS:-blocks}" = gates ]; then
    build="$here/build-gates"; memory="memory"
else
    build="$here/build"; memory="memory -nomap"
fi
mkdir -p "$build/sheets"
xlen=${XLEN:-16}
netlistsvg=${NETLISTSVG:-npx --yes netlistsvg@1.0.2}

# Named signals kept as wires so cross-sheet labels mean something.
keep="w:cpu.operand w:cpu.opcode w:cpu.is_opr w:cpu.stall w:cpu.pc_next
      w:cpu.in_ready w:cpu.out_valid w:cpu.p_push w:cpu.r_push"

yosys -q -p "
read_verilog -sv $hw/bf_cpu.v $hw/uart.v $hw/bf_chip.v
chparam -set XLEN $xlen bf_chip
hierarchy -top bf_chip
proc; flatten
setattr -set keep 1 $(echo $keep)
opt -full; $memory; opt -full
techmap; opt -full
abc -g AND,OR,XOR,MUX
dfflegalize -cell \$_DFF_P_ 01
techmap
opt_clean -purge
tee -q -o $build/stat.txt stat
write_json $build/gates.json
"
python3 "$here/split.py" "$build/gates.json" "$build/sheets"
$netlistsvg "$build/gates.json" -o "$build/complete.svg"
for f in "$build"/sheets/*.json; do
    case "$f" in */sheets.json) continue ;; esac
    $netlistsvg "$f" -o "${f%.json}.svg"
done

# netlistsvg lets long port labels hang off the left edge and leaves the
# background transparent: add a margin and a white drawing sheet.
python3 - "$build"/complete.svg "$build"/sheets/*.svg <<'PY'
import re, sys
for path in sys.argv[1:]:
    svg = open(path).read()
    m = re.search(r'<svg ([^>]*?)width="([\d.]+)" height="([\d.]+)"', svg)
    if not m or "viewBox" in m.group(0):
        continue
    w, h = float(m.group(2)), float(m.group(3))
    pad = 120
    head = (f'<svg {m.group(1)}width="{w + 2*pad:g}" height="{h + 2*pad:g}" '
            f'viewBox="{-pad:g} {-pad:g} {w + 2*pad:g} {h + 2*pad:g}"')
    svg = svg.replace(m.group(0), head, 1)
    svg = re.sub(r'(<svg [^>]*>)', r'\1<rect x="%g" y="%g" width="%g" height="%g" fill="#fff" stroke="none"/>'
                 % (-pad, -pad, w + 2*pad, h + 2*pad), svg, count=1)
    open(path, "w").write(svg)
PY
