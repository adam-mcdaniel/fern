#!/usr/bin/env python3
"""Colours every placed cell of bf_chip by the block it belongs to.

usage: cellmap_render.py cells.json out.png stats.json
cells.json comes from cellmap.py.  Flip-flops are assigned by their output
net name; logic cells by which flip-flops (or output pins) they feed, the
same way hw/schematic/split.py assigns gates to sheets.
"""

import json
import re
import sys
from collections import defaultdict

from PIL import Image, ImageDraw

# Colours are a colour-blind-checked categorical palette for a dark surface.
BLOCKS = [
    # key, label, colour, net-name pattern for flip-flops / output pins
    ("pstack", "Pointer stack (64 × 16)", "#3987e5", r"^cpu\.(pstack|ptop|psp)"),
    ("rstack", "Return stack (64 × 12)", "#d95926", r"^cpu\.(rstack|rtop|rsp)"),
    ("uart", "UART + RX FIFO", "#199e70", r"^(rx|tx|rx_fifo)\.|^uart_tx"),
    ("a", "Accumulator A", "#c98500", r"^cpu\.a\b"),
    ("p", "Tape pointer P", "#d55181", r"^cpu\.p\b|^dmem_addr"),
    ("pc", "Program counter", "#008300", r"^cpu\.pc\b|^imem_addr"),
    ("o", "Operand register O", "#9085e9", r"^cpu\.o\b"),
    ("ctrl", "Control, decode, tape write", "#e66767", r"^cpu\.state|^halted|^dmem_we|^dmem_wdata"),
]
CLOCK = ("clock", "Clock tree", "#c3c8cb")
FILL = ("fill", "Filler, decap, well taps", "#232b2f")
CLOCK_NET = "clk"


def classify(cells):
    """Returns (owner, kind): the block key and the cell kind of each cell."""
    unescape = lambda n: n.replace("\\", "")

    def block_of_name(name):
        for key, _, _, pattern in BLOCKS:
            if re.search(pattern, unescape(name)):
                return key
        return None

    driver = {}
    readers = defaultdict(list)
    for i, c in enumerate(cells):
        for n in c[5]:
            driver[n] = i
        for n in c[6]:
            readers[n].append(i)

    kind = {}
    for i, c in enumerate(cells):
        m = c[4]
        if re.search(r"__(decap|fill|tapvpwrvgnd|diode)", m):
            kind[i] = FILL[0]
        elif re.search(r"__clk", m):
            kind[i] = CLOCK[0]
        elif "__df" in m:
            kind[i] = "ff"
        else:
            kind[i] = "logic"

    # Flip-flops: by output net, or by the named net their output buffer drives.
    owner = {}
    for i, c in enumerate(cells):
        if kind[i] != "ff":
            continue
        key = next((block_of_name(n) for n in c[5] if block_of_name(n)), None)
        if key is None:
            for n in c[5]:
                for r in readers[n]:
                    key = key or next((block_of_name(m) for m in cells[r][5]
                                       if block_of_name(m)), None)
        owner[i] = key or "ctrl"

    # Logic: walk back from every flip-flop input and output pin.
    member = defaultdict(set)
    seeds = [(owner[i], n) for i in owner for n in cells[i][6] if n != CLOCK_NET]
    for i, c in enumerate(cells):
        if kind[i] == "logic":
            for n in c[5]:
                key = block_of_name(n)
                if key and not readers[n]:
                    seeds.append((key, n))
    for key, net in seeds:
        stack, seen = [net], set()
        while stack:
            d = driver.get(stack.pop())
            if d is None or kind[d] != "logic" or d in seen:
                continue
            seen.add(d)
            member[d].add(key)
            stack += cells[d][6]
    for i in kind:
        if kind[i] == "logic":
            keys = member[i]
            owner[i] = next(iter(keys)) if len(keys) == 1 else "ctrl"
        elif kind[i] in (FILL[0], CLOCK[0]):
            owner[i] = kind[i]
    return owner, kind


def main(src, png, stats_path):
    data = json.load(open(src))
    x0, y0, x1, y1 = data["die"]
    cells = data["cells"]
    owner, kind = classify(cells)

    colours = {k: c for k, _, c, _ in BLOCKS}
    colours[CLOCK[0]] = CLOCK[2]
    colours[FILL[0]] = FILL[2]
    labels = {k: l for k, l, _, _ in BLOCKS}
    labels[CLOCK[0]] = CLOCK[1]
    labels[FILL[0]] = FILL[1]

    scale = 6.0
    W, H = int((x1 - x0) * scale), int((y1 - y0) * scale)
    img = Image.new("RGB", (W, H), "#14191c")
    draw = ImageDraw.Draw(img)
    order = sorted(range(len(cells)), key=lambda i: owner[i] != FILL[0])
    for i in order:
        x, y, w, h = cells[i][:4]
        X0 = (x - x0) * scale
        Y0 = H - (y + h - y0) * scale
        draw.rectangle([X0, Y0, X0 + w * scale - 1, Y0 + h * scale - 1],
                       fill=colours[owner[i]])
    img.save(png, optimize=True)

    stats = defaultdict(lambda: {"cells": 0, "area": 0.0, "ffs": 0})
    for i, c in enumerate(cells):
        s = stats[owner[i]]
        s["cells"] += 1
        s["area"] += c[2] * c[3]
        s["ffs"] += kind[i] == "ff"
    rows = [{"key": k, "label": labels[k], "colour": colours[k], **stats[k]}
            for k in [b[0] for b in BLOCKS] + [CLOCK[0], FILL[0]]]
    json.dump({"die": [x1 - x0, y1 - y0], "blocks": rows}, open(stats_path, "w"), indent=1)
    for r in rows:
        print(f"{r['label']:30} {r['cells']:6} cells {r['ffs']:5} ff {r['area']:10.0f} um2")


if __name__ == "__main__":
    main(*sys.argv[1:])
