#!/usr/bin/env python3
"""Assembles the whole-CPU gate poster.

usage: poster.py build_dir out.svg out.json
reads  build_dir/sheets/*.json, *.svg (from gates.sh and split.py)
       build_dir/arrays/*.svg       (from arrays.py)
writes out.svg: a block diagram of which block feeds which (laid out by
Graphviz), then every block's gate schematic in a frame coloured like the
die map, with the memory arrays drawn out bit by bit; and out.json with the
frame positions.
"""

import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

# sheet -> (die-map block colour, frame title)
BLOCK = {
    "decode": ("#e66767", "Shared decode"),
    "control": ("#e66767", "Control FSM"),
    "tape": ("#e66767", "Tape write port"),
    "o": ("#9085e9", "Operand register O"),
    "pc": ("#008300", "Program counter"),
    "a": ("#c98500", "Accumulator A"),
    "p": ("#d55181", "Tape pointer P"),
    "pstack": ("#3987e5", "Pointer stack"),
    "rstack": ("#d95926", "Return stack"),
    "uart_rx": ("#199e70", "UART receiver"),
    "fifo": ("#199e70", "RX FIFO"),
    "uart_tx": ("#199e70", "UART transmitter"),
}
# columns of frames, left to right, in rough data-flow order
COLUMNS = [["decode", ["control", "o"]], ["pc", "tape"], ["a", "p"],
           ["pstack", "rstack"], ["uart_rx", "fifo", "uart_tx"]]
ARRAYS = {"pstack", "rstack", "fifo"}
PINS = {"imem_rdata": "program SRAM", "imem_addr": "program SRAM",
        "dmem_rdata": "tape SRAM", "dmem_addr": "tape SRAM",
        "dmem_wdata": "tape SRAM", "dmem_we": "tape SRAM",
        "uart_rx": "I/O pins", "uart_tx": "I/O pins", "halted": "I/O pins"}

GAP = 220
HEAD = 170


def svg_size(text):
    m = re.search(r'<svg[^>]*?width="([\d.]+)"[^>]*?height="([\d.]+)"', text)
    return float(m.group(1)), float(m.group(2))


# The drawings' own stylesheets would apply to the whole poster, so they are
# dropped and replaced by these, scoped to each kind of drawing.
SCOPED = """
.ns{stroke:#000;fill:none}
.ns text{fill:#000;stroke:none;font-size:10px;font-weight:bold;font-family:"Courier New",monospace}
.ns .nodelabel{text-anchor:middle}
.ns .inputPortLabel{text-anchor:end}
.ns .splitjoinBody{fill:#000}
.arr path,.arr rect,.arr circle{fill:none;stroke:#000;stroke-width:1}
.arr .g{stroke:#9aa3a8}
.arr .d{fill:#000;stroke:none}
.arr text{font:bold 10px "Courier New",monospace;fill:#000;stroke:none}
.arr .p{font-size:8px}
.arr .h{font-size:14px}
"""


def inner(text, x, y, w, h, cls):
    """Re-roots an SVG document as a nested <svg> at (x, y)."""
    body = re.sub(r"^.*?<svg", "<svg", text, flags=re.S)
    body = re.sub(r"<style>.*?</style>", "", body, flags=re.S)
    body = re.sub(r"<svg([^>]*?)>", lambda m: "<svg" + re.sub(
        r'\s(width|height|x|y|class)="[^"]*"', "", m.group(1)) +
        f' class="{cls}" x="{x:g}" y="{y:g}" width="{w:g}" height="{h:g}">', body, count=1)
    return body


def base(port):
    name = re.sub(r"\[.*", "", port)
    return "control" if re.match(r"^[a-z_]+_\d+$", name) else name


def connections(sheets_dir):
    """(source, destination) -> signal names, from the sheets' port bits."""
    out_of = {}
    ports = {}
    for key in BLOCK:
        mod = json.load(open(sheets_dir / f"{key}.json"))["modules"][key]
        ports[key] = mod["ports"]
        for name, p in mod["ports"].items():
            if p["direction"] == "output":
                for b in p["bits"]:
                    out_of[b] = key
    edges = defaultdict(set)
    for key, ps in ports.items():
        for name, p in ps.items():
            if p["direction"] != "input" or base(name) in ("clk", "rst"):
                continue
            srcs = {out_of.get(b) for b in p["bits"]}
            for src in srcs:
                if src is None:
                    pin = PINS.get(base(name))
                    if pin:
                        edges[(pin, key)].add(base(name))
                elif src != key:
                    edges[(src, key)].add(base(name))
    for key, ps in ports.items():
        for name, p in ps.items():
            if p["direction"] == "output" and base(name) in PINS:
                edges[(key, PINS[base(name)])].add(base(name))
    return edges


def overview(edges):
    lines = ['digraph g {', 'rankdir=LR; nodesep=0.35; ranksep=0.9; bgcolor="transparent";',
             'node [shape=box style="rounded,filled" fontname="Helvetica-Bold" fontsize=16 '
             'fontcolor="white" penwidth=0 margin="0.25,0.12"];',
             'edge [fontname="Courier-Bold" fontsize=11 color="#55606a" fontcolor="#33393d" '
             'penwidth=1.6 arrowsize=0.8];']
    for key, (colour, title) in BLOCK.items():
        lines.append(f'"{key}" [label="{title}" fillcolor="{colour}"];')
    for pin in sorted(set(PINS.values())):
        lines.append(f'"{pin}" [label="{pin}" shape=box style="rounded,dashed" '
                     f'fontcolor="#33393d" color="#55606a" penwidth=1.4];')
    for (s, d), names in sorted(edges.items()):
        label = "\\n".join(sorted(names))
        lines.append(f'"{s}" -> "{d}" [label="{label}"];')
    lines.append("}")
    svg = subprocess.run(["dot", "-Tsvg"], input="\n".join(lines), capture_output=True,
                         text=True, check=True).stdout
    w, h = (float(v) for v in re.search(
        r'<svg width="([\d.]+)pt" height="([\d.]+)pt"', svg).groups())
    return svg, w, h


def main(build, out_svg, out_json):
    build = Path(build)
    sheets = {s["key"]: s for s in json.load(open(build / "sheets/sheets.json"))}
    parts = []
    frames = []

    # block diagram across the top
    edges = connections(build / "sheets")
    ov, ow, oh = overview(edges)
    scale = 4.2
    title_h = 360
    x = 0.0
    columns = []
    for col in COLUMNS:
        y = 0.0
        cw = 0.0
        placed = []
        for item in col:
            group = item if isinstance(item, list) else [item]
            gx, gh = 0.0, 0.0
            for key in group:
                text = (build / f"sheets/{key}.svg").read_text()
                w, h = svg_size(text)
                docs = [(text, w, h)]
                if key in ARRAYS:
                    at = (build / f"arrays/{key}.svg").read_text()
                    aw, ah = svg_size(at)
                    docs.append((at, aw, ah))
                fw = sum(d[1] for d in docs) + GAP * (len(docs) - 1) + 80
                fh = max(d[2] for d in docs) + HEAD + 60
                placed.append((key, docs, gx, y, fw, fh))
                gx += fw + GAP
                gh = max(gh, fh)
            y += gh + GAP
            cw = max(cw, gx - GAP)
        columns.append((x, placed))
        x += cw + GAP * 2
    total_w = max(x - GAP * 2, ow * scale)
    top = title_h + oh * scale + GAP * 2
    total_h = top + max(max(p[3] + p[5] for p in placed) for _, placed in columns)

    # title, overview
    parts.append(f'<text x="0" y="120" class="t1">bf_chip, every gate</text>')
    s = sum(v["cells"] for v in sheets.values())
    parts.append(f'<text x="0" y="200" class="t2">XLEN = 16 · {s:,} cells drawn by netlistsvg '
                 f'plus 1,920 memory bits drawn as arrays · wires leaving a frame are labelled '
                 f'with their signal name</text>')
    ov_body = re.sub(r"^.*?<svg", "<svg", ov, flags=re.S)
    ov_body = re.sub(r'<svg width="[\d.]+pt" height="[\d.]+pt"',
                     f'<svg x="0" y="{title_h}" width="{ow*scale:g}" height="{oh*scale:g}"', ov_body, count=1)
    parts.append(ov_body)

    for cx, placed in columns:
        for key, docs, gx, gy, fw, fh in placed:
            colour, title = BLOCK[key]
            fx, fy = cx + gx, top + gy
            frames.append({"key": key, "title": title, "colour": colour,
                           "x": fx, "y": fy, "w": fw, "h": fh})
            parts.append(f'<rect x="{fx:g}" y="{fy:g}" width="{fw:g}" height="{fh:g}" rx="18" '
                         f'fill="#fff" stroke="{colour}" stroke-width="6"/>')
            parts.append(f'<path d="M{fx:g},{fy+18:g} a18,18 0 0 1 18,-18 h{fw-36:g} a18,18 0 0 1 18,18 '
                         f'v{HEAD-50:g} h{-fw:g} z" fill="{colour}"/>')
            sh = sheets[key]
            gates = sum(v for k, v in sh["counts"].items() if k != "$mem_v2")
            sub = f'{gates:,} cells'
            if key in ARRAYS:
                sub += " · RAM block drawn out bit by bit on the right"
            parts.append(f'<text x="{fx+40:g}" y="{fy+78:g}" class="f1">{title}</text>')
            parts.append(f'<text x="{fx+40:g}" y="{fy+110:g}" class="f2">{sub}</text>')
            dx = fx + 40
            for i, (text, w, h) in enumerate(docs):
                parts.append(inner(text, dx, fy + HEAD, w, h, "ns" if i == 0 else "arr"))
                dx += w + GAP

    pad = 160
    style = ("text.t1{font:700 110px Helvetica,Arial,sans-serif;fill:#1e2427}"
             "text.t2{font:400 44px Helvetica,Arial,sans-serif;fill:#5d676c}"
             "text.f1{font:700 46px Helvetica,Arial,sans-serif;fill:#fff}"
             "text.f2{font:400 26px Helvetica,Arial,sans-serif;fill:#fff}" + SCOPED)
    doc = (f'<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" '
           f'xmlns:s="https://github.com/nturley/netlistsvg" '
           f'width="{total_w + 2*pad:g}" height="{total_h + 2*pad:g}" '
           f'viewBox="{-pad} {-pad} {total_w + 2*pad:g} {total_h + 2*pad:g}">'
           f'<style>{style}</style>'
           f'<rect x="{-pad}" y="{-pad}" width="{total_w + 2*pad:g}" height="{total_h + 2*pad:g}" fill="#f5f6f2"/>'
           + "\n".join(parts) + "</svg>")
    Path(out_svg).write_text(doc)
    json.dump({"width": total_w + 2 * pad, "height": total_h + 2 * pad, "pad": pad,
               "frames": frames, "overview": {"y": title_h, "w": ow * scale, "h": oh * scale}},
              open(out_json, "w"), indent=1)
    print("poster", int(total_w + 2 * pad), "x", int(total_h + 2 * pad), len(frames), "frames,",
          len(edges), "connections")


if __name__ == "__main__":
    main(*sys.argv[1:])
