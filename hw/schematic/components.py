#!/usr/bin/env python3
"""One standalone gate diagram per block, framed like the whole-CPU poster.

usage: components.py build_dir out_dir
reads  build_dir/sheets/*.svg, build_dir/arrays/*.svg
writes out_dir/NN-name.svg (and .png / .pdf if rsvg-convert is installed)
"""

import re
import shutil
import subprocess
import sys
from pathlib import Path

from poster import ARRAYS, BLOCK, SCOPED, inner, svg_size

ORDER = ["decode", "control", "o", "pc", "a", "p", "tape",
         "pstack", "rstack", "uart_rx", "fifo", "uart_tx"]
GAP, HEAD, PAD = 220, 170, 60
PNG_SCALE = 2


def frame(key, build):
    colour, title = BLOCK[key]
    text = (build / f"sheets/{key}.svg").read_text()
    docs = [(text, *svg_size(text), "ns")]
    if key in ARRAYS:
        at = (build / f"arrays/{key}.svg").read_text()
        docs.append((at, *svg_size(at), "arr"))
    fw = sum(d[1] for d in docs) + GAP * (len(docs) - 1) + 80
    fh = max(d[2] for d in docs) + HEAD + 60
    W, H = fw + 2 * PAD, fh + 2 * PAD
    sub = "logic gates and D flip-flops"
    if key in ARRAYS:
        sub += " · the RAM block on the left is drawn out bit by bit on the right"
    parts = [
        f'<rect x="0" y="0" width="{W:g}" height="{H:g}" fill="#f5f6f2"/>',
        f'<rect x="{PAD}" y="{PAD}" width="{fw:g}" height="{fh:g}" rx="18" fill="#fff" stroke="{colour}" stroke-width="6"/>',
        f'<path d="M{PAD},{PAD + 18} a18,18 0 0 1 18,-18 h{fw - 36:g} a18,18 0 0 1 18,18 v{HEAD - 50} h{-fw:g} z" fill="{colour}"/>',
        f'<text x="{PAD + 40}" y="{PAD + 78}" class="f1">{title}</text>',
        f'<text x="{PAD + 40}" y="{PAD + 110}" class="f2">bf_chip, XLEN = 16 · {sub}</text>',
    ]
    dx = PAD + 40
    for text, w, h, cls in docs:
        parts.append(inner(text, dx, PAD + HEAD, w, h, cls))
        dx += w + GAP
    style = ("text.f1{font:700 46px Helvetica,Arial,sans-serif;fill:#fff}"
             "text.f2{font:400 26px Helvetica,Arial,sans-serif;fill:#fff}" + SCOPED)
    return (f'<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" '
            f'xmlns:s="https://github.com/nturley/netlistsvg" width="{W:g}" height="{H:g}" '
            f'viewBox="0 0 {W:g} {H:g}"><style>{style}</style>' + "\n".join(parts) + "</svg>")


def main(build, out):
    build, out = Path(build), Path(out)
    out.mkdir(parents=True, exist_ok=True)
    rsvg = shutil.which("rsvg-convert")
    for n, key in enumerate(ORDER, 1):
        slug = re.sub(r"[^a-z0-9]+", "-", BLOCK[key][1].lower()).strip("-")
        base = out / f"{n:02d}-{slug}"
        base.with_suffix(".svg").write_text(frame(key, build))
        if rsvg:
            subprocess.run([rsvg, "-z", str(PNG_SCALE), str(base.with_suffix(".svg")),
                            "-o", str(base.with_suffix(".png"))], check=True)
            subprocess.run([rsvg, "-f", "pdf", "-z", "0.5", str(base.with_suffix(".svg")),
                            "-o", str(base.with_suffix(".pdf"))], check=True)
        print(base.name)


if __name__ == "__main__":
    main(*sys.argv[1:])
