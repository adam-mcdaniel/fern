#!/usr/bin/env python3
"""Composites the layer masks from render.py into one die poster.

usage: poster.py <images dir> <ppum>
reads  <dir>/cells.json and <dir>/masks/mask_*.png (rendered at <ppum>)
writes <dir>/poster.png and <dir>/poster_labels.json

Transistors (diffusion and polysilicon) are tinted with the colour of the
block their standard cell belongs to, so functional regions read at any
zoom; the metal layers are drawn over them as translucent neutral lines.
"""

import json
import sys
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw

from cellmap_render import BLOCKS, CLOCK, FILL, classify

Image.MAX_IMAGE_PIXELS = None

NEUTRAL = {FILL[0]: "#3b4549", CLOCK[0]: "#b9c2c6"}
BG = (0.035, 0.047, 0.055)

# (mask, colour or None for the block colour, opacity, mix toward white)
LAYERS = [
    ("nwell", None, 0.30, -0.6),
    ("diff", None, 0.85, -0.15),
    ("poly", None, 0.92, 0.55),
    ("contact", (1, 1, 1), 0.45, 0),
    ("li1", (0.86, 0.84, 1.0), 0.14, 0),
    ("met1", (0.62, 0.78, 1.0), 0.36, 0),
    ("via", (1, 1, 1), 0.35, 0),
    ("met2", (1.0, 0.84, 0.58), 0.50, 0),
    ("met3", (0.58, 1.0, 0.88), 0.55, 0),
    ("met4", (0.96, 0.96, 0.96), 0.24, 0),
    ("met5", (1.0, 1.0, 1.0), 0.15, 0),
]


def hex_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def main(d, ppum):
    d = Path(d)
    ppum = float(ppum)
    data = json.load(open(d / "cells.json"))
    x0, y0, x1, y1 = data["die"]
    cells = data["cells"]
    owner, _ = classify(cells)
    W, H = Image.open(d / "masks/mask_poly.png").size

    colours = {k: c for k, _, c, _ in BLOCKS} | NEUTRAL
    # Block colour of every pixel covered by a cell (zero elsewhere).
    blockimg = Image.new("RGB", (W, H), (0, 0, 0))
    draw = ImageDraw.Draw(blockimg)
    order = sorted(range(len(cells)), key=lambda i: owner[i] != FILL[0])
    for i in order:
        x, y, w, h = cells[i][:4]
        X0 = (x - x0) * ppum
        Y0 = (y1 - (y + h)) * ppum
        draw.rectangle([X0, Y0, X0 + w * ppum - 1, Y0 + h * ppum - 1],
                       fill=hex_rgb(colours[owner[i]]))

    masks = {name: np.asarray(Image.open(d / f"masks/mask_{name}.png").convert("L"))
             for name, *_ in LAYERS}
    block = np.asarray(blockimg)
    out = np.empty((H, W, 3), np.uint8)
    band = 512
    for r0 in range(0, H, band):
        r1 = min(H, r0 + band)
        b = block[r0:r1].astype(np.float32) / 255
        covered = (b.sum(axis=2, keepdims=True) > 0)
        b = np.where(covered, b, 0.35)
        o = np.empty_like(b)
        o[:] = BG
        # faint tint over each cell's footprint
        o = np.where(covered, o * 0.82 + b * 0.18, o)
        for name, colour, alpha, whiten in LAYERS:
            m = masks[name][r0:r1].astype(np.float32)[..., None] / 255 * alpha
            if colour is None:
                c = b * (1 + whiten) if whiten < 0 else b + (1 - b) * whiten
            else:
                c = np.array(colour, np.float32)
            o = o * (1 - m) + c * m
        out[r0:r1] = np.clip(o * 255 + 0.5, 0, 255).astype(np.uint8)
    Image.fromarray(out).save(d / "poster.png")

    # Label each block at its densest 20 µm neighbourhood.
    bins = 20.0
    labels = []
    for key, label, colour, _ in BLOCKS:
        grid = {}
        for i, c in enumerate(cells):
            if owner[i] != key:
                continue
            cx, cy = c[0] + c[2] / 2, c[1] + c[3] / 2
            k = (int(cx // bins), int(cy // bins))
            grid[k] = grid.get(k, 0) + c[2] * c[3]
        if not grid:
            continue
        # smooth with neighbours so the label lands inside the block's body
        best = max(grid, key=lambda k: sum(grid.get((k[0] + dx, k[1] + dy), 0)
                                           for dx in (-1, 0, 1) for dy in (-1, 0, 1)))
        cx, cy = (best[0] + 0.5) * bins, (best[1] + 0.5) * bins
        labels.append({"key": key, "label": label, "colour": colour,
                       "x": (cx - x0) * ppum, "y": (y1 - cy) * ppum})
    json.dump({"width": W, "height": H, "ppum": ppum, "labels": labels},
              open(d / "poster_labels.json", "w"), indent=1)
    print("poster", W, H, len(labels), "labels")


if __name__ == "__main__":
    main(*sys.argv[1:])
