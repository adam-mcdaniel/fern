# KLayout batch script: renders the bf_chip GDS as PNGs.
#   klayout -b -r render.py -rd gds=<file.gds> -rd out=<dir>
# Writes die.png (whole die, routing layers) plus close-ups of the standard
# cells (cells.png) and of the transistor layers in one cell row
# (transistors.png).  With -rd full=<pixels per micron> it instead writes
# full.png: the whole die, transistor layers only, at that resolution, and
# with -rd masks=<pixels per micron> one white-on-black mask_<layer>.png per
# layer group for compositing (see poster.py).

import os
import pya

gds = globals()["gds"]
out = globals()["out"]

# SkyWater 130nm GDS layers, bottom to top.
LAYERS = {
    "nwell": (64, 20), "diff": (65, 20), "tap": (65, 44), "poly": (66, 20),
    "licon": (66, 44), "li1": (67, 20), "mcon": (67, 44),
    "met1": (68, 20), "via": (68, 44), "met2": (69, 20), "via2": (69, 44),
    "met3": (70, 20), "via3": (70, 44), "met4": (71, 20), "via4": (71, 44),
    "met5": (72, 20), "boundary": (235, 4),
}

# (layer, colour, dither pattern) -- pattern 0 is solid, others are stipples
# so lower layers stay visible through upper ones.
DIE = [
    ("li1", 0x7b5ea7, 5), ("met1", 0x3b7dd8, 5), ("met2", 0xd8a03b, 5),
    ("met3", 0x3bbfa0, 9), ("met4", 0xc9504a, 9), ("met5", 0xdcdcdc, 13),
    ("boundary", 0x9aa4a8, 1),
]
CELLS = [
    ("nwell", 0x2b4a2b, 0), ("diff", 0x4caf50, 0), ("tap", 0x2e7d32, 0),
    ("poly", 0xe0453a, 0), ("licon", 0xf2f2f2, 0), ("li1", 0x9b7fd1, 5),
    ("mcon", 0xffffff, 0), ("met1", 0x3b7dd8, 9), ("via", 0xffffff, 0),
    ("met2", 0xd8a03b, 9),
]
DEVICES = [
    ("nwell", 0x2b4a2b, 0), ("diff", 0x4caf50, 0), ("tap", 0x2e7d32, 0),
    ("poly", 0xe0453a, 0), ("licon", 0xf2f2f2, 0), ("li1", 0x9b7fd1, 9),
    ("mcon", 0xffffff, 0),
]


def render(view, layers, box, path, width, height):
    view.clear_layers()
    for name, colour, pattern in layers:
        layer, datatype = LAYERS[name]
        lp = pya.LayerPropertiesNode()
        lp.source = f"{layer}/{datatype}@1"
        lp.fill_color = colour
        lp.frame_color = colour
        lp.dither_pattern = pattern
        lp.width = 1
        lp.name = name
        view.insert_layer(view.end_layers(), lp)
    view.save_image_with_options(path, width, height, 0, 2, 0, box, False)


view = pya.LayoutView()
view.load_layout(gds, True)
view.max_hier()
view.set_config("background-color", "#101417")
view.set_config("grid-visible", "false")
view.set_config("text-visible", "false")

layout = view.cellview(0).layout()
top = layout.top_cell()
bbox = top.dbbox()
print("die", bbox.width(), bbox.height())

os.makedirs(out, exist_ok=True)
if "masks" in globals():
    # One white-on-black image per layer group, for compositing elsewhere.
    ppum = float(globals()["masks"])
    view.set_config("background-color", "#000000")
    groups = {"nwell": ["nwell"], "diff": ["diff", "tap"], "poly": ["poly"],
              "contact": ["licon", "mcon"], "li1": ["li1"], "met1": ["met1"],
              "met2": ["met2"], "met3": ["met3"], "met4": ["met4"],
              "met5": ["met5"], "via": ["via", "via2", "via3", "via4"]}
    for name, layers in groups.items():
        render(view, [(l, 0xffffff, 0) for l in layers], bbox,
               os.path.join(out, f"mask_{name}.png"),
               int(bbox.width() * ppum), int(bbox.height() * ppum))
        print("mask", name)
    raise SystemExit(0)
if "full" in globals():
    ppum = float(globals()["full"])
    view.set_config("background-color", "#0b0e10")
    render(view, DEVICES, bbox, os.path.join(out, "full.png"),
           int(bbox.width() * ppum), int(bbox.height() * ppum))
    raise SystemExit(0)
render(view, DIE, bbox, os.path.join(out, "die.png"), 3000, 3000)

# Close-ups near the centre of the die.
cx, cy = bbox.center().x, bbox.center().y
render(view, CELLS, pya.DBox(cx - 20, cy - 20, cx + 20, cy + 20),
       os.path.join(out, "cells.png"), 2000, 2000)
render(view, DEVICES, pya.DBox(cx - 6, cy - 3, cx + 6, cy + 3),
       os.path.join(out, "transistors.png"), 2400, 1200)
