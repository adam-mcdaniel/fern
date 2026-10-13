#!/usr/bin/env python3
"""Gate-level drawings of bf_chip's three memory arrays.

Automatic schematic layout turns a RAM into an unreadable tangle, so these
are drawn the way memory arrays are drawn by hand: one row per word, one
column per bit, every stored bit a D flip-flop with a 2-input multiplexer
that loads it when its word line is high.  A row decoder of AND gates drives
the word lines from the write address; each bit column is read through a
binary tree of 2-input multiplexers steered by the read address.

usage: arrays.py out_dir      writes pstack.svg, rstack.svg, fifo.svg
"""

import sys
from pathlib import Path

ROW = 46          # height of one word row
CELL = 92         # width of mux + flip-flop
LEVEL = 30        # width of one read-tree level
PAD = 14


class Svg:
    def __init__(self):
        self.parts = []

    def line(self, *pts, grey=False):
        d = "M" + " L".join(f"{x:g},{y:g}" for x, y in pts)
        cls = ' class="g"' if grey else ""
        self.parts.append(f'<path{cls} d="{d}"/>')

    def dot(self, x, y):
        self.parts.append(f'<circle class="d" cx="{x:g}" cy="{y:g}" r="2"/>')

    def text(self, x, y, s, anchor="start", cls=""):
        c = f' class="{cls}"' if cls else ""
        self.parts.append(f'<text{c} x="{x:g}" y="{y:g}" text-anchor="{anchor}">{s}</text>')

    def mux(self, x, y):
        """2-input mux at (x, y) top-left, 20 x 36.  Pins: in0 (x, y+9),
        in1 (x, y+27), sel (x+10, y+33), out (x+20, y+18)."""
        self.parts.append(f'<path d="M{x},{y} L{x+20},{y+8} L{x+20},{y+28} L{x},{y+36} Z"/>')
        self.text(x + 3, y + 12, "0", cls="p")
        self.text(x + 3, y + 30, "1", cls="p")

    def dff(self, x, y):
        """D flip-flop at (x, y), 30 x 34.  Pins: D (x, y+9), clk (x, y+26),
        Q (x+30, y+9)."""
        self.parts.append(f'<rect x="{x}" y="{y}" width="30" height="34"/>')
        self.parts.append(f'<path d="M{x},{y+21} L{x+6},{y+26} L{x},{y+31}"/>')
        self.text(x + 3, y + 12, "D", cls="p")
        self.text(x + 27, y + 12, "Q", anchor="end", cls="p")

    def and_gate(self, x, y, h):
        """AND gate of height h at (x, y); output at (x+h/2+14, y+h/2)."""
        r = h / 2
        self.parts.append(f'<path d="M{x},{y} H{x+14} A{r},{r} 0 0 1 {x+14},{y+h} H{x} Z"/>')

    def inverter(self, x, y):
        """Downward-pointing inverter at (x, y) top; output at (x, y+16)."""
        self.parts.append(f'<path d="M{x-6},{y} L{x+6},{y} L{x},{y+11} Z"/>')
        self.parts.append(f'<circle cx="{x}" cy="{y+13.5}" r="2.5"/>')

    def render(self, w, h, title):
        style = ("path,rect,circle{fill:none;stroke:#000;stroke-width:1}"
                 ".g{stroke:#9aa3a8}.d{fill:#000;stroke:none}"
                 "text{font:bold 10px 'Courier New',monospace;fill:#000;stroke:none}"
                 ".p{font-size:8px}.h{font-size:14px}")
        body = "\n".join(self.parts)
        return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{w:g}" height="{h:g}" '
                f'viewBox="0 0 {w:g} {h:g}"><title>{title}</title><style>{style}</style>'
                f'<rect x="0" y="0" width="{w:g}" height="{h:g}" fill="#fff" stroke="none"/>'
                f'{body}</svg>')


def array(words, width, abits, wdata, waddr, raddr, we, out, out_reg, title):
    s = Svg()
    levels = abits
    # columns of the address-literal bus: a_i and ~a_i for each write bit
    bus_x0 = PAD + 40
    lit_x = {}
    for i in range(abits):
        lit_x[(i, 1)] = bus_x0 + i * 24
        lit_x[(i, 0)] = bus_x0 + i * 24 + 12
    we_x = bus_x0 + abits * 24 + 6
    dec_x = we_x + 24
    and_h = max(14, (abits + 1) * 4)
    col_x0 = dec_x + and_h / 2 + 14 + 40
    col_w = CELL + levels * LEVEL + 40
    top = 150
    clk_x = col_x0 - 22
    bottom = top + words * ROW

    # header: write address in, complements, write enable, clock
    for i in range(abits):
        x1, x0 = lit_x[(i, 1)], lit_x[(i, 0)]
        s.text(x1, 28 + (i % 2) * 12, f"{waddr}[{i}]", anchor="middle")
        s.line((x1, 44), (x1, bottom))
        s.dot(x1, 70)
        s.line((x1, 70), (x0, 70), (x0, 76))
        s.inverter(x0, 76)
        s.line((x0, 92), (x0, bottom))
    s.text(we_x, 28 + (abits % 2) * 12, we, anchor="middle")
    s.line((we_x, 44), (we_x, bottom))
    s.text(clk_x, 132, "clk", anchor="middle")
    s.line((clk_x, 138), (clk_x, bottom))

    # bit lines (write data) and read-address lines per column
    for b in range(width):
        cx = col_x0 + b * col_w
        bl = cx + 4
        s.text(bl, 28 + (b % 2) * 12, f"{wdata}[{b}]", anchor="middle")
        s.line((bl, 44), (bl, bottom))
        for lv in range(levels):
            rx = cx + CELL + lv * LEVEL + 24
            s.text(rx, 100 + (lv % 2) * 11, f"{raddr}{lv}", anchor="middle", cls="p")
            s.line((rx, 106 + (lv % 2) * 11), (rx, bottom + 6 * ROW // 2), grey=True)

    # rows
    leaf = {}
    for w in range(words):
        y = top + w * ROW
        mid = y + 18
        # decoder AND: inputs are the address literals for w, plus we
        ay = mid - and_h / 2
        s.and_gate(dec_x, ay, and_h)
        for i in range(abits):
            bit = (w >> i) & 1
            px = lit_x[(i, bit)]
            py = ay + 4 + i * 4
            s.dot(px, py)
            s.line((px, py), (dec_x, py))
        py = ay + 4 + abits * 4
        s.dot(we_x, py)
        s.line((we_x, py), (dec_x, py))
        wl_y = y + 40
        s.text(dec_x - 4, y + 2, f"{w}", anchor="end", cls="p")
        ox = dec_x + and_h / 2 + 14
        s.line((ox, mid), (ox + 14, mid), (ox + 14, wl_y), (col_x0 + (width - 1) * col_w + 10, wl_y))
        s.dot(clk_x, y + 34)
        s.line((clk_x, y + 34), (col_x0 + (width - 1) * col_w + 40, y + 34), grey=True)
        for b in range(width):
            cx = col_x0 + b * col_w
            mx, fx = cx + 14, cx + 52
            s.mux(mx, y)
            # in1 from bit line, sel from word line, out to D
            s.dot(cx + 4, y + 27)
            s.line((cx + 4, y + 27), (mx, y + 27))
            s.dot(mx + 10, wl_y)
            s.line((mx + 10, wl_y), (mx + 10, y + 33))
            s.line((mx + 20, y + 18), (fx - 6, y + 18), (fx - 6, y + 9), (fx, y + 9))
            s.dff(fx, y)
            s.dot(fx - 10 + 10, y + 34) if False else None
            s.line((fx, y + 26), (fx - 3, y + 26), (fx - 3, y + 34))
            # Q feeds back to in0 and out to the read tree
            qx = fx + 30
            s.line((qx, y + 9), (qx + 6, y + 9), (qx + 6, y - 3), (mx - 6, y - 3), (mx - 6, y + 9), (mx, y + 9))
            s.dot(qx + 6, y + 9)
            leaf[(w, b)] = (qx + 6, y + 9)

    # read trees: level lv pairs the outputs of level lv-1
    for b in range(width):
        cx = col_x0 + b * col_w
        nodes = [leaf[(w, b)] for w in range(words)]
        for lv in range(levels):
            tx = cx + CELL + lv * LEVEL
            sel_x = tx + 24
            nxt = []
            for k in range(0, len(nodes), 2):
                (x0, y0), (x1, y1) = nodes[k], nodes[k + 1]
                my = (y0 + y1) / 2 - 18
                s.mux(tx, my)
                s.line((x0, y0), (tx - 4, y0), (tx - 4, my + 9), (tx, my + 9))
                s.line((x1, y1), (tx - 8, y1), (tx - 8, my + 27), (tx, my + 27))
                s.line((tx + 10, my + 33), (tx + 10, my + 40), (sel_x, my + 40))
                s.dot(sel_x, my + 40)
                nxt.append((tx + 20, my + 18))
            nodes = nxt
        # root -> output (through a register for the stacks)
        rx, ry = nodes[0]
        oy = bottom + 30
        s.line((rx, ry), (rx + 8, ry), (rx + 8, oy + 9), (rx + 14, oy + 9))
        if out_reg:
            s.dff(rx + 14, oy)
            s.line((rx + 14, oy + 26), (rx + 10, oy + 26), (rx + 10, oy + 40), (clk_x, oy + 40), (clk_x, bottom), grey=True)
            s.line((rx + 44, oy + 9), (rx + 50, oy + 9), (rx + 50, oy + 60))
            s.text(rx + 50, oy + 74, f"{out}[{b}]", anchor="middle")
        else:
            s.line((rx + 14, oy + 9), (rx + 14, oy + 60))
            s.text(rx + 14, oy + 74, f"{out}[{b}]", anchor="middle")

    total_w = col_x0 + width * col_w + PAD
    total_h = bottom + 130
    s.text(PAD, total_h - 16, title, cls="h")
    return s.render(total_w, total_h, title)


def main(out):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "pstack.svg").write_text(array(
        64, 16, 6, "p", "psp", "rd", "push", "ptop", True,
        "pointer stack: 64 words x 16 bits; write at psp on *, read address rd = psp-1, read into ptop"))
    (out / "rstack.svg").write_text(array(
        64, 12, 6, "pc_next", "rsp", "rd", "push", "rtop", True,
        "return stack: 64 words x 12 bits; write at rsp on !, read address rd = rsp-1, read into rtop"))
    (out / "fifo.svg").write_text(array(
        16, 8, 4, "rx_byte", "wr", "rd", "rx_valid", "in_data", False,
        "RX FIFO: 16 words x 8 bits; write at wr when a byte arrives, read address rd"))


if __name__ == "__main__":
    main(*sys.argv[1:])
