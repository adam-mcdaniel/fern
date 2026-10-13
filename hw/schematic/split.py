#!/usr/bin/env python3
"""Split a flat gate-level Yosys netlist into one schematic sheet per register.

Each sheet holds a register's flip-flops (or a memory block) plus the gates
that compute its next value.  Gates that feed more than one register go on a
shared "decode" sheet.  Signals that cross sheets become ports named after
the net, so sheets can be cross-referenced by name; unnamed nets made by
synthesis are called <driving sheet>_<id>.

usage: split.py gates.json out_dir
writes out_dir/<sheet>.json (one Yosys JSON netlist per sheet) and
out_dir/sheets.json (sheet order, titles and statistics).
"""

import json
import re
import sys
from collections import defaultdict
from pathlib import Path

# Which sheet each register/memory belongs to, by its net or cell name.
SHEETS = [
    ("pc", "Program counter", r"^cpu\.pc$|^imem_addr$"),
    ("a", "Accumulator A", r"^cpu\.a$"),
    ("p", "Tape pointer P", r"^cpu\.p$|^dmem_addr$"),
    ("o", "Operand register O", r"^cpu\.o$|^cpu\.operand$"),
    ("control", "Control FSM", r"^cpu\.state$|^halted$"),
    ("tape", "Tape write port", r"^dmem_we$|^dmem_wdata$"),
    ("pstack", "Pointer stack", r"^cpu\.psp$|pstack|^cpu\.ptop$"),
    ("rstack", "Return stack", r"^cpu\.rsp$|rstack|^cpu\.rtop$"),
    ("uart_rx", "UART receiver", r"^rx\."),
    ("fifo", "RX FIFO", r"rx_fifo\."),
    ("uart_tx", "UART transmitter", r"^tx\.|^uart_tx$"),
]
SHARED = ("decode", "Shared decode")

COMB = {"$_AND_", "$_OR_", "$_XOR_", "$_NOT_", "$_MUX_"}


def sheet_for(name):
    for key, _, pattern in SHEETS:
        if re.search(pattern, name):
            return key
    return None


def main(src, out):
    mod = json.load(open(src))["modules"]
    (top_name, top), = mod.items()
    cells, ports = top["cells"], top["ports"]

    # Best human name for each bit: prefer user-visible nets, then short ones.
    bitname = {}
    for name, net in sorted(top["netnames"].items(),
                            key=lambda kv: (kv[0].startswith("$"), len(kv[0]))):
        for i, b in enumerate(net["bits"]):
            if isinstance(b, int) and b not in bitname:
                bitname[b] = (name, i, len(net["bits"]))

    def outs(cell):
        c = cells[cell]
        return [b for p, d in c["port_directions"].items() if d == "output"
                for b in c["connections"][p] if isinstance(b, int)]

    def ins(cell):
        c = cells[cell]
        return [b for p, d in c["port_directions"].items() if d == "input"
                for b in c["connections"][p] if isinstance(b, int)]

    driver = {}
    for cell in cells:
        for b in outs(cell):
            driver[b] = cell
    readers = defaultdict(set)
    for cell in cells:
        for b in ins(cell):
            readers[b].add(cell)

    # Seed every state element (and output port) with its sheet.
    owner = {}
    sinks = defaultdict(list)       # sheet -> bits whose cones it owns
    for cell, c in cells.items():
        if c["type"] in COMB:
            continue
        key = None
        for b in outs(cell):
            key = key or sheet_for(bitname.get(b, ("",))[0])
        key = key or sheet_for(cell)
        if key is None:
            sys.exit(f"no sheet for {c['type']} {cell}")
        owner[cell] = key
        sinks[key] += ins(cell)
    for pname, p in ports.items():
        if p["direction"] == "output":
            key = sheet_for(pname)
            sinks[key] += [b for b in p["bits"] if isinstance(b, int)]

    # Walk back from each sheet's sinks through combinational gates.
    member = defaultdict(set)
    for key, bits in sinks.items():
        stack = list(bits)
        seen = set()
        while stack:
            b = stack.pop()
            cell = driver.get(b)
            if cell is None or cells[cell]["type"] not in COMB or cell in seen:
                continue
            seen.add(cell)
            member[cell].add(key)
            stack += ins(cell)
    for cell, c in cells.items():
        if c["type"] in COMB:
            keys = member[cell]
            owner[cell] = next(iter(keys)) if len(keys) == 1 else SHARED[0]

    # Build one module per sheet.
    order = [s[:2] for s in SHEETS] + [SHARED]
    port_bits_in = {b for p in ports.values() if p["direction"] == "input"
                    for b in p["bits"] if isinstance(b, int)}
    port_bits_out = {b for p in ports.values() if p["direction"] == "output"
                     for b in p["bits"] if isinstance(b, int)}
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    index = []
    for key, title in order:
        mine = [c for c in cells if owner[c] == key]
        mine_set = set(mine)
        used = {b for c in mine for b in ins(c)}
        made = {b for c in mine for b in outs(c)}
        in_bits = sorted(b for b in used if b not in made)
        out_bits = sorted(b for b in made
                          if b in port_bits_out or readers[b] - mine_set)

        def group(bits, direction):
            groups = defaultdict(list)
            for b in bits:
                name, i, width = bitname.get(b, ("$", 0, 1))
                if name.startswith("$"):
                    # Unnamed signal made by synthesis: name it after the
                    # sheet that drives it, so readers know where to look.
                    src = owner.get(driver.get(b), "in")
                    name, i, width = f"{src}_{b}", 0, 1
                groups[name].append((i, b, width))
            result = {}
            for name, members in sorted(groups.items()):
                members.sort()
                label = re.sub(r"^cpu\.", "", name).replace(".", "_")
                if members[0][2] > 1 and len(members) < members[0][2]:
                    idx = [str(i) for i, _, _ in members]
                    label += f"[{','.join(idx)}]" if len(idx) <= 4 else f"[{idx[0]}..{idx[-1]}]"
                elif members[0][2] > 1:
                    label += f"[{members[0][2]-1}:0]"
                result[label] = {"direction": direction,
                                 "bits": [b for _, b, _ in members]}
            return result

        sheet_ports = group(in_bits, "input")
        sheet_ports.update(group(out_bits, "output"))
        module = {"ports": sheet_ports,
                  "cells": {c: cells[c] for c in mine},
                  "netnames": {}}
        json.dump({"modules": {key: module}}, open(out / f"{key}.json", "w"))
        counts = defaultdict(int)
        for c in mine:
            counts[cells[c]["type"]] += 1
        index.append({"key": key, "title": title, "cells": len(mine),
                      "counts": dict(counts),
                      "inputs": len(in_bits), "outputs": len(out_bits)})
        print(f"{key:9} {len(mine):5} cells  {len(in_bits):4} in  {len(out_bits):4} out  {dict(counts)}")
    json.dump(index, open(out / "sheets.json", "w"), indent=1)


if __name__ == "__main__":
    main(*sys.argv[1:])
