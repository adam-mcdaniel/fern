# OpenROAD Python script: dumps every placed instance as
# [x, y, w, h, master, [output nets], [input nets]] in microns.
#   openroad -python cellmap.py <design.odb> <out.json>
import json
import sys

import odb

db = odb.dbDatabase.create()
odb.read_db(db, sys.argv[1])
block = db.getChip().getBlock()
dbu = block.getDbUnitsPerMicron()
die = block.getDieArea()
cells = []
for inst in block.getInsts():
    bb = inst.getBBox()
    outs = [it.getNet().getName() for it in inst.getITerms()
            if it.isOutputSignal() and it.getNet()]
    ins = [it.getNet().getName() for it in inst.getITerms()
           if it.isInputSignal() and it.getNet()]
    cells.append([bb.xMin() / dbu, bb.yMin() / dbu,
                  (bb.xMax() - bb.xMin()) / dbu, (bb.yMax() - bb.yMin()) / dbu,
                  inst.getMaster().getName(), outs, ins])
json.dump({"die": [die.xMin() / dbu, die.yMin() / dbu, die.xMax() / dbu, die.yMax() / dbu],
           "cells": cells}, open(sys.argv[2], "w"))
print(len(cells), "instances")
