#!/bin/sh
# Usage: hw/asic/render.sh [run-tag]        (default: final)
# Renders a finished LibreLane run to images in runs/<tag>/images:
#   die.png, cells.png, transistors.png  layer renders (KLayout)
#   cellmap.png, cellmap.json            cells coloured by block, with areas
set -e
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
run="runs/${1:-final}"
image=${LIBRELANE_IMAGE:-ghcr.io/librelane/librelane:3.0.14}
gds=$(ls "$run"/final/gds/*.gds)
odb=$(ls "$run"/final/odb/*.odb)
mkdir -p "$run/images"

docker run --rm -v "$here":/work -w /work "$image" sh -c "
    klayout -b -r render.py -rd gds=$gds -rd out=$run/images &&
    openroad -exit -no_splash -python cellmap.py $odb $run/images/cells.json"
python3 cellmap_render.py "$run/images/cells.json" "$run/images/cellmap.png" "$run/images/cellmap.json"
