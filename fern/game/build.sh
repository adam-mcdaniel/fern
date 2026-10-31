#!/bin/sh
# Builds a fern program that uses screen.fern (breakout.fern, by default)
# into an executable, with screen.c and SDL2: fern does it all, this just
# says what to link.
#
#   fern/game/build.sh [--debug] [FILE.fern] [OUTPUT]
#   fern/game/build.sh [--debug] all   # every program here (each .fern with a main)
#
# Release (the default; --release says so too) has fern optimize, and the C
# compiler -O3: for a big program it's the quicker to build as well as the
# faster to run (see fern's README), the optimized program being so much
# less C. --debug has fern skip its optimizer (-O2). A program's own C, if
# it has any, it names in `// links: FILE.c` lines (relative to this
# folder).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
mode=--release
if [ "$1" = --release ]; then
    shift
elif [ "$1" = --debug ]; then
    mode=""
    shift
fi
if [ "$1" = all ]; then
    # (four at a time)
    cargo build --release --quiet -p fern --manifest-path "$root/Cargo.toml"
    # (fern is built once, here: building it while another build runs it
    # replaces the file under it, which macOS kills it for)
    grep -l '^fn main()' "$here"/*.fern | FERN_BUILT=1 xargs -n 1 -P 4 "$0" ${mode:---debug}
    exit 0
fi
src=${1:-$here/breakout.fern}
out=${2:-$here/$(basename "$src" .fern)}

[ -n "$FERN_BUILT" ] || cargo build --release --quiet -p fern --manifest-path "$root/Cargo.toml"
# (C of a program's own, if it has any: what its `// links: FILE.c` lines
# name, relative to its folder)
own=$(sed -n 's|^// links: ||p' "$src" | sed "s|^|$(dirname "$src")/|")
# (fern writes the C and runs the C compiler, with screen.c and SDL2 linked in)
"$root/target/release/fern" "$src" $mode -o "$out" -- "$here/screen.c" $own $(pkg-config --cflags --libs sdl2)
