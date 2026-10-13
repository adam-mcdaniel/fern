#!/bin/bash
# Usage: [XLEN=16] hw/test.sh [test.bf ...]
# Runs each program on the simulated CPU and on the C backend and compares
# their output byte for byte.  A test's stdin is <name>.in when present.
# The C backend always uses 64-bit cells; a test whose output depends on the
# width instead compares against <name>.<xlen>.out.
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cargo build --quiet --manifest-path "$here/../Cargo.toml" || exit 1
bfc="$here/../target/debug/bf"

[ $# -eq 0 ] && set -- "$here"/tests/*.bf
fail=0
for prog in "$@"; do
    name=$(basename "$prog" .bf)
    input="${prog%.bf}.in"
    [ -f "$input" ] || input=/dev/null

    expected="${prog%.bf}.${XLEN:-64}.out"
    if [ -f "$expected" ]; then
        cp "$expected" "$tmp/c.out"
    elif ls "${prog%.bf}".*.out > /dev/null 2>&1; then
        echo "SKIP $name (no expected output for ${XLEN:-64}-bit)"
        continue
    else
        "$bfc" "$prog" > "$tmp/p.c" && cc -w -o "$tmp/p" "$tmp/p.c" || { echo "FAIL $name (C build)"; fail=1; continue; }
        "$tmp/p" < "$input" > "$tmp/c.out"
    fi
    if [ "$input" = /dev/null ]; then
        "$here/sim.sh" "$prog" > "$tmp/hw.out"
    else
        "$here/sim.sh" "$prog" "$input" > "$tmp/hw.out"
    fi

    if cmp -s "$tmp/c.out" "$tmp/hw.out"; then
        echo "PASS $name (${XLEN:-64}-bit)"
    else
        echo "FAIL $name (${XLEN:-64}-bit)"
        diff <(od -c "$tmp/c.out") <(od -c "$tmp/hw.out") | head -10
        fail=1
    fi
done
exit $fail
