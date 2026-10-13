#!/bin/sh
# Usage: hw/gen.sh
# Regenerates the hardware tests that are built with src/asm (and its IR):
# each program in examples/ is saved as hw/tests/<name>.bf, and each DOT
# program in examples/dot/ as hw/tests/dot_<name>.bf, with its input if it
# has one. arith's output depends on the cell width, so its expected output
# for each width comes from the interpreter.
set -e
here=$(cd "$(dirname "$0")" && pwd)
run="cargo run --quiet --manifest-path $here/../Cargo.toml --example"
for name in fib primes strings arith ir_demo; do
    $run "$name" > "$here/tests/$name.bf"
done
for name in hello lists strings trees; do
    $run dot -- "$here/../examples/dot/$name.dot" > "$here/tests/dot_$name.bf"
    if [ -f "$here/../examples/dot/$name.in" ]; then
        cp "$here/../examples/dot/$name.in" "$here/tests/dot_$name.in"
    fi
done
for xlen in 16 32 64; do
    $run arith -- --out "$xlen" > "$here/tests/arith.$xlen.out"
done
