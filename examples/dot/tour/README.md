# A tour of DOT

Each program shows one idea from Dependent Object Types, and how the language
in `src/asm/ir/dot` writes it. Modules, signatures, functors and generics
aren't features added on top of DOT: they're objects, record types,
functions and type members. The comments in each file show the DOT behind
the syntax.

| file | what it shows |
|---|---|
| `modules.dot` | modules as objects, sealing with signatures, first-class modules, functors, imports, modules in files (`shapes.dot`), the standard library's map functor |
| `generics.dot` | type parameters as objects with a type member, inferred type arguments, bounds, generic types as refinements, variance, `[A] => ...` |
| `objects.dot` | records and width subtyping, intersections, recursive types, family polymorphism, self types, bounded abstract types |
| `data.dot` | algebraic data types as folds (Church encodings), an expression evaluator |
| `state.dot` | `var`, `while`, closures sharing state, var fields, and why types can't depend on them |
| `ffi.dot` | `extern def`: calling functions outside the program the way the VM does, as `void name(int64_t **tape, int64_t **ptr, int64_t *acc)` in C (`ffi.c`), or in Rust in the interpreter (`examples/dot_ffi.rs`) |
| `../ffi/io.dot` | `extern def`: file I/O in C (`io.c`), linked into a native build |

Run one with

```sh
cargo run --example dot -- examples/dot/tour/generics.dot --run
echo 1 | cargo run --example dot -- examples/dot/tour/modules.dot --run
cargo run --example dot_ffi
```

`--check` prints a program's type instead, `--ir` the optimized IR, and with
neither, the program for the VM. Programs that call C are built natively,
through LLVM or (`--via-c`) as the VM program through the C backend:

```sh
cargo run --example dot -- examples/dot/ffi/io.dot --build io examples/dot/ffi/io.c
./io
```

An external function gets its arguments in the cells from the pointer on
and leaves its result in `*acc`; it has to leave the pointer where it was.
`dot.h`'s `DOT_EXTERN` writes that for you around a plain C function:

```c
// extern def clamp(x: Int, low: Int, high: Int): Int
DOT_EXTERN(Int, clamp, (Int, x), (Int, low), (Int, high)) {
    return x < low ? low : x > high ? high : x;
}
```

(`String` parameters arrive as C strings; `bf.h`'s `BF_FUNCTION(name)` is
for functions that work on the tape, pointer and accumulator themselves.)

The standard library (`src/asm/ir/dot/std/`) is written the same way: `option`,
`list`, `ref`, `array` (on raw cells, from the compiler's `builtin def`s),
`map` (a functor over an ordering) and `text`.
