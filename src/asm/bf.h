// Writing C functions that programs for the VM call.
//
// The VM calls a label the program doesn't define as a C function
//
//   void name(int64_t **tape, int64_t **ptr, int64_t *acc)
//
// with the machine's tape (`*tape` is its first cell), pointer (`*ptr` is
// the cell it's at) and accumulator. A function can do what it likes with
// them, but must leave the pointer where it was. `BF_FUNCTION` writes that
// signature, for functions that use the machine directly:
//
//   BF_FUNCTION(putint) { printf("%lld", BF_CELL(0)); }
//   BF_FUNCTION(answer) { BF_ACC = 42; }
//   BF_FUNCTION(dump) { for (int i = 0; i < 16; i++) printf("%llx ", BF_TAPE(i)); }
//
// Programs from the IR (and DOT's `extern def`) call with a convention: the
// arguments in cells next to each other with the pointer at the first, and
// the result left in the accumulator. `BF_EXTERN` writes a function that
// takes that convention, around a plain C function with typed parameters:
//
//   BF_EXTERN(Int, clamp, (Int, x), (Int, low), (Int, high)) {
//       return x < low ? low : x > high ? high : x;
//   }
//   BF_EXTERN(Unit, beep) { putchar('\a'); }
//
// The types say how a cell becomes a C value, and back:
//
//   Int    int64_t, as it is
//   Bool   bool: a cell's 0 is false, anything else true, and back 1 or 0
//   Char   char, the cell's low byte
//   Cells  int64_t *: the cell holds an address (in the C backend, a real
//          one), here a pointer to the cells there
//   Any    int64_t, untouched (an address, say, for passing on)
//   Unit   for a result only: none, which leaves 0
//
// The macros take any number of arguments, so they need C23 or GNU C
// (clang's and gcc's default).
//
// A header can add types by defining `BF_TYPE_T`, `BF_LOAD_T(var, cell)`
// (statements declaring `var`, the C value of `cell`) and
// `BF_RESULT_T(acc, value)` (dot.h adds DOT's strings). At most 9
// parameters, as the IR passes.

#ifndef BF_H
#define BF_H

#include <stdbool.h>
#include <stdint.h>

// --- using the machine directly

#if defined(__GNUC__)
#define BF_UNUSED __attribute__((unused))
#else
#define BF_UNUSED
#endif

#define BF_FUNCTION(name) void name(int64_t **tape BF_UNUSED, int64_t **ptr BF_UNUSED, int64_t *acc BF_UNUSED)

// The cell `i` cells on from the pointer; the accumulator; cell `i` of the
// tape. (Inside a `BF_FUNCTION`.)
#define BF_CELL(i) ((*ptr)[i])
#define BF_ACC (*acc)
#define BF_TAPE(i) ((*tape)[i])

// --- types

#define BF_TYPE_Int int64_t
#define BF_LOAD_Int(var, cell) int64_t var = (cell);
#define BF_RESULT_Int(acc, v) ((acc) = (int64_t)(v))

#define BF_TYPE_Bool bool
#define BF_LOAD_Bool(var, cell) bool var = (cell) != 0;
#define BF_RESULT_Bool(acc, v) ((acc) = (v) ? 1 : 0)

#define BF_TYPE_Char char
#define BF_LOAD_Char(var, cell) char var = (char)(cell);
#define BF_RESULT_Char(acc, v) ((acc) = (int64_t)(unsigned char)(v))

#define BF_TYPE_Cells int64_t *
#define BF_LOAD_Cells(var, cell) int64_t *var = (int64_t *)(intptr_t)(cell);
#define BF_RESULT_Cells(acc, v) ((acc) = (int64_t)(intptr_t)(v))

#define BF_TYPE_Any int64_t
#define BF_LOAD_Any(var, cell) int64_t var = (cell);
#define BF_RESULT_Any(acc, v) ((acc) = (int64_t)(v))

#define BF_TYPE_Unit void
#define BF_RESULT_Unit(acc, call) ((call), (acc) = 0)

// --- the convention

// `BF_EXTERN(ret, name, (type, param)...) { body }` is the C function
// `name` the VM calls, which takes the arguments from their cells, passes
// them to a function `name_body(params)` with `body`, and leaves what that
// gives back in the accumulator.
#define BF_EXTERN(ret, name, ...)                                             \
    static BF_TYPE_##ret name##_body(BF_PARAMS(__VA_ARGS__));                 \
    BF_FUNCTION(name) {                                                       \
        BF_LOADS(__VA_ARGS__)                                                 \
        BF_RESULT_##ret(*acc, name##_body(BF_ARGS(__VA_ARGS__)));             \
    }                                                                         \
    static BF_TYPE_##ret name##_body(BF_PARAMS(__VA_ARGS__))

// The machinery: how many `(type, name)` pairs there are, each one as a
// parameter (`int64_t x`), the statements that take the arguments from
// their cells (into `bf_arg0`, `bf_arg1`, ...), and those as arguments.
#define BF_CAT(a, b) BF_CAT_(a, b)
#define BF_CAT_(a, b) a##b
#define BF_COUNT(...) BF_COUNT_(__VA_OPT__(__VA_ARGS__, ) 9, 8, 7, 6, 5, 4, 3, 2, 1, 0)
#define BF_COUNT_(_1, _2, _3, _4, _5, _6, _7, _8, _9, n, ...) n

#define BF_TYPE_OF(type, name) type
#define BF_PARAM(pair) BF_PARAM_ pair
#define BF_PARAM_(type, name) BF_TYPE_##type name
#define BF_LOAD(i, pair) BF_LOAD_(i, BF_TYPE_OF pair)
#define BF_LOAD_(i, type) BF_LOAD__(type, BF_CAT(bf_arg, i), (*ptr)[i])
#define BF_LOAD__(type, var, cell) BF_LOAD_##type(var, cell)

#define BF_PARAMS(...) BF_CAT(BF_PARAMS_, BF_COUNT(__VA_ARGS__))(__VA_ARGS__)
#define BF_PARAMS_0() void
#define BF_PARAMS_1(a) BF_PARAM(a)
#define BF_PARAMS_2(a, b) BF_PARAM(a), BF_PARAM(b)
#define BF_PARAMS_3(a, b, c) BF_PARAMS_2(a, b), BF_PARAM(c)
#define BF_PARAMS_4(a, b, c, d) BF_PARAMS_3(a, b, c), BF_PARAM(d)
#define BF_PARAMS_5(a, b, c, d, e) BF_PARAMS_4(a, b, c, d), BF_PARAM(e)
#define BF_PARAMS_6(a, b, c, d, e, f) BF_PARAMS_5(a, b, c, d, e), BF_PARAM(f)
#define BF_PARAMS_7(a, b, c, d, e, f, g) BF_PARAMS_6(a, b, c, d, e, f), BF_PARAM(g)
#define BF_PARAMS_8(a, b, c, d, e, f, g, h) BF_PARAMS_7(a, b, c, d, e, f, g), BF_PARAM(h)
#define BF_PARAMS_9(a, b, c, d, e, f, g, h, i) BF_PARAMS_8(a, b, c, d, e, f, g, h), BF_PARAM(i)

#define BF_LOADS(...) BF_CAT(BF_LOADS_, BF_COUNT(__VA_ARGS__))(__VA_ARGS__)
#define BF_LOADS_0()
#define BF_LOADS_1(a) BF_LOAD(0, a)
#define BF_LOADS_2(a, b) BF_LOADS_1(a) BF_LOAD(1, b)
#define BF_LOADS_3(a, b, c) BF_LOADS_2(a, b) BF_LOAD(2, c)
#define BF_LOADS_4(a, b, c, d) BF_LOADS_3(a, b, c) BF_LOAD(3, d)
#define BF_LOADS_5(a, b, c, d, e) BF_LOADS_4(a, b, c, d) BF_LOAD(4, e)
#define BF_LOADS_6(a, b, c, d, e, f) BF_LOADS_5(a, b, c, d, e) BF_LOAD(5, f)
#define BF_LOADS_7(a, b, c, d, e, f, g) BF_LOADS_6(a, b, c, d, e, f) BF_LOAD(6, g)
#define BF_LOADS_8(a, b, c, d, e, f, g, h) BF_LOADS_7(a, b, c, d, e, f, g) BF_LOAD(7, h)
#define BF_LOADS_9(a, b, c, d, e, f, g, h, i) BF_LOADS_8(a, b, c, d, e, f, g, h) BF_LOAD(8, i)

#define BF_ARGS(...) BF_CAT(BF_ARGS_, BF_COUNT(__VA_ARGS__))
#define BF_ARGS_0
#define BF_ARGS_1 bf_arg0
#define BF_ARGS_2 BF_ARGS_1, bf_arg1
#define BF_ARGS_3 BF_ARGS_2, bf_arg2
#define BF_ARGS_4 BF_ARGS_3, bf_arg3
#define BF_ARGS_5 BF_ARGS_4, bf_arg4
#define BF_ARGS_6 BF_ARGS_5, bf_arg5
#define BF_ARGS_7 BF_ARGS_6, bf_arg6
#define BF_ARGS_8 BF_ARGS_7, bf_arg7
#define BF_ARGS_9 BF_ARGS_8, bf_arg8

#endif
