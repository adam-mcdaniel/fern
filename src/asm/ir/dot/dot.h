// Working with DOT's values in C functions that DOT programs call, declared
// in DOT with `extern def name(...): T`. The VM calls each the way it calls
// any function the program doesn't define:
//
//   void name(int64_t **tape, int64_t **ptr, int64_t *acc)
//
// with the arguments in cells next to each other and the pointer at the
// first (`dot_arg(ptr, i)`), and takes what it leaves in `*acc` as the
// result. It must leave the pointer where it was. A value is one cell: an
// `Int` is itself, a `Bool` is 1 or 0, `Unit` is 0, and anything else is
// the address of its record.
//
// `DOT_EXTERN` (bf.h's `BF_EXTERN`) writes that function around a plain C
// one, taking the arguments as the DOT declaration's types say:
//
//   // extern def greet(name: String, times: Int): Int
//   DOT_EXTERN(Int, greet, (String, name), (Int, times)) {
//       for (int64_t i = 0; i < times; i++) printf("hello, %s\n", name);
//       return times;
//   }
//
// with bf.h's types (`Int`, `Bool`, `Char`, `Cells`, `Any`, and `Unit` as a
// result) and `String`: a DOT string, as a C string (copied into the
// wrapper's stack frame, ending with 0, so only good during the call).

#ifndef DOT_H
#define DOT_H

#include <stdint.h>
#include <string.h>
#include "bf.h"

#define DOT_EXTERN BF_EXTERN

// The `i`th argument of a call (from 0).
static inline int64_t dot_arg(int64_t **ptr, int i) { return (*ptr)[i]; }

// A string is its length, then a cell for each character.
static inline int64_t dot_length(int64_t s) { return ((int64_t *)(intptr_t)s)[0]; }

static inline int dot_char(int64_t s, int64_t i) { return (int)((int64_t *)(intptr_t)s)[i + 1]; }

// Copies the string `s` into `out`, which has room for `size` bytes, ending
// it with 0 (and cutting it short if need be).
static inline char *dot_to_c(int64_t s, char *out, size_t size) {
    size_t n = (size_t)dot_length(s);
    if (n + 1 > size) n = size - 1;
    for (size_t i = 0; i < n; i++) out[i] = (char)dot_char(s, (int64_t)i);
    out[n] = 0;
    return out;
}

// --- DOT's strings, for `DOT_EXTERN`

#define BF_TYPE_String const char *
#define BF_LOAD_String(var, cell)                                             \
    char var##_text[dot_length(cell) + 1];                                    \
    const char *var = dot_to_c((cell), var##_text, sizeof var##_text);

// Fills a buffer from `std.c` (made by `buffer(capacity)`, and passed as its
// `cells`) with up to `capacity` bytes of `text`, which DOT then reads as a
// string with `contents`. Gives how many bytes it took.
static inline int64_t dot_fill(int64_t cells, int64_t capacity, const char *text, size_t n) {
    int64_t *c = (int64_t *)(intptr_t)cells;
    if ((int64_t)n > capacity) n = (size_t)capacity;
    c[0] = (int64_t)n;
    for (size_t i = 0; i < n; i++) c[i + 1] = (unsigned char)text[i];
    return (int64_t)n;
}

#endif
