// The external functions ffi.dot calls. `DOT_EXTERN` writes each as the
// VM calls it (`void name(int64_t **tape, int64_t **ptr, int64_t *acc)`),
// taking the arguments from their cells as the declaration's types say, and
// leaving the result in the accumulator.

#include "dot.h"

// extern def popcount(n: Int): Int
DOT_EXTERN(Int, popcount, (Int, n)) {
    return __builtin_popcountll((uint64_t)n);
}

// extern def checksum(s: String): Int
DOT_EXTERN(Int, checksum, (String, s)) {
    int64_t sum = 0;
    for (const char *c = s; *c; c++) sum += (unsigned char)*c;
    return sum;
}

// extern def clamp(x: Int, low: Int, high: Int): Int
DOT_EXTERN(Int, clamp, (Int, x), (Int, low), (Int, high)) {
    return x < low ? low : x > high ? high : x;
}
