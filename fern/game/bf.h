// Writing C functions for programs from `bf::ir` to call.
//
// Declare one in the program with `p.external("clamp", 3)`, call it like any
// other function, and write it here:
//
//   #include "bf.h"
//   BF_FUNCTION(clamp) {
//       int64_t x = BF_ARG(0), lo = BF_ARG(1), hi = BF_ARG(2);
//       BF_RETURN(x < lo ? lo : x > hi ? hi : x);
//   }
//
// then compile it with the C that `bf` makes of the program:
//
//   clang -O2 -fwrapv program.c clamp.c
//
// Arguments and results are cells (int64_t). An argument that's an address
// (from `alloc`, `array` or `global`) is a real pointer to cells in C:
// `BF_POINTER(i)[j]` is element `j` of the array passed as argument `i`.
//
// The program runs on a thread of its own (for a stack as big as its
// memory), so a function that has to run on the main thread, as windows and
// their events do on a Mac, says so: `BF_MAIN_THREAD_FUNCTION(name)` in place
// of `BF_FUNCTION(name)`. Each call then waits for the main thread to run it.

#ifndef BF_H
#define BF_H

#include <stdint.h>

#define BF_FUNCTION(name) void name(int64_t **bf_tape, int64_t **bf_ptr, int64_t *bf_acc)
#define BF_ARG(i) ((*bf_ptr)[i])
#define BF_POINTER(i) ((int64_t *)BF_ARG(i))
#define BF_RETURN(value) do { (void)bf_tape; *bf_acc = (int64_t)(value); return; } while (0)

// Runs f(arg) on the main thread, and waits until it has.
void bf_on_main_thread(void (*f)(void *), void *arg);

#define BF_MAIN_THREAD_FUNCTION(name) \
    static void bf_here_##name(int64_t **bf_tape, int64_t **bf_ptr, int64_t *bf_acc); \
    struct bf_call_##name { int64_t **tape, **ptr, *acc; }; \
    static void bf_there_##name(void *p) { struct bf_call_##name *c = p; bf_here_##name(c->tape, c->ptr, c->acc); } \
    BF_FUNCTION(name) { struct bf_call_##name c = {bf_tape, bf_ptr, bf_acc}; bf_on_main_thread(bf_there_##name, &c); } \
    static void bf_here_##name(int64_t **bf_tape, int64_t **bf_ptr, int64_t *bf_acc)

#endif
