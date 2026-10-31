// What THE AMAZING STELLA needs from C beyond screen.c: whether a key is
// held, by SDL's scancode (the one button is Space, Enter, or Z held
// down, as well as the mouse), and a clock in microseconds for timing
// frames in the test harnesses.
//
// Written with bf.h, like screen.c: each argument and result is a cell.

#define SDL_MAIN_HANDLED
#include <SDL.h>
#include <time.h>
#include "bf.h"

// scan_down(code): whether the key with this SDL scancode is held
BF_FUNCTION(scan_down) {
    int64_t code = BF_ARG(0);
    int n = 0;
    const Uint8 *keys = SDL_GetKeyboardState(&n);
    BF_RETURN(keys && code >= 0 && code < n && keys[code]);
}

// clock_us(): microseconds on a steady clock, for measuring
BF_FUNCTION(clock_us) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    BF_RETURN((int64_t)t.tv_sec * 1000000 + t.tv_nsec / 1000);
}
