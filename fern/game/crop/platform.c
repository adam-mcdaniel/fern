// What BUMPER CROP needs from C beyond screen.c: every key on the keyboard
// by SDL's scancode (pinball's flippers are the two shift keys, which
// screen.c doesn't tell apart), a clock in microseconds for timing frames,
// and the controller's rumble.
//
// Written with bf.h, like screen.c: each argument and result is a cell.

#define SDL_MAIN_HANDLED
#include <SDL.h>
#include <time.h>
#include "bf.h"

// scan_down(code): whether the key with this SDL scancode is held (the
// keyboard's state is what screen_show last read)
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

// rumble(low, high, ms): shakes the first game controller, if there is
// one: its low and high motors from 0 to 65535, for ms milliseconds (on
// the main thread, where SDL wants its devices opened)
BF_MAIN_THREAD_FUNCTION(rumble) {
    static SDL_GameController *pad;
    if (!pad || !SDL_GameControllerGetAttached(pad)) {
        pad = NULL;
        for (int i = 0; i < SDL_NumJoysticks(); i++) {
            if (SDL_IsGameController(i)) { pad = SDL_GameControllerOpen(i); break; }
        }
    }
    if (pad) SDL_GameControllerRumble(pad, (Uint16)BF_ARG(0), (Uint16)BF_ARG(1), (Uint32)BF_ARG(2));
    BF_RETURN(0);
}
