// A window for fern programs: the C behind `screen.fern`'s `extern fn`s,
// written with `bf.h` and SDL2.
//
// A fern value is one cell (an int64_t). An `Int` or `Bool` is itself; an
// `Array<Int>` or a `String` is a pointer to a block: its length, then an
// element (or a character) a cell.
//
// The framebuffer is an `Array<Int>` of width * height cells, a row at a
// time from the top left, each 0xRRGGBB. `screen_show` copies it to the
// window, waits for the next frame (60 a second), and reads the keyboard
// and the mouse, which the other functions then report.

#define SDL_MAIN_HANDLED
#include <SDL.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <spawn.h>
#include <sys/wait.h>
#include <math.h>

extern char **environ;
#include "bf.h"

static SDL_Window *window;
static SDL_Renderer *renderer;
static SDL_Texture *texture;
static uint32_t *rgb;
static int width, height;
// The frames' pace: 60 a second, by a schedule on the high-resolution
// clock: each frame due a 60th of a second after the last was due (not
// after it happened to end), so they stay even whatever the display's
// rate (vsync alone, on a 120 Hz display, gives frames of one refresh and
// three by turns). Measured: 0 to 4 frames in 300 more than 2 ms off.
static uint64_t ticks_per_second, frame_due;

// the sound: a beep (a square wave while it's on), and a synthesizer (see
// sound_play)
static SDL_AudioDeviceID audio;
static volatile int beeping;

// the game controller, if one's plugged in, and its buttons that went down
// since the last frame
static SDL_GameController *pad;
static uint8_t pad_pressed_now[SDL_CONTROLLER_BUTTON_MAX];

// the command line (see save_args)
static int arg_count;
static char **arg_values;

// what's held down now, and what went down since the last frame
static uint8_t pressed[SDL_NUM_SCANCODES];
static int mouse_x_now, mouse_y_now, mouse_held, mouse_clicks, right_clicks;

// fern's key numbers (see screen.fern) as SDL's
static SDL_Scancode scancode(int64_t key) {
    if (key >= 'a' && key <= 'z') return SDL_SCANCODE_A + (key - 'a');
    if (key >= '1' && key <= '9') return SDL_SCANCODE_1 + (key - '1');
    switch (key) {
        case '0': return SDL_SCANCODE_0;
        case ' ': return SDL_SCANCODE_SPACE;
        case 13: return SDL_SCANCODE_RETURN;
        case 27: return SDL_SCANCODE_ESCAPE;
        case 1: return SDL_SCANCODE_LEFT;
        case 2: return SDL_SCANCODE_RIGHT;
        case 3: return SDL_SCANCODE_UP;
        case 4: return SDL_SCANCODE_DOWN;
        case 5: return SDL_SCANCODE_LSHIFT;
        case 6: return SDL_SCANCODE_TAB;
        case 7: return SDL_SCANCODE_F11;
        case 8: return SDL_SCANCODE_BACKSPACE;
        default: return SDL_SCANCODE_UNKNOWN;
    }
}

// ---- the synthesizer
//
// Voices, each a note: a waveform at a pitch (sliding, exponentially, to
// another), shaped by an envelope (rising over its attack, then dying away
// over the rest of its length), through a low-pass filter (whose cutoff can
// slide too, the same way, for a sweep), panned, and
// sent some to a reverb. A note can start at a time to come, on the sound's
// own clock (sound_clock), to the sample: music is notes scheduled a little
// ahead. Each is on a bus, music or effects, with a volume of its own.

#define RATE 44100
#define VOICES 64
#define PLUCK_MAX 2048

enum { SINE, TRIANGLE, SQUARE, SAW, NOISE, PLUCK, PAD, PULSE };

typedef struct {
    int on, wave, bus;
    int64_t start, length, attack;        // in samples, start on the clock
    double phase, phase2, freq, slide;    // slide: freq's factor each sample
    double vol, left, right, send;
    double low, k;                        // the filter's state and coefficient
    double cut, cut_slide;                // its cutoff (hertz), and its factor each sample
    int sweep;                            // whether the cutoff slides
    uint32_t noise;
    float pluck[PLUCK_MAX];               // Karplus-Strong's delay line
    int pluck_n, pluck_i;
} Voice;

static Voice voices[VOICES];
static int64_t clock_now;                 // samples played
static double bus_volume[2] = {1, 1};

// the reverb: four combs in parallel, then two all-passes (Schroeder's), a
// little different on the left from the right
static const int comb_len[2][4] = {{1557, 1617, 1491, 1422}, {1580, 1640, 1514, 1445}};
static const int pass_len[2][2] = {{225, 556}, {248, 579}};
static float comb_buf[2][4][1700], pass_buf[2][2][600];
static int comb_i[2][4], pass_i[2][2];
static float comb_low[2][4];

static float reverb(int side, float in) {
    float out = 0;
    for (int c = 0; c < 4; c++) {
        float *b = comb_buf[side][c];
        int *i = &comb_i[side][c];
        float y = b[*i];
        comb_low[side][c] = y * 0.6f + comb_low[side][c] * 0.4f;   // (damping)
        b[*i] = in + comb_low[side][c] * 0.84f;
        if (++*i >= comb_len[side][c]) *i = 0;
        out += y;
    }
    for (int a = 0; a < 2; a++) {
        float *b = pass_buf[side][a];
        int *i = &pass_i[side][a];
        float y = b[*i];
        b[*i] = out + y * 0.5f;
        out = y - out * 0.5f;
        if (++*i >= pass_len[side][a]) *i = 0;
    }
    return out;
}

static double voice_sample(Voice *v) {
    double t = v->phase, s;
    switch (v->wave) {
        case SINE: s = sin(2 * M_PI * t); break;
        case TRIANGLE: s = 4 * fabs(t - 0.5) - 1; break;
        case SQUARE: s = t < 0.5 ? 0.6 : -0.6; break;
        case PULSE: s = t < 0.2 ? 0.6 : -0.6; break;
        case SAW: s = 2 * t - 1; break;
        case PAD: s = (2 * t - 1) * 0.5 + (2 * v->phase2 - 1) * 0.5; break;
        case NOISE:
            v->noise ^= v->noise << 13; v->noise ^= v->noise >> 17; v->noise ^= v->noise << 5;
            s = (v->noise & 0xffff) / 32768.0 - 1;
            break;
        case PLUCK: {
            // the string: a delay line a period long, averaged as it goes round
            int j = (v->pluck_i + 1) % v->pluck_n;
            s = v->pluck[v->pluck_i];
            v->pluck[v->pluck_i] = (float)((s + v->pluck[j]) * 0.4985);
            v->pluck_i = j;
            break;
        }
        default: s = 0;
    }
    v->phase += v->freq / RATE;
    if (v->phase >= 1) v->phase -= floor(v->phase);
    v->phase2 += v->freq * 1.0068 / RATE;
    if (v->phase2 >= 1) v->phase2 -= floor(v->phase2);
    v->freq *= v->slide;
    return s;
}

static void mix(void *unused, Uint8 *out, int bytes) {
    static unsigned beep_phase;
    float *samples = (float *)out;
    int frames = bytes / (int)sizeof(float) / 2;
    for (int f = 0; f < frames; f++, clock_now++) {
        double l = 0, r = 0, wet = 0;
        for (int i = 0; i < VOICES; i++) {
            Voice *v = &voices[i];
            if (!v->on || clock_now < v->start) continue;
            int64_t age = clock_now - v->start;
            if (age >= v->length) { v->on = 0; continue; }
            double env;
            if (age < v->attack) env = (double)age / v->attack;
            else {
                double rest = 1 - (double)(age - v->attack) / (v->length - v->attack);
                env = v->wave == PAD ? rest : rest * rest;
            }
            double s = voice_sample(v);
            if (v->sweep) {
                v->cut *= v->cut_slide;
                v->k = 1 - exp(-2 * M_PI * v->cut / RATE);
            }
            v->low += (s - v->low) * v->k;
            double x = v->low * env * v->vol * bus_volume[v->bus];
            l += x * v->left;
            r += x * v->right;
            wet += x * v->send;
        }
        if (beeping) {
            double b = (beep_phase++ / 50 % 2 ? 0.08 : -0.08);
            l += b;
            r += b;
        }
        l += reverb(0, (float)wet) * 0.28;
        r += reverb(1, (float)wet) * 0.28;
        // (a soft limit, so a crowd of notes saturates instead of clipping)
        samples[2 * f] = (float)tanh(l);
        samples[2 * f + 1] = (float)tanh(r);
    }
}

static void open_audio(void) {
    if (SDL_InitSubSystem(SDL_INIT_AUDIO) != 0) return;
    SDL_AudioSpec want = {0};
    want.freq = RATE;
    want.format = AUDIO_F32SYS;
    want.channels = 2;
    want.samples = 512;
    want.callback = mix;
    audio = SDL_OpenAudioDevice(NULL, 0, &want, NULL, 0);
    if (audio) SDL_PauseAudioDevice(audio, 0);
}

// sound_play(wave, hz16, end_hz16, at, attack, length, volume_pan, cutoff,
// reverb_bus): a note of a waveform (0 sine, 1 triangle, 2 square, 3 saw,
// 4 noise, 5 a plucked string, 6 a pad of two saws a little out of tune, 7
// a narrow pulse), from hz16 to end_hz16 (16ths of a hertz), starting at
// `at` ms on the sound's clock (or now, if that's past), rising over
// `attack` ms and lasting `length` ms in all; volume_pan is volume (0 to
// 255) * 256 + pan + 128 (pan -100 left to 100 right), cutoff the filter's
// (hertz; or, to sweep it, where it starts + where it ends * 65536),
// reverb_bus is reverb (0 to 255) * 2 + bus (0 music, 1 effects).
// (Packed, two to an argument: a C function takes at most nine.) Its voice
// is the free one, or else the one nearest its end.
BF_FUNCTION(sound_play) {
    if (!audio) BF_RETURN(0);
    int wave = (int)BF_ARG(0);
    double freq = BF_ARG(1) / 16.0, end = BF_ARG(2) / 16.0;
    int64_t at = BF_ARG(3), attack = BF_ARG(4), length = BF_ARG(5);
    double vol = (BF_ARG(6) >> 8) / 255.0 * 0.35, pan = ((BF_ARG(6) & 255) - 128) / 100.0;
    double cutoff = (double)(BF_ARG(7) & 0xffff), cut_end = (double)(BF_ARG(7) >> 16);
    double send = (BF_ARG(8) >> 1) / 255.0;
    int bus = (int)(BF_ARG(8) & 1);
    if (freq < 1) freq = 1;
    if (end < 1) end = 1;
    if (length < 1) length = 1;
    if (pan < -1) pan = -1;
    if (pan > 1) pan = 1;
    if (cutoff < 20) cutoff = 20;
    if (cut_end < 20) cut_end = cutoff;
    SDL_LockAudioDevice(audio);
    int64_t start = at * RATE / 1000;
    if (start < clock_now) start = clock_now;
    int best = 0;
    int64_t best_left = INT64_MAX;
    for (int i = 0; i < VOICES; i++) {
        if (!voices[i].on) { best = i; break; }
        int64_t left = voices[i].start + voices[i].length - clock_now;
        if (left < best_left) { best_left = left; best = i; }
    }
    Voice *v = &voices[best];
    v->on = 1;
    v->wave = wave;
    v->bus = bus;
    v->start = start;
    v->length = length * RATE / 1000;
    v->attack = attack * RATE / 1000;
    if (v->attack < 32) v->attack = 32;
    if (v->attack >= v->length) v->attack = v->length - 1;
    v->phase = 0;
    v->phase2 = 0.37;
    v->freq = freq;
    v->slide = pow(end / freq, 1.0 / (double)(v->length > 1 ? v->length : 1));
    v->vol = vol;
    v->left = sqrt((1 - pan) / 2) * 1.414;
    v->right = sqrt((1 + pan) / 2) * 1.414;
    v->send = send;
    v->low = 0;
    v->k = 1 - exp(-2 * M_PI * cutoff / RATE);
    v->cut = cutoff;
    v->cut_slide = pow(cut_end / cutoff, 1.0 / (double)(v->length > 1 ? v->length : 1));
    v->sweep = cut_end != cutoff;
    v->noise = 0x9e3779b9u ^ (uint32_t)(start * 2654435761u);
    if (wave == PLUCK) {
        // (the string starts as noise, a period of it)
        v->pluck_n = (int)(RATE / freq);
        if (v->pluck_n < 2) v->pluck_n = 2;
        if (v->pluck_n > PLUCK_MAX) v->pluck_n = PLUCK_MAX;
        v->pluck_i = 0;
        uint32_t n = v->noise | 1;
        for (int i = 0; i < v->pluck_n; i++) {
            n ^= n << 13; n ^= n >> 17; n ^= n << 5;
            v->pluck[i] = (float)((n & 0xffff) / 32768.0 - 1);
        }
    }
    SDL_UnlockAudioDevice(audio);
    BF_RETURN(best);
}

// sound_clock(): the sound's clock, in ms: how much it has played
BF_FUNCTION(sound_clock) {
    BF_RETURN(clock_now * 1000 / RATE);
}

// sound_volume(music, effects): each bus's volume, 0 to 100
BF_FUNCTION(sound_volume) {
    bus_volume[0] = BF_ARG(0) / 100.0;
    bus_volume[1] = BF_ARG(1) / 100.0;
    BF_RETURN(0);
}

// sound_stop(bus): silences every note on the bus, playing or to come
BF_FUNCTION(sound_stop) {
    if (!audio) BF_RETURN(0);
    SDL_LockAudioDevice(audio);
    for (int i = 0; i < VOICES; i++) if (voices[i].bus == BF_ARG(0)) voices[i].on = 0;
    SDL_UnlockAudioDevice(audio);
    BF_RETURN(0);
}

// screen_open(width, height, scale, title): a window of width x height
// pixels, each scale x scale on the screen
BF_MAIN_THREAD_FUNCTION(screen_open) {
    width = (int)BF_ARG(0);
    height = (int)BF_ARG(1);
    int scale = (int)BF_ARG(2);
    int64_t *title_cells = BF_POINTER(3);
    char title[256];
    int n = title_cells[0] < 255 ? (int)title_cells[0] : 255;
    for (int i = 0; i < n; i++) title[i] = (char)title_cells[i + 1];
    title[n] = 0;

    if (SDL_Init(SDL_INIT_VIDEO) != 0) {
        fprintf(stderr, "SDL_Init: %s\n", SDL_GetError());
        BF_RETURN(0);
    }
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "0"); // sharp pixels
    window = SDL_CreateWindow(title, SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, width * scale, height * scale, SDL_WINDOW_ALLOW_HIGHDPI);
    renderer = window ? SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC) : NULL;
    texture = renderer ? SDL_CreateTexture(renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STREAMING, width, height) : NULL;
    rgb = malloc(sizeof(uint32_t) * width * height);
    if (!texture || !rgb) {
        fprintf(stderr, "can't open a window: %s\n", SDL_GetError());
        BF_RETURN(0);
    }
    SDL_RenderSetLogicalSize(renderer, width, height);
    ticks_per_second = SDL_GetPerformanceFrequency();
    frame_due = SDL_GetPerformanceCounter();
    open_audio();
    SDL_InitSubSystem(SDL_INIT_GAMECONTROLLER);
    BF_RETURN(1);
}

// screen_show(pixels): shows the framebuffer, and waits for the next frame;
// false once the window's been closed
BF_MAIN_THREAD_FUNCTION(screen_show) {
    int64_t *pixels = BF_POINTER(0);
    if (pixels[0] < (int64_t)width * height) {
        fprintf(stderr, "screen_show: the framebuffer has %lld pixels, not %d\n", (long long)pixels[0], width * height);
        exit(1);
    }
    for (int i = 0; i < width * height; i++) rgb[i] = 0xff000000u | (uint32_t)(pixels[i + 1] & 0xffffff);
    SDL_UpdateTexture(texture, NULL, rgb, width * sizeof(uint32_t));
    SDL_RenderClear(renderer);
    SDL_RenderCopy(renderer, texture, NULL, NULL);
    SDL_RenderPresent(renderer);
    uint64_t now = SDL_GetPerformanceCounter();
    uint64_t period = ticks_per_second / 60;
    frame_due += period;
    if (now > frame_due + 2 * period) {
        // (far behind, after a slow frame or a pause: a new schedule from now)
        frame_due = now;
    } else {
        // (waiting out the rest of the frame: sleeping most of it, then the
        // last millisecond or so on the clock, which sleeping can't time)
        while (now < frame_due) {
            uint64_t left_ms = (frame_due - now) * 1000 / ticks_per_second;
            if (left_ms > 2) SDL_Delay((uint32_t)(left_ms - 2));
            now = SDL_GetPerformanceCounter();
        }
    }

    memset(pressed, 0, sizeof pressed);
    mouse_clicks = 0;
    right_clicks = 0;
    memset(pad_pressed_now, 0, sizeof pad_pressed_now);
    int open = 1;
    SDL_Event e;
    while (SDL_PollEvent(&e)) {
        if (e.type == SDL_QUIT) open = 0;
        if (e.type == SDL_KEYDOWN && !e.key.repeat) pressed[e.key.keysym.scancode] = 1;
        if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_LEFT) mouse_clicks++;
        if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_RIGHT) right_clicks++;
        if (e.type == SDL_CONTROLLERDEVICEADDED && !pad) pad = SDL_GameControllerOpen(e.cdevice.which);
        if (e.type == SDL_CONTROLLERDEVICEREMOVED && pad && !SDL_GameControllerGetAttached(pad)) {
            SDL_GameControllerClose(pad);
            pad = NULL;
        }
        if (e.type == SDL_CONTROLLERBUTTONDOWN && e.cbutton.button < SDL_CONTROLLER_BUTTON_MAX) pad_pressed_now[e.cbutton.button] = 1;
        // (in the framebuffer's pixels, since the renderer has its logical size)
        if (e.type == SDL_MOUSEMOTION) {
            mouse_x_now = e.motion.x;
            mouse_y_now = e.motion.y;
        }
    }
    mouse_held = (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_LMASK) != 0;
    BF_RETURN(open);
}

// key_down(key): whether it's held down
BF_FUNCTION(key_down) {
    SDL_Scancode s = scancode(BF_ARG(0));
    BF_RETURN(s != SDL_SCANCODE_UNKNOWN && SDL_GetKeyboardState(NULL)[s]);
}

// key_pressed(key): whether it went down since the frame before
BF_FUNCTION(key_pressed) {
    SDL_Scancode s = scancode(BF_ARG(0));
    BF_RETURN(s != SDL_SCANCODE_UNKNOWN && pressed[s]);
}

BF_FUNCTION(mouse_x) {
    BF_RETURN(mouse_x_now < 0 ? 0 : mouse_x_now >= width ? width - 1 : mouse_x_now);
}

BF_FUNCTION(mouse_y) {
    BF_RETURN(mouse_y_now < 0 ? 0 : mouse_y_now >= height ? height - 1 : mouse_y_now);
}

// mouse_down(): whether the left button's held down
BF_FUNCTION(mouse_down) {
    BF_RETURN(mouse_held);
}

// mouse_clicked(): whether the left button went down since the frame before
BF_FUNCTION(mouse_clicked) {
    BF_RETURN(mouse_clicks > 0);
}

// mouse_right(): whether the right button went down since the frame before
BF_FUNCTION(mouse_right) {
    BF_RETURN(right_clicks > 0);
}

// screen_ticks(): milliseconds since the window opened
BF_FUNCTION(screen_ticks) {
    BF_RETURN(SDL_GetTicks64());
}

// screen_beep(on): starts or stops the beep
BF_FUNCTION(screen_beep) {
    beeping = BF_ARG(0) != 0;
    BF_RETURN(0);
}

// ---- a game controller (SDL's numbering: buttons 0 A, 1 B, 2 X, 3 Y, 4
// back, 6 start, 11 to 14 the d-pad up, down, left, right; axes 0 and 1
// the left stick, 2 and 3 the right, 4 and 5 the triggers)

// pad_axis(n): -32768 to 32767, or 0 with no controller
BF_FUNCTION(pad_axis) {
    BF_RETURN(pad ? SDL_GameControllerGetAxis(pad, (SDL_GameControllerAxis)BF_ARG(0)) : 0);
}

// pad_down(n): whether the button's held down
BF_FUNCTION(pad_down) {
    BF_RETURN(pad ? SDL_GameControllerGetButton(pad, (SDL_GameControllerButton)BF_ARG(0)) : 0);
}

// pad_pressed(n): whether it went down since the frame before
BF_FUNCTION(pad_pressed) {
    int64_t b = BF_ARG(0);
    BF_RETURN(b >= 0 && b < SDL_CONTROLLER_BUTTON_MAX && pad_pressed_now[b]);
}

// screen_full(on): fills the screen (keeping the picture's shape), or
// goes back to a window
BF_MAIN_THREAD_FUNCTION(screen_full) {
    if (window) {
        SDL_SetWindowFullscreen(window, BF_ARG(0) ? SDL_WINDOW_FULLSCREEN_DESKTOP : 0);
        SDL_ShowCursor(BF_ARG(0) ? SDL_DISABLE : SDL_ENABLE);
    }
    BF_RETURN(0);
}

// ---- files

// (the program's `main` is the C that fern made, so the command line is
// saved before it starts: macOS and Linux both give a constructor argc
// and argv)
__attribute__((constructor)) static void save_args(int argc, char **argv) {
    arg_count = argc;
    arg_values = argv;
}

// load_arg_file(n, into, at): the bytes of the file named by command-line
// argument n (1 is the first), into into's elements from at; how many, or
// -1 if there's no such argument or file, or it doesn't fit
BF_FUNCTION(load_arg_file) {
    int64_t n = BF_ARG(0), *into = BF_POINTER(1), at = BF_ARG(2);
    if (n < 1 || n >= arg_count) BF_RETURN(-1);
    FILE *f = fopen(arg_values[n], "rb");
    if (!f) BF_RETURN(-1);
    int64_t count = 0;
    int c;
    while ((c = fgetc(f)) != EOF) {
        if (at + count >= into[0]) {
            fclose(f);
            BF_RETURN(-1);
        }
        into[1 + at + count++] = c;
    }
    fclose(f);
    BF_RETURN(count);
}

// where saved files go: the user's own folder for this program (SDL's
// "pref path"), name and all; 0 if it's too long
static int saved_path(int64_t *cells, char *path, size_t size) {
    char *dir = SDL_GetPrefPath("fern", "arcade");
    if (!dir) return 0;
    size_t d = strlen(dir);
    if (d + cells[0] + 1 > size) { SDL_free(dir); return 0; }
    memcpy(path, dir, d);
    for (int64_t i = 0; i < cells[0]; i++) path[d + i] = (char)cells[i + 1];
    path[d + cells[0]] = 0;
    SDL_free(dir);
    return 1;
}

// file_save(name, cells, n): writes the first n cells, a number a line, to
// the file `name` in this user's folder for these programs; whether it could
BF_FUNCTION(file_save) {
    int64_t *data = BF_POINTER(1), n = BF_ARG(2);
    char path[1024], temp[1040];
    if (n > data[0] || !saved_path(BF_POINTER(0), path, sizeof path)) BF_RETURN(0);
    // (written beside it, then moved over it, so a crash can't leave half a file)
    snprintf(temp, sizeof temp, "%s.new", path);
    FILE *f = fopen(temp, "w");
    if (!f) BF_RETURN(0);
    for (int64_t i = 0; i < n; i++) fprintf(f, "%lld\n", (long long)data[i + 1]);
    int ok = fclose(f) == 0 && rename(temp, path) == 0;
    BF_RETURN(ok);
}

// file_load(name, into): the numbers file_save wrote, into into's cells;
// how many, or -1 if there's no such file
BF_FUNCTION(file_load) {
    int64_t *into = BF_POINTER(1);
    char path[1024];
    if (!saved_path(BF_POINTER(0), path, sizeof path)) BF_RETURN(-1);
    FILE *f = fopen(path, "r");
    if (!f) BF_RETURN(-1);
    long long x;
    int64_t n = 0;
    while (n < into[0] && fscanf(f, "%lld", &x) == 1) into[1 + n++] = x;
    fclose(f);
    BF_RETURN(n);
}

// ---- other programs

// screen_run(name): runs the program `name` in the same folder as this one
// (another of these programs), with this one's window hidden until it's
// done; its exit status, or -1 if it couldn't start
BF_MAIN_THREAD_FUNCTION(screen_run) {
    int64_t *cells = BF_POINTER(0);
    char path[1024];
    const char *self = arg_count > 0 ? arg_values[0] : "";
    const char *slash = strrchr(self, '/');
    int dir = slash ? (int)(slash - self) + 1 : 0;
    if (dir + cells[0] >= (int64_t)sizeof path) BF_RETURN(-1);
    memcpy(path, self, dir);
    for (int64_t i = 0; i < cells[0]; i++) path[dir + i] = (char)cells[i + 1];
    path[dir + cells[0]] = 0;
    if (window) SDL_HideWindow(window);
    char *argv[] = {path, NULL};
    pid_t pid;
    int status = -1;
    if (posix_spawn(&pid, path, NULL, NULL, argv, environ) == 0) waitpid(pid, &status, 0);
    if (window) {
        SDL_ShowWindow(window);
        SDL_RaiseWindow(window);
    }
    // (what was typed and clicked meanwhile was for the other program)
    SDL_FlushEvents(SDL_FIRSTEVENT, SDL_LASTEVENT);
    memset(pressed, 0, sizeof pressed);
    mouse_clicks = right_clicks = 0;
    BF_RETURN(status);
}
