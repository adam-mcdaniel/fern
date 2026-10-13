/*
 * bfsys.h -- single-header "standard library" / system-call table for a
 * BrainF***-with-`!` turing tarpit.   Just  #include "bfsys.h"  once.
 *
 * Every syscall has the signature  cell fn(cell)  -- exactly one cell in,
 * exactly one cell out.  No syscall takes or returns a pointer; the `p`
 * member of the union is never used by this library.  Anything that would
 * normally need a string, a second argument, or an out-parameter goes
 * through the library's single byte buffer ("the buffer") instead:
 *
 *   - Build a string by calling buf_push once per byte.
 *   - Syscalls that need a path/name/command read it from the buffer.
 *   - Syscalls that produce text (read, getcwd, fmt_int, ...) append it
 *     to the buffer; drain it with buf_pop.
 *   - A few calls need two strings; those are NUL-separated in the buffer
 *     ("old\0new" for rename, "name\0value" for setenv, argv for exec).
 *
 * File I/O goes through one "current fd" register set by `fd`.  It starts
 * at 0 (stdin), so `read` works out of the box; call fd(1) before `write`,
 * or just use `putc`.
 *
 * Suggested interpreter convention for `!`:
 *
 *      p[1] = bf_syscall(p[0].i, p[1]);
 *
 * i.e. the current cell holds the syscall number, the cell to its right
 * holds the argument and receives the result.  Any other convention works
 * too; the library only cares that you call bf_syscall_table[n](arg).
 *
 * Integer results use cell.i; -1 (all bits set) means failure and the
 * `errno` syscall tells you why.  Float results use cell.f.
 */
#ifndef BFSYS_H
#define BFSYS_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <math.h>
#include <time.h>
#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <termios.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>

typedef union cell {
    double      f;
    uint64_t    i;
    union cell *p;
} cell;

typedef cell (*bf_syscall_fn)(cell);

/* name             arg (in)             result (out)                                */
#define BF_SYSCALLS(X)                                                                 \
    /* --- core ---------------------------------------------------------------- */   \
    X(nop)        /* x                    x                                          */ \
    X(putc)       /* byte                 1, or -1                (writes to stdout) */ \
    X(getc)       /* -                    byte, or -1 on EOF      (reads from stdin) */ \
    X(exit)       /* status               never returns                              */ \
    X(errno)      /* -                    errno of the last failing call             */ \
    X(strerror)   /* errno                len; message appended to buffer            */ \
    /* --- the buffer ---------------------------------------------------------- */   \
    X(buf_clear)  /* -                    0                                          */ \
    X(buf_push)   /* byte                 new length                                 */ \
    X(buf_pop)    /* -                    first byte (removed), or -1 if empty       */ \
    X(buf_get)    /* index                byte at index, or -1                       */ \
    X(buf_drop)   /* n                    bytes actually dropped from the front      */ \
    X(buf_len)    /* -                    length                                     */ \
    /* --- file descriptors ---------------------------------------------------- */   \
    X(fd)         /* fd                   fd   (selects the current fd)              */ \
    X(open)       /* flags (BF_O_*)       fd, or -1               (path = buffer)    */ \
    X(close)      /* fd                   0, or -1                                   */ \
    X(read)       /* max bytes (0=64K)    bytes appended to buffer, 0 at EOF, -1     */ \
    X(write)      /* max bytes (0=all)    bytes written from buffer front, or -1     */ \
    X(seek_set)   /* offset               new offset, or -1                          */ \
    X(seek_cur)   /* offset               new offset, or -1                          */ \
    X(seek_end)   /* offset               new offset, or -1                          */ \
    X(isatty)     /* fd                   1 or 0                                     */ \
    X(tty_raw)    /* 1/0                  0, or -1  (raw mode on stdin; auto-reset)  */ \
    /* --- filesystem (path = buffer) ------------------------------------------ */   \
    X(unlink)     /* -                    0, or -1                                   */ \
    X(rename)     /* -                    0, or -1                ("old\0new")       */ \
    X(mkdir)      /* mode (0 = 0755)      0, or -1                                   */ \
    X(rmdir)      /* -                    0, or -1                                   */ \
    X(chdir)      /* -                    0, or -1                                   */ \
    X(getcwd)     /* -                    len; path appended to buffer               */ \
    X(fsize)      /* -                    size in bytes, or -1                       */ \
    X(ftype)      /* -                    0 none, 1 file, 2 dir, 3 other             */ \
    X(dir_open)   /* -                    0, or -1                                   */ \
    X(dir_next)   /* -                    len (name appended), or -1 when done       */ \
    X(dir_close)  /* -                    0                                          */ \
    /* --- processes & environment --------------------------------------------- */   \
    X(argc)       /* -                    number of program arguments                */ \
    X(argv)       /* index                len (arg appended to buffer), or -1        */ \
    X(getenv)     /* -                    len (buffer := value), or -1  (name = buf) */ \
    X(setenv)     /* -                    0, or -1                ("name\0value")    */ \
    X(system)     /* -                    exit status             (command = buffer) */ \
    X(fork)       /* -                    child pid / 0 in child / -1                */ \
    X(exec)       /* -                    -1 on failure   (argv = NUL-separated buf) */ \
    X(wait)       /* pid (-1 = any)       exit status, 128+sig if killed, or -1      */ \
    X(getpid)     /* -                    pid                                        */ \
    /* --- time & randomness --------------------------------------------------- */   \
    X(time)       /* -                    unix seconds                               */ \
    X(clock)      /* -                    monotonic nanoseconds                      */ \
    X(sleep)      /* nanoseconds          0                                          */ \
    X(rand)       /* -                    64 random bits                             */ \
    X(srand)      /* seed                 0                                          */ \
    /* --- networking (TCP) ---------------------------------------------------- */   \
    X(tcp_connect)/* port                 fd, or -1               (host = buffer)    */ \
    X(tcp_listen) /* port                 listening fd, or -1                        */ \
    X(tcp_accept) /* listening fd         connected fd, or -1                        */ \
    /* --- numbers (pure) ------------------------------------------------------ */   \
    X(itof)       /* i                    (double) (int64) i                         */ \
    X(ftoi)       /* f                    (int64) f                                  */ \
    X(fmt_int)    /* i                    len; decimal (signed) appended to buffer   */ \
    X(fmt_float)  /* f                    len; shortest round-trip repr appended     */ \
    X(parse_int)  /* -                    value parsed from buffer front (consumed)  */ \
    X(parse_float)/* -                    value parsed from buffer front (consumed)  */ \
    X(sqrt)  X(sin)  X(cos)  X(atan)  X(exp)  X(log)  X(floor)  /* f -> f          */

enum {
#define X(name) BF_SYS_##name,
    BF_SYSCALLS(X)
#undef X
    BF_SYS_COUNT
};

/* flags for `open` (OR them together) */
enum {
    BF_O_READ   = 1,
    BF_O_WRITE  = 2,
    BF_O_CREATE = 4,
    BF_O_TRUNC  = 8,
    BF_O_APPEND = 16,
};

/* ========================================================================== */
/*  Implementation                                                             */
/* ========================================================================== */

#define BF_ERR ((uint64_t)-1)

#if defined(__GNUC__) || defined(__clang__)
#  define BF_UNUSED __attribute__((unused))
#else
#  define BF_UNUSED
#endif

static cell bf_I(uint64_t v) { cell c; c.i = v; return c; }
static cell bf_F(double   v) { cell c; c.f = v; return c; }
static cell bf_R(long long r) { return bf_I(r < 0 ? BF_ERR : (uint64_t)r); }   /* -1 -> BF_ERR */

/* ---- state ---------------------------------------------------------------- */
static uint8_t *bf_buf;                 /* the buffer: bytes [bf_head, bf_tail) */
static size_t   bf_head, bf_tail, bf_cap;
static int      bf_cur_fd;              /* current fd for read/write/seek       */
static DIR     *bf_dir;
static int      bf_argc;
static char   **bf_argv;
static uint64_t bf_rng;
static int      bf_rng_seeded;
static struct termios bf_tty_saved;
static int      bf_tty_is_raw;

/* ---- buffer internals ----------------------------------------------------- */
static size_t bf_blen(void) { return bf_tail - bf_head; }

static void bf_reserve(size_t extra) {
    if (bf_tail + extra <= bf_cap) return;
    if (bf_head) {                      /* compact */
        memmove(bf_buf, bf_buf + bf_head, bf_blen());
        bf_tail -= bf_head;
        bf_head = 0;
    }
    if (bf_tail + extra > bf_cap) {
        size_t ncap = bf_cap ? bf_cap * 2 : 256;
        while (ncap < bf_tail + extra) ncap *= 2;
        bf_buf = (uint8_t *)realloc(bf_buf, ncap);
        if (!bf_buf) { perror("bfsys: out of memory"); abort(); }
        bf_cap = ncap;
    }
}

static void bf_append(const void *src, size_t n) {
    bf_reserve(n);
    memcpy(bf_buf + bf_tail, src, n);
    bf_tail += n;
}

static size_t bf_drop(size_t n) {
    if (n > bf_blen()) n = bf_blen();
    bf_head += n;
    if (bf_head == bf_tail) bf_head = bf_tail = 0;
    return n;
}

/* NUL-terminated view of the buffer (stays valid until the next buffer change) */
static const char *bf_cstr(void) {
    bf_reserve(1);
    bf_buf[bf_tail] = 0;
    return (const char *)bf_buf + bf_head;
}

/* Second string in a "a\0b" buffer, or "" if there is none. */
static const char *bf_cstr2(void) {
    const char *a = bf_cstr();
    size_t n = strlen(a);
    return (n < bf_blen()) ? a + n + 1 : "";
}

static cell bf_append_str(const char *s) {          /* returns length pushed */
    size_t n = strlen(s);
    bf_append(s, n);
    return bf_I(n);
}

/* ---- tty helper ----------------------------------------------------------- */
static void bf_tty_restore(void) {
    if (bf_tty_is_raw) { tcsetattr(0, TCSAFLUSH, &bf_tty_saved); bf_tty_is_raw = 0; }
}

/* ---- rng (splitmix64) ----------------------------------------------------- */
static uint64_t bf_next_rand(void) {
    if (!bf_rng_seeded) {
        struct timespec ts; clock_gettime(CLOCK_REALTIME, &ts);
        bf_rng = (uint64_t)ts.tv_sec * 1000000007ull ^ (uint64_t)ts.tv_nsec ^ ((uint64_t)getpid() << 32);
        bf_rng_seeded = 1;
    }
    uint64_t z = (bf_rng += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

/* ========================================================================== */
/*  Syscalls -- every one is  cell sys_name(cell)                               */
/* ========================================================================== */

/* --- core ------------------------------------------------------------------ */
static cell sys_nop(cell a) { return a; }

static cell sys_putc(cell a) {
    unsigned char b = (unsigned char)a.i;
    return bf_R(write(1, &b, 1));
}

static cell sys_getc(cell a) {
    unsigned char b; (void)a;
    return read(0, &b, 1) == 1 ? bf_I(b) : bf_I(BF_ERR);
}

static cell sys_exit(cell a) {
    bf_tty_restore();
    exit((int)a.i);
}

static cell sys_errno(cell a) { (void)a; return bf_I((uint64_t)errno); }

static cell sys_strerror(cell a) { return bf_append_str(strerror((int)a.i)); }

/* --- the buffer ------------------------------------------------------------ */
static cell sys_buf_clear(cell a) { (void)a; bf_head = bf_tail = 0; return bf_I(0); }

static cell sys_buf_push(cell a) {
    uint8_t b = (uint8_t)a.i;
    bf_append(&b, 1);
    return bf_I(bf_blen());
}

static cell sys_buf_pop(cell a) {
    (void)a;
    if (!bf_blen()) return bf_I(BF_ERR);
    uint8_t b = bf_buf[bf_head];
    bf_drop(1);
    return bf_I(b);
}

static cell sys_buf_get(cell a) {
    return a.i < bf_blen() ? bf_I(bf_buf[bf_head + a.i]) : bf_I(BF_ERR);
}

static cell sys_buf_drop(cell a) { return bf_I(bf_drop((size_t)a.i)); }
static cell sys_buf_len (cell a) { (void)a; return bf_I(bf_blen()); }

/* --- file descriptors ------------------------------------------------------ */
static cell sys_fd(cell a) { bf_cur_fd = (int)a.i; return a; }

static cell sys_open(cell a) {
    uint64_t f = a.i;
    int flags = (f & BF_O_READ) && (f & BF_O_WRITE) ? O_RDWR
              : (f & BF_O_WRITE)                    ? O_WRONLY
              :                                       O_RDONLY;
    if (f & BF_O_CREATE) flags |= O_CREAT;
    if (f & BF_O_TRUNC)  flags |= O_TRUNC;
    if (f & BF_O_APPEND) flags |= O_APPEND;
    return bf_R(open(bf_cstr(), flags, 0644));
}

static cell sys_close(cell a) { return bf_R(close((int)a.i)); }

static cell sys_read(cell a) {
    size_t n = a.i ? (size_t)a.i : 65536;
    bf_reserve(n);
    ssize_t r = read(bf_cur_fd, bf_buf + bf_tail, n);
    if (r > 0) bf_tail += (size_t)r;
    return bf_R(r);
}

static cell sys_write(cell a) {
    size_t n = a.i && a.i < bf_blen() ? (size_t)a.i : bf_blen();
    ssize_t w = write(bf_cur_fd, bf_buf + bf_head, n);
    if (w > 0) bf_drop((size_t)w);
    return bf_R(w);
}

static cell sys_seek_set(cell a) { return bf_R(lseek(bf_cur_fd, (off_t)(int64_t)a.i, SEEK_SET)); }
static cell sys_seek_cur(cell a) { return bf_R(lseek(bf_cur_fd, (off_t)(int64_t)a.i, SEEK_CUR)); }
static cell sys_seek_end(cell a) { return bf_R(lseek(bf_cur_fd, (off_t)(int64_t)a.i, SEEK_END)); }

static cell sys_isatty(cell a) { return bf_I((uint64_t)isatty((int)a.i)); }

static cell sys_tty_raw(cell a) {
    if (!a.i) { bf_tty_restore(); return bf_I(0); }
    if (bf_tty_is_raw) return bf_I(0);
    if (tcgetattr(0, &bf_tty_saved) < 0) return bf_I(BF_ERR);
    struct termios raw = bf_tty_saved;
    cfmakeraw(&raw);
    if (tcsetattr(0, TCSAFLUSH, &raw) < 0) return bf_I(BF_ERR);
    bf_tty_is_raw = 1;
    atexit(bf_tty_restore);
    return bf_I(0);
}

/* --- filesystem (path = buffer) -------------------------------------------- */
static cell sys_unlink(cell a) { (void)a; return bf_R(unlink(bf_cstr())); }
static cell sys_rename(cell a) { (void)a; return bf_R(rename(bf_cstr(), bf_cstr2())); }
static cell sys_mkdir (cell a) { return bf_R(mkdir(bf_cstr(), a.i ? (mode_t)a.i : 0755)); }
static cell sys_rmdir (cell a) { (void)a; return bf_R(rmdir(bf_cstr())); }
static cell sys_chdir (cell a) { (void)a; return bf_R(chdir(bf_cstr())); }

static cell sys_getcwd(cell a) {
    char tmp[4096]; (void)a;
    if (!getcwd(tmp, sizeof tmp)) return bf_I(BF_ERR);
    return bf_append_str(tmp);
}

static cell sys_fsize(cell a) {
    struct stat st; (void)a;
    if (stat(bf_cstr(), &st) < 0) return bf_I(BF_ERR);
    return bf_I((uint64_t)st.st_size);
}

static cell sys_ftype(cell a) {
    struct stat st; (void)a;
    if (stat(bf_cstr(), &st) < 0) return bf_I(0);
    if (S_ISREG(st.st_mode)) return bf_I(1);
    if (S_ISDIR(st.st_mode)) return bf_I(2);
    return bf_I(3);
}

static cell sys_dir_close(cell a) {
    (void)a;
    if (bf_dir) { closedir(bf_dir); bf_dir = NULL; }
    return bf_I(0);
}

static cell sys_dir_open(cell a) {
    sys_dir_close(a);
    bf_dir = opendir(bf_cstr());
    return bf_I(bf_dir ? 0 : BF_ERR);
}

static cell sys_dir_next(cell a) {
    struct dirent *e;
    if (!bf_dir) return bf_I(BF_ERR);
    while ((e = readdir(bf_dir)) != NULL)
        if (strcmp(e->d_name, ".") && strcmp(e->d_name, ".."))
            return bf_append_str(e->d_name);
    sys_dir_close(a);
    return bf_I(BF_ERR);
}

/* --- processes & environment ----------------------------------------------- */
static cell sys_argc(cell a) { (void)a; return bf_I((uint64_t)bf_argc); }

static cell sys_argv(cell a) {
    return a.i < (uint64_t)bf_argc ? bf_append_str(bf_argv[a.i]) : bf_I(BF_ERR);
}

static cell sys_getenv(cell a) {
    const char *v = getenv(bf_cstr());
    if (!v) return bf_I(BF_ERR);
    sys_buf_clear(a);
    return bf_append_str(v);
}

static cell sys_setenv(cell a) { (void)a; return bf_R(setenv(bf_cstr(), bf_cstr2(), 1)); }

static cell sys_system(cell a) {
    (void)a;
    int st = system(bf_cstr());
    if (st < 0) return bf_I(BF_ERR);
    return bf_I(WIFEXITED(st) ? (uint64_t)WEXITSTATUS(st) : 128u + (uint64_t)WTERMSIG(st));
}

static cell sys_fork(cell a) { (void)a; return bf_R(fork()); }

static cell sys_exec(cell a) {
    /* buffer = "prog\0arg1\0arg2\0..."  (a trailing NUL is optional) */
    (void)a;
    const char *s = bf_cstr();
    size_t n = bf_blen(), count = 0;
    for (size_t i = 0; i < n; i++) if (s[i] == 0) count++;
    if (n && s[n - 1] != 0) count++;
    char **argv = (char **)calloc(count + 1, sizeof(char *));
    if (!argv) return bf_I(BF_ERR);
    size_t k = 0;
    for (size_t i = 0; i < n && k < count; i++) {
        argv[k++] = (char *)s + i;
        while (i < n && s[i]) i++;
    }
    if (count) execvp(argv[0], argv);
    free(argv);
    return bf_I(BF_ERR);
}

static cell sys_wait(cell a) {
    int st;
    if (waitpid((pid_t)(int64_t)a.i, &st, 0) < 0) return bf_I(BF_ERR);
    return bf_I(WIFEXITED(st) ? (uint64_t)WEXITSTATUS(st) : 128u + (uint64_t)WTERMSIG(st));
}

static cell sys_getpid(cell a) { (void)a; return bf_I((uint64_t)getpid()); }

/* --- time & randomness ----------------------------------------------------- */
static cell sys_time(cell a) { (void)a; return bf_I((uint64_t)time(NULL)); }

static cell sys_clock(cell a) {
    struct timespec ts; (void)a;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return bf_I((uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec);
}

static cell sys_sleep(cell a) {
    struct timespec ts = { (time_t)(a.i / 1000000000ull), (long)(a.i % 1000000000ull) };
    while (nanosleep(&ts, &ts) < 0 && errno == EINTR) {}
    return bf_I(0);
}

static cell sys_rand (cell a) { (void)a; return bf_I(bf_next_rand()); }
static cell sys_srand(cell a) { bf_rng = a.i; bf_rng_seeded = 1; return bf_I(0); }

/* --- networking ------------------------------------------------------------ */
static cell sys_tcp_connect(cell a) {
    char port[16]; struct addrinfo hints, *res, *ai; int fd = -1;
    snprintf(port, sizeof port, "%u", (unsigned)(a.i & 0xffff));
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC; hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(bf_cstr(), port, &hints, &res) != 0) { errno = EHOSTUNREACH; return bf_I(BF_ERR); }
    for (ai = res; ai; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) continue;
        if (connect(fd, ai->ai_addr, ai->ai_addrlen) == 0) break;
        close(fd); fd = -1;
    }
    freeaddrinfo(res);
    return bf_R(fd);
}

static cell sys_tcp_listen(cell a) {
    struct sockaddr_in sa; int one = 1;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return bf_I(BF_ERR);
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET; sa.sin_addr.s_addr = htonl(INADDR_ANY);
    sa.sin_port = htons((uint16_t)a.i);
    if (bind(fd, (struct sockaddr *)&sa, sizeof sa) < 0 || listen(fd, 16) < 0) { close(fd); return bf_I(BF_ERR); }
    return bf_I((uint64_t)fd);
}

static cell sys_tcp_accept(cell a) { return bf_R(accept((int)a.i, NULL, NULL)); }

/* --- numbers --------------------------------------------------------------- */
static cell sys_itof(cell a) { return bf_F((double)(int64_t)a.i); }
static cell sys_ftoi(cell a) { return bf_I((uint64_t)(int64_t)a.f); }

static cell sys_fmt_int(cell a) {
    char tmp[32];
    snprintf(tmp, sizeof tmp, "%lld", (long long)(int64_t)a.i);
    return bf_append_str(tmp);
}

static cell sys_fmt_float(cell a) {
    char tmp[32];
    snprintf(tmp, sizeof tmp, "%.15g", a.f);            /* short form if it round-trips */
    if (strtod(tmp, NULL) != a.f) snprintf(tmp, sizeof tmp, "%.17g", a.f);
    return bf_append_str(tmp);
}

static cell sys_parse_int(cell a) {
    const char *s = bf_cstr(); char *end; (void)a;
    long long v = strtoll(s, &end, 0);
    bf_drop((size_t)(end - s));
    return bf_I((uint64_t)v);
}

static cell sys_parse_float(cell a) {
    const char *s = bf_cstr(); char *end; (void)a;
    double v = strtod(s, &end);
    bf_drop((size_t)(end - s));
    return bf_F(v);
}

static cell sys_sqrt (cell a) { return bf_F(sqrt (a.f)); }
static cell sys_sin  (cell a) { return bf_F(sin  (a.f)); }
static cell sys_cos  (cell a) { return bf_F(cos  (a.f)); }
static cell sys_atan (cell a) { return bf_F(atan (a.f)); }
static cell sys_exp  (cell a) { return bf_F(exp  (a.f)); }
static cell sys_log  (cell a) { return bf_F(log  (a.f)); }
static cell sys_floor(cell a) { return bf_F(floor(a.f)); }

/* ========================================================================== */
/*  Table + host helpers                                                       */
/* ========================================================================== */

BF_UNUSED static const bf_syscall_fn bf_syscall_table[BF_SYS_COUNT] = {
#define X(name) sys_##name,
    BF_SYSCALLS(X)
#undef X
};

BF_UNUSED static const char *const bf_syscall_names[BF_SYS_COUNT] = {
#define X(name) #name,
    BF_SYSCALLS(X)
#undef X
};

/* Optional: call once from main() so the `argc`/`argv` syscalls work. */
BF_UNUSED static void bf_init(int argc, char **argv) { bf_argc = argc; bf_argv = argv; }

/* Bounds-checked dispatch: this is what `!` should call. */
BF_UNUSED static cell bf_syscall(uint64_t num, cell arg) {
    if (num >= BF_SYS_COUNT) { errno = ENOSYS; return bf_I(BF_ERR); }
    return bf_syscall_table[num](arg);
}

#endif /* BFSYS_H */
