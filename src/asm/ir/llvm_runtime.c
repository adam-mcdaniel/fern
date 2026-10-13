// The garbage collector behind `gc_alloc` in native code compiled from the
// IR's LLVM backend: a conservative, non-moving mark-sweep collector, like
// the one the VM gets, for native stacks.
//
// The roots are the stack (with the registers saved onto it by setjmp) and
// the module's global cells. A word that points anywhere into an allocated
// object keeps it alive. The heap is one reserved region of pages: a page
// holds objects of one size, with a bit for each saying it's allocated and
// one saying it's marked; an object too big for a page gets a run of pages.
// The collector runs when what's been allocated since the last collection
// is as much as what was live after it (or 1 MB, at first).

#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define PAGE 4096
#define REGION ((size_t)1 << 34) // reserved, not committed until used
#define PAGES (REGION / PAGE)
#define MAX_SMALL 256 // cells: anything bigger gets pages of its own
#define SLOTS (PAGE / 8)

typedef struct {
    // 0: free; else the size of its objects in cells, or for a large
    // object's first page, its size, with `span` its pages; a large object's
    // other pages have `head` set to how far back its first page is
    uint32_t size;
    uint32_t span;
    uint32_t head;
    uint32_t count;
    uint64_t allocated[SLOTS / 64];
    uint64_t marked[SLOTS / 64];
} Page;

static char *heap;
static Page *pages;
static size_t used;            // pages handed out so far, from the start
static void *free_lists[MAX_SMALL + 1];
static uintptr_t stack_bottom;
static int64_t *globals;
static int64_t global_count;
static size_t since_collection, threshold = 1 << 20;
static uintptr_t *mark_stack;
static size_t mark_top, mark_cap;

static int bit(uint64_t *bits, size_t i) { return (bits[i / 64] >> (i % 64)) & 1; }
static void set_bit(uint64_t *bits, size_t i) { bits[i / 64] |= (uint64_t)1 << (i % 64); }
static void clear_bit(uint64_t *bits, size_t i) { bits[i / 64] &= ~((uint64_t)1 << (i % 64)); }

void rt_init(void *bottom, int64_t *cells, int64_t count) {
    heap = mmap(NULL, REGION, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
    pages = mmap(NULL, PAGES * sizeof(Page), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
    if (heap == MAP_FAILED || pages == MAP_FAILED) {
        fputs("out of memory\n", stdout);
        exit(0);
    }
    stack_bottom = (uintptr_t)bottom;
    globals = cells;
    global_count = count;
}

static void push(uintptr_t start, size_t cells) {
    if (mark_top + 2 > mark_cap) {
        mark_cap = mark_cap ? mark_cap * 2 : 1024;
        mark_stack = realloc(mark_stack, mark_cap * sizeof(uintptr_t));
    }
    mark_stack[mark_top++] = start;
    mark_stack[mark_top++] = cells;
}

// Marks the object `w` points into, if it does.
static void mark(uintptr_t w) {
    if (w < (uintptr_t)heap || w >= (uintptr_t)heap + used * PAGE) return;
    size_t p = (w - (uintptr_t)heap) / PAGE;
    if (pages[p].head) p -= pages[p].head;
    Page *pg = &pages[p];
    if (pg->size == 0) return;
    uintptr_t start = (uintptr_t)heap + p * PAGE;
    if (pg->span) {
        // a large object
        if (w >= start + (size_t)pg->size * 8 || !bit(pg->allocated, 0) || bit(pg->marked, 0)) return;
        set_bit(pg->marked, 0);
        push(start, pg->size);
        return;
    }
    size_t slot = (w - start) / ((size_t)pg->size * 8);
    if (slot >= pg->count || !bit(pg->allocated, slot) || bit(pg->marked, slot)) return;
    set_bit(pg->marked, slot);
    push(start + slot * pg->size * 8, pg->size);
}

static void scan(uintptr_t from, uintptr_t to) {
    for (uintptr_t a = from & ~(uintptr_t)7; a + 8 <= to; a += 8) mark(*(uintptr_t *)a);
}

static void __attribute__((noinline)) collect(void) {
    jmp_buf registers;
    setjmp(registers);
    volatile uintptr_t here = (uintptr_t)&registers;
    scan(here, stack_bottom);
    scan((uintptr_t)globals, (uintptr_t)(globals + global_count));
    while (mark_top) {
        size_t cells = mark_stack[--mark_top];
        uintptr_t start = mark_stack[--mark_top];
        scan(start, start + cells * 8);
    }
    // sweep, rebuilding the free lists from what's left
    memset(free_lists, 0, sizeof free_lists);
    size_t live = 0;
    for (size_t p = 0; p < used; p++) {
        Page *pg = &pages[p];
        if (pg->size == 0 || pg->head) continue;
        char *start = heap + p * PAGE;
        if (pg->span) {
            if (bit(pg->marked, 0)) {
                clear_bit(pg->marked, 0);
                live += (size_t)pg->size * 8;
            } else {
                for (size_t q = p; q < p + pg->span; q++) memset(&pages[q], 0, sizeof(Page));
            }
            continue;
        }
        int any = 0;
        for (size_t s = 0; s < pg->count; s++) {
            if (bit(pg->marked, s)) {
                clear_bit(pg->marked, s);
                any = 1;
            } else {
                clear_bit(pg->allocated, s);
            }
        }
        if (!any) {
            memset(pg, 0, sizeof(Page));
            continue;
        }
        for (size_t s = pg->count; s-- > 0;) {
            if (bit(pg->allocated, s)) {
                live += (size_t)pg->size * 8;
                continue;
            }
            void **object = (void **)(start + s * pg->size * 8);
            *object = free_lists[pg->size];
            free_lists[pg->size] = object;
        }
    }
    since_collection = 0;
    threshold = live > (1 << 20) ? live : (1 << 20);
}

// `n` free pages in a row: from the free ones, or else new ones.
static size_t take_pages(size_t n) {
    size_t run = 0;
    for (size_t p = 0; p < used; p++) {
        run = pages[p].size == 0 && pages[p].head == 0 ? run + 1 : 0;
        if (run == n) return p + 1 - n;
    }
    if ((used + n) > PAGES) {
        fputs("out of memory\n", stdout);
        exit(0);
    }
    used += n;
    return used - n;
}

int64_t rt_alloc(int64_t n) {
    size_t cells = n < 1 ? 1 : (size_t)n;
    since_collection += cells * 8;
    if (since_collection > threshold) collect();
    if (cells > MAX_SMALL) {
        size_t span = (cells * 8 + PAGE - 1) / PAGE;
        size_t p = take_pages(span);
        for (size_t q = p + 1; q < p + span; q++) {
            pages[q].head = (uint32_t)(q - p);
            pages[q].size = 1;
        }
        pages[p] = (Page){.size = (uint32_t)cells, .span = (uint32_t)span};
        set_bit(pages[p].allocated, 0);
        char *start = heap + p * PAGE;
        memset(start, 0, span * PAGE);
        return (int64_t)(uintptr_t)start;
    }
    if (!free_lists[cells]) {
        size_t p = take_pages(1);
        Page *pg = &pages[p];
        *pg = (Page){.size = (uint32_t)cells, .count = (uint32_t)(PAGE / (cells * 8))};
        char *start = heap + p * PAGE;
        for (size_t s = pg->count; s-- > 0;) {
            void **object = (void **)(start + s * cells * 8);
            *object = free_lists[cells];
            free_lists[cells] = object;
        }
    }
    void **object = free_lists[cells];
    free_lists[cells] = *object;
    size_t p = ((char *)object - heap) / PAGE;
    size_t slot = ((char *)object - (heap + p * PAGE)) / (cells * 8);
    set_bit(pages[p].allocated, slot);
    memset(object, 0, cells * 8);
    return (int64_t)(uintptr_t)object;
}
