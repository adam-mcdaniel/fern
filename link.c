#include <stdint.h>
#include <stdio.h>

void do_a_thing(int64_t **tape, int64_t **ptr, int64_t *acc) {
    *acc = '?';
}

void debug(int64_t **tape, int64_t **ptr, int64_t *acc) {
    printf("\n[TAPE]");
    for (int i=0; i<256; i++) {
        if (i % 4 == 0) printf("\n[%04d]: ", i);

        printf("%16llx", (*tape)[i]);
    }
}

void putint(int64_t **tape, int64_t **ptr, int64_t *acc) {
    printf("%lld", **ptr);
}
