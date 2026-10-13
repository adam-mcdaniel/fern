
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int64_t **stack = NULL;
static int64_t *tape=NULL, *ptr=NULL, acc=0;
static void (*f)() = NULL;
   int main() {stack=malloc(1024 * sizeof(int64_t)); tape=malloc(100000 * sizeof(int64_t)); ptr=tape; ptr += 7;acc = 132;*ptr = acc;ptr += -7;ptr += 8;acc = 2;*ptr = acc;ptr += -8;ptr += 8;acc = *ptr;ptr += -8;ptr += 2;*ptr = acc;ptr += -2;ptr += 2;acc = *ptr;ptr += -2;while (acc) {ptr += 1;acc = 0;*ptr = acc;ptr += -1;ptr += 7;acc = 1;acc = -acc;acc += *ptr;ptr += -7;acc = acc > 0;while (acc) {ptr += 7;acc = 2;acc = -acc;acc += *ptr;*ptr = acc;ptr += -7;ptr += 1;acc = 1;acc += *ptr;*ptr = acc;ptr += -1;ptr += 7;acc = 1;acc = -acc;acc += *ptr;ptr += -7;acc = acc > 0;}ptr += 1;acc = *ptr;ptr += -1;ptr += 7;*ptr = acc;ptr += -7;ptr += 2;acc = 1;acc = -acc;acc += *ptr;*ptr = acc;ptr += -2;ptr += 2;acc = *ptr;ptr += -2;}ptr += 7;acc = *ptr;putchar(acc);ptr += -7;ptr += 7;acc = 10;*ptr = acc;ptr += -7;ptr += 7;acc = *ptr;putchar(acc);ptr += -7; return 0;}
