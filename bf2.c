#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

static int64_t *stack[1024];
static int64_t tape[30000], *ptr=tape, acc=0;

int test() {
    return 5;
}

int main(int argc, char **argv) {
    if (argc <= 1) {
        fprintf(stderr, "Usage: bf2 <file>");
        return 1;
    }

    FILE *file = fopen(argv[1], "r");

    fseek(file, 0, SEEK_END);
    size_t size = ftell(file);
    rewind(file);


    char *data = malloc(size);
    fread(data, size, 1, file);

    for (int i=0; i<size; i++) {
        printf("%c", data[i]);
    }

    char *op = test;

    printf("%d", (int (*op)())());
    return 0;
}