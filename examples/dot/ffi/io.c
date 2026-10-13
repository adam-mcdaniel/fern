// File I/O for DOT programs, in C: each function here is declared in
// io.dot with `extern def`, and linked into its native build. `DOT_EXTERN`
// writes each as the VM calls it, taking the arguments from their cells as
// the declaration's types say, and leaving the result in the accumulator.

#include <stdio.h>
#include <stdlib.h>
#include "dot.h"

// extern def write_file(path: String, text: String): Bool
// Writes `text` to the file `path`, and says whether it could.
DOT_EXTERN(Bool, write_file, (String, path), (String, text)) {
    FILE *f = fopen(path, "w");
    if (!f) return false;
    fputs(text, f);
    fclose(f);
    return true;
}

// extern def read_file(path: String, into: Int, capacity: Int): Int
// Reads the file `path` into a buffer, and gives how many characters it
// read, or -1 if it couldn't.
DOT_EXTERN(Int, read_file, (String, path), (Any, into), (Int, capacity)) {
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    char *text = malloc((size_t)capacity);
    size_t n = fread(text, 1, (size_t)capacity, f);
    fclose(f);
    int64_t got = dot_fill(into, capacity, text, n);
    free(text);
    return got;
}

// extern def env_var(name: String, into: Int, capacity: Int): Int
// Reads the environment variable `name` into a buffer, giving its length,
// or -1 if it isn't set.
DOT_EXTERN(Int, env_var, (String, name), (Any, into), (Int, capacity)) {
    const char *value = getenv(name);
    return value ? dot_fill(into, capacity, value, strlen(value)) : -1;
}
