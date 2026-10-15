//! Connected regions of a 200x200 grid with random walls, by breadth-first
//! search with a queue from each cell not yet reached; prints how many
//! there are and the size of the largest.

mod common;

use bf::asm::*;
use common::*;

const S: i64 = 200;

#[test]
fn floodfill_prints_what_c_does() {
    let ops = program(|o| {
        let (grid, queue, start, head, tail, at, t, n) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, grid, S * S);
        heap_alloc_const(o, queue, S * S);
        // 1 for a wall, 0 for open, 2 once reached
        set(o, n, 555);
        for_const(o, start, 0, S * S, R0, |o| {
            lcg(o, n);
            mov(o, t, n);
            rshu_const(o, t, 8);
            rem_const(o, t, 100);
            lt_const(o, t, 41);
            store_index(o, grid, start, t);
        });
        // the regions in the globals: how many, and the largest
        heap_alloc_const(o, R9, 2);
        set(o, &g(0), 0);
        set(o, &g(1), 0);
        for_const(o, start, 0, S * S, R0, |o| {
            load_index(o, t, grid, start);
            eq_const(o, t, 0);
            begin_if(o, t);
            inc(o, &g(0));
            set(o, t, 2);
            store_index(o, grid, start, t);
            set(o, head, 0);
            set(o, tail, 1);
            store_index(o, queue, head, start);
            while_loop(o, R0, |o| { mov(o, R0, head); lt_assign(o, R0, tail); }, |o| {
                load_index(o, at, queue, head);
                inc(o, head);
                // the four neighbours that are on the grid
                for (dir, edge) in [(-S, 0), (S, 1), (-1, 2), (1, 3)] {
                    match edge {
                        0 => { mov(o, t, at); ge_const(o, t, S); }
                        1 => { mov(o, t, at); lt_const(o, t, S * S - S); }
                        2 => { mov(o, t, at); rem_const(o, t, S); ne_const(o, t, 0); }
                        _ => { mov(o, t, at); rem_const(o, t, S); ne_const(o, t, S - 1); }
                    }
                    begin_if(o, t);
                    mov(o, n, at);
                    add_const(o, n, dir);
                    load_index(o, t, grid, n);
                    eq_const(o, t, 0);
                    begin_if(o, t);
                    set(o, t, 2);
                    store_index(o, grid, n, t);
                    store_index(o, queue, tail, n);
                    inc(o, tail);
                    end_if(o);
                    end_if(o);
                }
            });
            max_assign(o, &g(1), tail);
            end_if(o);
        });
        putint(o, &g(0));
        puts(o, " ");
        putint(o, &g(1));
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define S {S}
static int64_t grid[S * S], queue[S * S];
int main(void) {{
    int64_t n = 555;
    for (int64_t k = 0; k < S * S; k++) {{ LCG(n); grid[k] = (n >> 8) % 100 < 41; }}
    int64_t regions = 0, largest = 0;
    for (int64_t start = 0; start < S * S; start++) {{
        if (grid[start] != 0) continue;
        regions++;
        grid[start] = 2;
        int64_t head = 0, tail = 1;
        queue[0] = start;
        while (head < tail) {{
            int64_t at = queue[head++];
            int64_t dirs[4] = {{-S, S, -1, 1}};
            int ok[4] = {{at >= S, at < S * S - S, at % S != 0, at % S != S - 1}};
            for (int d = 0; d < 4; d++)
                if (ok[d] && grid[at + dirs[d]] == 0) {{ grid[at + dirs[d]] = 2; queue[tail++] = at + dirs[d]; }}
        }}
        if (tail > largest) largest = tail;
    }}
    printf("%lld %lld\n", (long long)regions, (long long)largest);
}}
"#
    );
    check("floodfill", &ops, &c);
}
