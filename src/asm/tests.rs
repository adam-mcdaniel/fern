use super::*;
use crate::interp::Machine;

/// `malloc` hands out blocks given back to `free` again: small ones of the
/// same size, the last freed first; big ones, the first that's big enough;
/// and taking and giving back over and over doesn't grow the heap.
#[test]
fn malloc_uses_freed_blocks_again() {
    let mut o = vec![];
    init_with(&mut o, 4096);
    malloc_const(&mut o, R1, 3);
    malloc_const(&mut o, R2, 20);
    malloc_const(&mut o, R3, 3);
    free(&mut o, R1);
    free(&mut o, R3);
    free(&mut o, R2);
    set(&mut o, R0, 0);
    free(&mut o, R0);
    malloc_const(&mut o, R4, 3);
    malloc_const(&mut o, R5, 3);
    malloc_const(&mut o, R6, 18);
    malloc_const(&mut o, R7, 25);
    mov(&mut o, R8, HP);
    set(&mut o, R0, 1000);
    begin_while(&mut o, R0);
    malloc_const(&mut o, R9, 0);
    set(&mut o, &R9.deref(), 7);
    free(&mut o, R9);
    malloc_const(&mut o, R9, 40);
    free(&mut o, R9);
    dec(&mut o, R0);
    end_while(&mut o, R0);
    for machine in [Machine::c(), Machine::cpu_xlen(16), Machine::cpu()] {
        let tape = machine.run(&o, b"").unwrap().tape;
        let r = |n: u64| tape[(19 + n) as usize];
        assert_eq!(r(4), r(3), "the last small block freed first");
        assert_eq!(r(5), r(1));
        assert_eq!(r(6), r(2), "a big block that's big enough");
        assert!(r(7) < r(1) && r(7) < r(2) && r(7) < r(3), "nothing freed fits 25 cells");
        // (only the first time round: a block of 1 cell and one of 40,
        // each with its header)
        assert_eq!(tape[18], r(8) - 43 * machine.stride, "taking and giving back again didn't grow the heap");
    }
}

/// Globals have the same cells wherever they're used, start at 0, and the
/// stack (and the heap) leave them alone.
#[test]
fn globals_stay_where_they_are() {
    let mut g = Globals::new();
    let a = g.var("a", 1);
    let buf = g.var("buf", 40);
    let b = g.var("b", 1);
    assert_eq!(g.var("a", 1), a);
    assert_eq!(g.get("buf"), buf);
    assert_eq!(g.cells(), 42);
    let mut o = vec![];
    // (set before, so that starting has to clear it)
    set(&mut o, &buf.offset(5), 9);
    init_globals(&mut o, 4096, &mut g);
    set(&mut o, &a, 11);
    set(&mut o, &b, 22);
    begin_func(&mut o, "f", 3);
    set(&mut o, &local(0), 33);
    set(&mut o, &local(2), 44);
    mov(&mut o, R0, &arg(0));
    inc(&mut o, &a);
    end_func(&mut o);
    set(&mut o, R1, 5);
    call(&mut o, "f", &[R1, R1, R1]);
    malloc_const(&mut o, R2, 8);
    set(&mut o, &R2.deref().offset(7), 55);
    mov(&mut o, R3, &buf.offset(5));
    // the address of buf[3], through a pointer
    addr_of(&mut o, R4, &buf);
    set(&mut o, &R4.deref().offset(3), 66);
    for machine in [Machine::c(), Machine::cpu_xlen(16)] {
        let tape = machine.run(&o, b"").unwrap().tape;
        fn cell(l: &Location) -> u64 {
            match l {
                Location::Static(StaticLocation(c)) => *c,
                Location::Offset(l, k) => (cell(l) as i64 + k) as u64,
                Location::Deref(_) => unreachable!("a fixed cell"),
            }
        }
        let at = |l: &Location| tape[cell(l) as usize];
        assert_eq!((at(&a), at(&b), at(R0), at(R3), at(&buf.offset(3))), (12, 22, 5, 0, 66));
        assert!((0..40).filter(|&k| k != 3).all(|k| at(&buf.offset(k)) == 0), "only buf[3] was set");
    }
}

#[test]
#[should_panic(expected = "declared after init_globals")]
fn globals_are_declared_first() {
    let mut g = Globals::new();
    g.var("a", 1);
    init_globals(&mut vec![], 4096, &mut g);
    g.var("late", 1);
}
