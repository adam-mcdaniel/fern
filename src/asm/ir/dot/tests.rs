use super::*;
use crate::asm::ir::{lower, optimize, run, run_with};
use std::collections::HashMap;
use crate::interp::Machine;

/// `machine`, checking that lowered programs keep lowering's promise that
/// no pointer leads to the registers.
fn guard(machine: Machine) -> Machine {
    Machine { guarded: 0..48, ..machine }
}

/// Compiles `src` and checks that it prints `expected` everywhere: with the
/// IR interpreter, before and after optimizing, and lowered, under both
/// address models and on a 16-bit CPU.
fn check_runs(src: &str, input: &str, expected: &str) {
    let module = compile(src).unwrap_or_else(|e| panic!("{e}"));
    let mut optimized = module.clone();
    optimize(&mut optimized);
    for (what, m) in [("unoptimized", &module), ("optimized", &optimized)] {
        let out = run(m, input.as_bytes(), 64).unwrap_or_else(|e| panic!("{what}: {e}\n{m}"));
        assert_eq!(String::from_utf8(out).unwrap(), expected, "{what} IR\n{m}");
        let ops = lower(m).unwrap();
        for (model, machine) in [("CPU", Machine::cpu()), ("C", Machine::c()), ("16-bit CPU", Machine::cpu_xlen(16))] {
            let out = guard(machine).run(&ops, input.as_bytes()).unwrap_or_else(|e| panic!("{what}, {model}: {e}"));
            assert_eq!(String::from_utf8(out.output).unwrap(), expected, "{what}, lowered, {model}\n{m}");
        }
    }
}

/// The program's type.
fn type_of(src: &str) -> String {
    check(src).unwrap_or_else(|e| panic!("{e}")).type_string()
}

/// Checks that `src` is rejected with a message containing `message`, at
/// `line`.
fn rejects(src: &str, line: usize, message: &str) {
    match check(src) {
        Ok(c) => panic!("accepted, with type {}", c.type_string()),
        Err(e) => {
            assert!(e.message.contains(message), "wrong error: {e}");
            assert_eq!(e.line, line, "wrong line: {e}");
        }
    }
}

#[test]
fn arithmetic_and_printing() {
    check_runs(
        r#"
        println(1 + 2 * 3 - 4 / 2)
        println(-7 % 3)
        print(10 > 3 && !(2 == 3)); print(" "); println(1 >= 2 || false)
        printc(72); printc(105); println()
        print("no newline")
        "#,
        "",
        "5\n-1\ntrue false\nHi\nno newline",
    );
}

#[test]
fn functions_and_closures() {
    check_runs(
        r#"
        def fact(n: Int): Int = if (n <= 1) 1 else n * fact(n - 1)
        def compose(f: Int => Int, g: Int => Int): Int => Int = (x: Int) => f(g(x))
        def adder(k: Int) = (x: Int) => x + k
        val add3 = adder(3)
        val k = 100
        val curried = (a: Int, b: Int, c: Int) => a * k + b * 10 + c
        println(fact(7))
        println(compose(add3, (x: Int) => x * 2)(5))
        println(curried(1, 2, 3))
        val partial = curried(4)
        println(partial(5)(6))
        "#,
        "",
        "5040\n13\n123\n456\n",
    );
}

#[test]
fn mutual_recursion_in_a_group() {
    check_runs(
        r#"
        def even(n: Int): Bool = if (n == 0) true else odd(n - 1)
        def odd(n: Int): Bool = if (n == 0) false else even(n - 1)
        println(even(10)); println(odd(7)); println(even(3))
        "#,
        "",
        "true\ntrue\nfalse\n",
    );
}

#[test]
fn input() {
    check_runs(
        r#"
        def loop(total: Int): Int = {
          val n = read()
          if (n == 0) total else loop(total + n)
        }
        println(loop(0))
        def echo(): Unit = {
          val c = readc()
          if (c < 0) () else { printc(c); echo() }
        }
        echo()
        "#,
        "1 2 3 4 0\nabc",
        // reading the 0 takes the newline after it
        "10\nabc",
    );
}

#[test]
fn and_and_or_short_circuit() {
    check_runs(
        r#"
        def loud(b: Bool): Bool = { print("!"); b }
        println(false && loud(true))
        println(true || loud(true))
        println(true && loud(false))
        "#,
        "",
        "false\ntrue\n!false\n",
    );
}

#[test]
fn objects_and_width_subtyping() {
    // `a` and `b` are both in the first object, so they get different slots,
    // and a function taking `{ val b: Int }` can be passed any object with a
    // `b`, wherever its slot is
    check_runs(
        r#"
        val o = new { val a = 1; val b = 2; val c = 3 }
        val p = new { val b = 20; val d = 40 }
        def getB(x: { val b: Int }): Int = x.b
        println(getB(o) + getB(p))
        val nested = new { val inner = new { val v = 7 }; val w = 8 }
        println(nested.inner.v * nested.w)
        "#,
        "",
        "22\n56\n",
    );
}

#[test]
fn objects_refer_to_themselves() {
    check_runs(
        r#"
        val counter = new { self =>
          val start = 10
          def count(n: Int): Int = if (n == 0) 0 else 1 + self.count(n - 1)
          def fromStart(): Int = count(start)
        }
        println(counter.fromStart())
        "#,
        "",
        "10\n",
    );
}

const COUNTER: &str = r#"
    type Counter = { c =>
      type T
      def start(): c.T
      def next(n: c.T): c.T
      def show(n: c.T): Int
    }
    val ints: Counter = new {
      type T = Int
      def start(): T = 0
      def next(n: T): T = n + 1
      def show(n: T): Int = n
    }
    val evens: Counter = new {
      type T = Int
      def start(): T = 0
      def next(n: T): T = n + 2
      def show(n: T): Int = n
    }
"#;

#[test]
fn abstract_types_hide_what_they_are() {
    check_runs(
        &format!("{COUNTER}\nprintln(ints.show(ints.next(ints.next(ints.start()))))\nprintln(evens.show(evens.next(evens.start())))"),
        "",
        "2\n2\n",
    );
    // the counter's T is abstract, so an Int isn't one
    rejects(&format!("{COUNTER}\nints.show(5)"), 21, "expected ints.T, but this has type Int");
    rejects(&format!("{COUNTER}\nints.start() + 1"), 21, "expected Int, but this has type ints.T");
    // and each counter's T is its own: path-dependent types
    rejects(&format!("{COUNTER}\nints.show(evens.start())"), 21, "expected ints.T, but this has type evens.T");
}

#[test]
fn generic_lists() {
    check_runs(include_str!("../../../../examples/dot/lists.dot"), "", "55\n385\ntrue false false true false false \n");
}

#[test]
fn bounds_on_type_members() {
    // an upper bound lets a T be used as an Int, but not an Int as a T
    let src = r#"
        val o: { type T <: Int; val v: T; def f(x: T): Int } = new { type T = Int; val v: T = 4; def f(x: T): Int = x * 10 }
    "#;
    check_runs(&format!("{src}\nprintln(o.v + 1)\nprintln(o.f(o.v))"), "", "5\n40\n");
    rejects(&format!("{src}\no.f(4)"), 4, "expected o.T, but this has type Int");
    // a lower bound is the other way around
    let src = r#"
        val o: { type T >: Int; val v: T; def f(x: T): Int } = new { type T = Int; val v: T = 4; def f(x: T): Int = x * 10 }
    "#;
    check_runs(&format!("{src}\nprintln(o.f(4))"), "", "40\n");
    rejects(&format!("{src}\no.v + 1"), 4, "expected Int, but this has type o.T");
}

#[test]
fn dependent_functions() {
    // the result's type depends on the argument
    let src = r#"
        def get(o: { type T; val v: T }): o.T = o.v
        val a = new { type T = Int; val v: T = 41 }
        val b = new { type T = Bool; val v: T = true }
    "#;
    check_runs(&format!("{src}\nprintln(get(a) + 1)\nprintln(get(b) && true)"), "", "42\ntrue\n");
    rejects(&format!("{src}\nget(b) + 1"), 6, "expected Int, but this has type b.T");
    assert_eq!(type_of("(o: { type T; val v: T }) => o.v"), "(o: { type T; val v: T }) => o.T");
    assert_eq!(type_of("(o: { s => type T; val v: s.T }) => o.v"), "(o: { s => type T; val v: s.T }) => o.T");
}

#[test]
fn types_are_avoided_when_their_paths_go_out_of_scope() {
    // the block's value has type o.T, which means nothing outside it, so it
    // becomes T's bound
    assert_eq!(type_of("{ val o = new { type T = Int; val v: T = 3 }; o.v }"), "Int");
    assert_eq!(type_of("new { type T = Int; val v: T = 3 }.v"), "Int");
    // an abstract type with no bounds can only become Top
    assert_eq!(type_of("{ val o: { type T; val v: T } = new { type T = Int; val v: T = 3 }; o.v }"), "Top");
    // in a parameter's type it becomes the lower bound
    assert_eq!(
        type_of("{ val o: { type T >: Int <: Int } = new { type T = Int }; (x: o.T) => x }"),
        "Int => Int"
    );
    // an alias for a type being avoided keeps both its bounds
    assert_eq!(
        type_of("{ val o: { type T >: Int } = new { type T = Int }; new { type U = o.T } }"),
        "{ type U >: Int }"
    );
    rejects("{ val o: { type T; val v: T } = new { type T = Int; val v: T = 3 }; o.v } + 1", 1, "expected Int, but this has type o.T");
}

#[test]
fn recursive_types() {
    // a type that refers to itself through its self variable
    let src = r#"
        type Stream = { s => val head: Int; def tail(): Stream }
        def from(n: Int): Stream = new { val head = n; def tail(): Stream = from(n + 1) }
        def take(s: Stream, n: Int): Unit = if (n == 0) () else { print(s.head); print(" "); take(s.tail(), n - 1) }
        take(from(5), 4)
    "#;
    check_runs(src, "", "5 6 7 8 ");
    // a family of types that depend on each other: an animal eats its food
    let src = r#"
        type Animal = { a => type Food; def eat(f: a.Food): Int }
        val cow = new { type Food = Int; def eat(f: Food): Int = f * 2 }
        val owl = new { type Food = Bool; def eat(f: Food): Int = if (f) 1 else 0 }
        def feed(x: Animal, f: x.Food): Int = x.eat(f)
    "#;
    check_runs(&format!("{src}\nprintln(feed(cow, 21))\nprintln(feed(owl, true))"), "", "42\n1\n");
    rejects(&format!("{src}\nfeed(owl, 21)"), 7, "expected owl.Food, but this has type Int");
}

#[test]
fn self_types() {
    check_runs(
        r#"
        type Point = { val x: Int; val y: Int }
        val p = new { self: Point => val x = 3; val y = self.x * 2 }
        println(p.y)
        "#,
        "",
        "6\n",
    );
    rejects("new { self: { val x: Int } => val x = true }", 1, "isn't its self type");
}

#[test]
fn programs_that_are_rejected() {
    rejects("x + 1", 1, "`x` isn't defined");
    rejects("val x = 1\n\nx + true", 3, "expected Int, but this has type Bool");
    rejects("if (1) 2 else 3", 1, "expected Bool");
    rejects("{ if (true) 1 else false } + 1", 1, "expected Int, but this has type Bool");
    rejects("new { val a = 1; val a = 2 }", 1, "`a` is defined twice");
    rejects("def f(n: Int) = new { val next = f(n) }", 1, "can't work out the type of `f`");
    rejects("val f = x => x", 1, "can't tell what type `x` is");
    rejects("1 == true", 1, "can't compare Int with Bool");
    rejects("new { val a = 1 } == 1", 1, "can't compare");
    rejects("\"a\" - 1", 1, "expected Int, but this has type String");
    rejects("\"a\" + new { val a = 1 }", 1, "can't add { val a: Int } to a String");
    rejects("error(1)", 1, "expected String");
    rejects("new { val a = 1 }.b", 1, "there's no `b` in { val a: Int }");
    rejects("3(4)", 1, "this isn't a function");
    rejects("val f = (x: Int) => x\nf(true)", 2, "expected Int, but this has type Bool");
    rejects("(x: { type T }) => (y: x.U) => y", 1, "`x` has no type member `U`");
    rejects("val x: Foo = 3", 1, "no type called `Foo`");
    rejects("print(new { val a = 1 })", 1, "can only print an Int, a Bool or a String");
    rejects("val x = (1 + 2", 1, "expected `)`");
    rejects("val = 3", 1, "expected a name");
    rejects("\n  1 $ 2", 2, "unexpected character");
    rejects("1 /* never closed", 1, "unterminated comment");
}

#[test]
fn error_positions() {
    let Err(e) = check("val a = 1\nval b = a +\n  true") else { panic!("accepted") };
    assert_eq!((e.line, e.col), (3, 3), "{e}");
    assert_eq!(e.to_string(), "3:3: expected Int, but this has type Bool");
}

#[test]
fn checking_gives_up_on_runaway_types() {
    // T's only bound is itself, so asking whether it's an Int never ends
    rejects("def f(x: { l => type T <: l.T }, y: x.T): Int = y", 1, "expected Int, but this has type x.T");
}

#[test]
fn syntax() {
    check_runs(
        r#"
        // statements continue over lines after an operator, and before
        // `.` or `else` /* and comments can be
        // like this */
        val o = new { val inner = new { val v = 5 } }
        val v = o
          .inner
          .v
        val w =
          v *
          2
        if (w == 10)
          println("ten")
        else
          println("not ten")
        { val a = 1; val b = 2; println(a + b) }
        val u: Unit = () /* a comment */ ; println(/* inside */ 4)
        "#,
        "",
        "ten\n3\n4\n",
    );
}

#[test]
fn subtyping() {
    let accepts = |src: &str| {
        check(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    };
    let refuses = |src: &str| assert!(check(src).is_err(), "{src} was accepted");
    // records: more fields is a subtype
    accepts("(new { val a = 1; val b = true } : { val a: Int })");
    refuses("(new { val a = 1 } : { val a: Int; val b: Bool })");
    accepts("(new { val a = 1; val b = 2 } : { val a: Int } & { val b: Int })");
    accepts("(new { val a = 1 } : Top)");
    // functions: contravariant in the parameter, covariant in the result
    accepts("((x: { val a: Int }) => x.a : { val a: Int; val b: Bool } => Int)");
    refuses("((x: { val a: Int; val b: Bool }) => x.a : { val a: Int } => Int)");
    accepts("((x: Int) => new { val a = x; val b = x } : Int => { val a: Int })");
    refuses("((x: Int) => new { val a = x } : Int => { val a: Int; val b: Int })");
    // the same, for functions that aren't lambdas where they're checked
    accepts("val f = (x: { val a: Int }) => x.a\n(f : { val a: Int; val b: Bool } => Int)");
    refuses("val f = (x: { val a: Int; val b: Bool }) => x.a\n(f : { val a: Int } => Int)");
    // a field in both halves of an intersection has both types
    accepts("(x: { val a: { val b: Int } } & { val a: { val c: Int } }) => x.a.b + x.a.c");
    // type members: their bounds can only get wider
    accepts("(new { type T = Int } : { type T <: Int })");
    accepts("(new { type T = Int } : { type T >: Int })");
    accepts("(new { type T = Int } : { type T })");
    refuses("(new { type T = Int } : { type T <: Bool })");
    refuses("(new { type T = Int } : { type T >: Bool })");
    accepts("((x: { type T <: Int }) => 1 : { type T = Int } => Int)");
    refuses("((x: { type T = Int }) => 1 : { type T <: Int } => Int)");
    // members through a type member's bounds
    accepts("(x: { type T <: { val a: Int }; val v: T }) => x.v.a + 1");
    refuses("(x: { type T >: { val a: Int }; val v: T }) => x.v.a + 1");
    // a field or type member declared in both halves of an intersection
    accepts("(x: { val a: { val b: Int } } & { val a: { val c: Int } }) => (x : { val a: { val b: Int } & { val c: Int } })");
    accepts("(x: { type T <: { val a: Int } } & { type T <: { val b: Int } }) => (x : { type T <: { val a: Int; val b: Int } })");
    refuses("(x: { type T <: { val a: Int } } & { type U <: { val b: Int } }) => (x : { type T <: { val a: Int; val b: Int } })");
    // recursive types, compared at the same self
    accepts("(new { s => type T = Int; val v: s.T = 1 } : { r => type T; val v: r.T })");
    accepts("(new { s => type T = Int; val v: Int = 1 } : { r => type T; val v: r.T })");
    refuses("(new { s => type T = Int; val v: Bool = true } : { r => type T; val v: r.T })");
}


/// Compiles and optimizes `src`, and checks that it prints `expected`
/// lowered on every machine. For programs that only fit once optimized: ones
/// whose loops are tail calls, which only become loops then, or which need
/// the garbage collector, which the IR interpreter doesn't have.
fn check_optimized(src: &str, input: &str, expected: &str) {
    let mut module = compile(src).unwrap_or_else(|e| panic!("{e}"));
    optimize(&mut module);
    let ops = lower(&module).unwrap();
    for (model, machine) in [("CPU", Machine::cpu()), ("C", Machine::c()), ("16-bit CPU", Machine::cpu_xlen(16))] {
        let out = guard(machine).run(&ops, input.as_bytes()).unwrap_or_else(|e| panic!("{model}: {e}"));
        assert_eq!(String::from_utf8(out.output).unwrap(), expected, "{model}\n{module}");
    }
}

#[test]
fn joins() {
    assert_eq!(type_of("if (true) 1 else false"), "Top");
    assert_eq!(type_of("if (true) new { val a = 1; val b = 2 } else new { val a = 3; val c = true }"), "{ val a: Int }");
    assert_eq!(
        type_of("if (true) new { val a = new { val x = 1; val y = 2 } } else new { val a = new { val x = 2 } }"),
        "{ val a: { val x: Int } }"
    );
    // a type member's lower bounds meet, and its upper bounds join
    assert_eq!(type_of("if (true) new { type T = Int } else new { type T = Bool }"), "{ type T >: Int & Bool }");
    // functions: the parameters meet, the results join
    assert_eq!(
        type_of("if (true) (x: { val a: Int }) => new { val r = 1; val s = 2 } else (x: { val b: Int }) => new { val r = 3 }"),
        "({ val a: Int; val b: Int }) => { val r: Int }"
    );
    check_runs("val o = if (read() > 0) new { val a = 1; val b = 2 } else new { val b = 3; val a = 4 }\nprintln(o.a)", "1", "1\n");
}

#[test]
fn recursive_functions_without_result_types() {
    check_runs(
        r#"
        def fact(n: Int) = if (n <= 1) 1 else n * fact(n - 1)
        def even(n: Int) = if (n == 0) true else odd(n - 1)
        def odd(n: Int) = if (n == 0) false else even(n - 1)
        def countdown(n: Int) = if (n == 0) new { val done = true } else countdown(n - 1)
        println(fact(7)); println(even(10)); println(odd(10)); println(countdown(3).done)
        "#,
        "",
        "5040\ntrue\nfalse\ntrue\n",
    );
    assert_eq!(type_of("def f(n: Int) = f(n)\nf"), "Int => Bot");
    assert_eq!(type_of("def f(n: Int) = if (n == 0) 0 else f(n - 1) + 1\nf"), "Int => Int");
}

#[test]
fn lambda_parameters_from_the_type_expected() {
    check_runs(
        r#"
        def twice(f: Int => Int, x: Int): Int = f(f(x))
        def compose(f: Int => Int, g: Int => Int): Int => Int = x => f(g(x))
        val inc: Int => Int = x => x + 1
        val add: Int => Int => Int = (a, b) => a + b
        println(twice(x => x * 3, 7))
        println(compose(inc, x => x * 10)(4))
        println(add(2)(3))
        println(((a, b) => a * b : (Int, Int) => Int)(6, 7))
        "#,
        "",
        "63\n41\n5\n42\n",
    );
    check_runs(&format!("{}\nprintln(lists.map(Ints, Ints, x => x * 2, range(0, 4)).tail().head())", LISTS_PRELUDE), "", "2\n");
}

const LISTS_PRELUDE: &str = r#"
val lists = new { m =>
  type List = { l => type A; val isEmpty: Bool; def head(): l.A; def tail(): m.List & { type A <: l.A } }
  def nil(t: { type T }): m.List & { type A = t.T } = new { l =>
    type A = t.T; val isEmpty = true; def head(): A = error("head of an empty list"); def tail(): m.List & { type A <: l.A } = error("tail of an empty list") }
  def cons(t: { type T }, x: t.T, xs: m.List & { type A <: t.T }): m.List & { type A = t.T } = new { l =>
    type A = t.T; val isEmpty = false; def head(): A = x; def tail(): m.List & { type A <: l.A } = xs }
  def map(s: { type T }, t: { type T }, f: s.T => t.T, xs: m.List & { type A <: s.T }): m.List & { type A = t.T } =
    if (xs.isEmpty) nil(t) else cons(t, f(xs.head()), map(s, t, f, xs.tail()))
}
val Ints = new { type T = Int }
def range(lo: Int, hi: Int): lists.List & { type A = Int } = if (lo >= hi) lists.nil(Ints) else lists.cons(Ints, lo, range(lo + 1, hi))
"#;

#[test]
fn values_are_computed_in_order() {
    rejects("new { val a = b; val b = 1 }", 1, "`a` uses `b`, which comes after it");
    rejects("new { val a = a }", 1, "`a` uses itself");
    rejects("new { val a = f(1); def f(x: Int): Int = b; val b = 2 }", 1, "`a` uses `f`, which comes after it");
    rejects("new { def f(x: Int): Int = b; val a = f(1); val b = 2 }", 1, "`a` uses `b`, which comes after it");
    rejects("new { s => val a = s }", 1, "`a` uses `s` before it's built");
    rejects("def g(o: Top): Int = 1\nnew { s => def f(x: Int): Int = g(s); val a = f(1) }", 2, "`a` uses `f`, which uses `s`");
    check_runs(
        r#"
        val o = new { s =>
          val a = 1
          val b = a + 1
          def f(x: Int): Int = x + b // only uses what comes before c
          val c = f(10)
          def g(x: Int): Int = x + d // which can come after, since it's never called while building
          val d = 10
        }
        println(o.b); println(o.c); println(o.g(1))
        "#,
        "",
        "2\n12\n11\n",
    );
}

#[test]
fn strings() {
    check_runs(
        r#"
        val s = "hello"
        val t = s + ", " + "world"
        println(t)
        println(t.length)
        printc(t.charAt(1)); println()
        println(t.substring(7, 12))
        println("n = " + 42 + ", b = " + true + ", neg = " + -7 + ", zero = " + 0)
        println(s == "hello"); println(s != "hello"); println(s == "hell")
        val first = t.substring(0)
        println(first(5))
        val at = s.charAt
        println(at(4))
        def shout(s: String): String = s + "!"
        println(shout("hi"))
        println("" + (-32768) + " " + 32767)
        "#,
        "",
        "hello, world\n12\ne\nworld\nn = 42, b = true, neg = -7, zero = 0\ntrue\nfalse\nfalse\nhello\n111\nhi!\n-32768 32767\n",
    );
    check_runs(
        r#"
        def lines(n: Int): Int = {
          val line = readLine()
          if (line == "") n else { println(line.length + ": " + line); lines(n + 1) }
        }
        println(lines(0) + " lines")
        "#,
        "one\nthree\nthe longest line of them all\n\n",
        "3: one\n5: three\n28: the longest line of them all\n3 lines\n",
    );
    check_runs(r#"println("abc".charAt(3))"#, "", "error: string index out of range\n");
    check_runs(r#"print("abc".substring(2, 1))"#, "", "error: string index out of range\n");
}

#[test]
fn errors_stop_the_program() {
    check_runs(
        r#"
        def check(n: Int): Int = if (n > 3) error("too big: " + n) else n
        println(check(1))
        println(check(5))
        println("never printed")
        "#,
        "",
        "1\nerror: too big: 5\n",
    );
    check_runs("println(1)\nval z = read()\nprintln(10 / z)\nprintln(2)", "0", "1\nerror: division by zero\n");
    check_runs("println(10 % read())", "3", "1\n");
    assert_eq!(type_of(r#"error("no")"#), "Bot");
}

#[test]
fn identity() {
    check_runs(
        r#"
        val o = new { val a = 1 }
        val p = new { val a = 1 }
        val f = (x: Int) => x
        println(o == o); println(o == p); println(o != p); println(f == f)
        println(new { type T = Int } == new { type T = Int })
        "#,
        "",
        "true\nfalse\ntrue\ntrue\nfalse\n",
    );
}

#[test]
fn garbage_is_collected() {
    // each round builds a list and throws it away: far more than fits in
    // the tape, unless it's freed; and the loops are tail calls, so they
    // only fit on the stack once they're loops
    let src = format!(
        "{LISTS_PRELUDE}\n{}",
        r#"
        def sum(xs: lists.List & { type A <: Int }, acc: Int): Int = if (xs.isEmpty) acc else sum(xs.tail(), acc + xs.head())
        def rounds(n: Int, total: Int): Int = if (n == 0) total else rounds(n - 1, total + sum(range(0, 10), 0) % 7)
        val keep = range(0, 20)
        println(rounds(300, 0))
        println(sum(keep, 0))
        def words(n: Int, s: String): String = if (n == 0) s else words(n - 1, (s + "ab").substring(2, s.length + 2))
        println(words(500, "xyz"))
        "#
    );
    check_optimized(&src, "", "900\n190\nbab\n");
}

#[test]
fn calls_to_known_functions_are_direct() {
    let mut m = compile(
        r#"
        def loop(i: Int, total: Int): Int = if (i == 0) total else loop(i - 1, total + i)
        val inc = (x: Int) => x + 1
        println(inc(loop(read(), 0)))
        "#,
    )
    .unwrap();
    optimize(&mut m);
    let ir = m.to_string();
    assert!(!ir.contains("call *"), "{ir}");
    // the tail call became a loop, so a long count needs no stack
    check_optimized("def loop(i: Int, total: Int): Int = if (i == 0) total else loop(i - 1, total + 1)\nprintln(loop(read(), 0))", "20000", "20000\n");
}

#[test]
fn stack_overflow_stops_the_program() {
    // n is needed after each call, so every level keeps it on the stack
    check_optimized(
        "def depth(n: Int): Int = if (n == 0) 0 else { val r = depth(n - 1); if (r < n) r + 1 else r }\nprintln(depth(read()))",
        "10",
        "10\n",
    );
    check_optimized(
        "def depth(n: Int): Int = if (n == 0) 0 else { val r = depth(n - 1); if (r < n) r + 1 else r }\nprintln(depth(read()))",
        "20000",
        "stack overflow\n",
    );
}

#[test]
fn types_print_like_the_source() {
    assert_eq!(type_of("(o: { type T; val v: T }) => o.v"), "(o: { type T; val v: T }) => o.T");
    // a record inside one that refers to the outer one's members names it
    assert_eq!(
        type_of("(o: { type T; val inner: { s => type U; val v: T; val w: s.U } }) => o"),
        "(o: { this => type T; val inner: { s => type U; val v: this.T; val w: s.U } }) => { type T; val inner: { s => type U; val v: o.T; val w: s.U } }"
    );
    assert_eq!(type_of("\"text\""), "String");
}

/// Like `check_runs`, compiling with `compiler`.
fn check_runs_with(compiler: &Compiler, src: &str, input: &str, expected: &str) {
    let module = compiler.compile(src).unwrap_or_else(|e| panic!("{e}"));
    let mut optimized = module.clone();
    optimize(&mut optimized);
    for (what, m) in [("unoptimized", &module), ("optimized", &optimized)] {
        let out = run(m, input.as_bytes(), 64).unwrap_or_else(|e| panic!("{what}: {e}"));
        assert_eq!(String::from_utf8(out).unwrap(), expected, "{what} IR");
        let ops = lower(m).unwrap();
        for (model, machine) in [("CPU", Machine::cpu()), ("C", Machine::c()), ("16-bit CPU", Machine::cpu_xlen(16))] {
            let out = guard(machine).run(&ops, input.as_bytes()).unwrap_or_else(|e| panic!("{what}, {model}: {e}"));
            assert_eq!(String::from_utf8(out.output).unwrap(), expected, "{what}, lowered, {model}");
        }
    }
}

fn tour_compiler() -> Compiler {
    let mut c = Compiler::new();
    c.module("shapes", include_str!("../../../../examples/dot/tour/shapes.dot"));
    c
}

#[test]
fn tour_of_modules() {
    let src = include_str!("../../../../examples/dot/tour/modules.dot");
    let expected = "#2\n42\n3 o'clock\n3 o'clock\n(7 o'clock, 2 o'clock)\n#2\na square of area 9\na rectangle of area 10\n60\n3\n";
    check_runs_with(&tour_compiler(), src, "1", expected);
    // with the other module chosen
    let expected = "#2\n42\n3 o'clock\nup 3\n(7 o'clock, 2 o'clock)\n#2\na square of area 9\na rectangle of area 10\n60\n3\n";
    check_runs_with(&tour_compiler(), src, "0", expected);
}

#[test]
fn tour_of_generics() {
    check_runs(
        include_str!("../../../../examples/dot/tour/generics.dot"),
        "",
        "4\nleft\nhello, dot\n21\n3\n300\ntwin\n3 6 9 12 15 18\n",
    );
}

#[test]
fn tour_of_objects_data_and_state() {
    check_runs(
        include_str!("../../../../examples/dot/tour/objects.dot"),
        "",
        "7\nred (1, 2)\n10 11 12 13 \ncow eats 3 grass\nowl eats 2 mice\n10\n104\ntrue\nfalse\n",
    );
    check_runs(
        include_str!("../../../../examples/dot/tour/data.dot"),
        "",
        "(2 + 3) * -(4 + 1) = -25\n8\n5 and 3 more\nnothing\n42\n",
    );
    check_runs(include_str!("../../../../examples/dot/tour/state.dot"), "", "30\n3\n120\n120\nabc\n0 1 4 9 16 25\n");
}

#[test]
fn modules_are_sealed_by_their_signatures() {
    let src = include_str!("../../../../examples/dot/tour/modules.dot");
    let sealed = format!("{src}\nClock.next(41)");
    let Err(e) = tour_compiler().check(&sealed) else { panic!("accepted") };
    assert!(e.message.contains("expected Clock.T, but this has type Int"), "{e}");
    // two sealed modules' abstract types are different types
    let mixed = format!("{src}\nClock.show(Up.zero())");
    let Err(e) = tour_compiler().check(&mixed) else { panic!("accepted") };
    assert!(e.message.contains("expected Clock.T, but this has type Up.T"), "{e}");
    // an unsealed module's types are what they are
    check_runs("module M { type T = Int; val x: T = 4 }\nprintln(M.x + 1)", "", "5\n");
}

#[test]
fn generics_are_type_members() {
    // a type parameter is an object with a type member, so the sugar and the
    // DOT it stands for are interchangeable
    assert_eq!(type_of("def id[A](x: A): A = x\nid"), "(A: { type T }) => A => A");
    check_runs(
        r#"
        def id[A](x: A): A = x
        def id2(A: { type T }, x: A.T): A.T = x
        println(id2[Int](1) + id[Int](2) + id(new { type T = Int }, 3) + id2(4))
        type Box[+A] = { def get(): A }
        val b: Box { type A <: Int } = new Box[Int] { def get(): Int = 5 }
        val c: Box[Int] = b
        println(c.get())
        "#,
        "",
        "10\n5\n",
    );
    rejects("def f[A <: Int](x: A): A = x\nf(true)", 2, "Bool doesn't fit `A`");
    rejects("type Box[+A] = { def get(): A }\nval b: Box[Int, Int] = 1", 2, "takes 1 type parameters, not 2");
    rejects("type Plain = { val a: Int }\nval b: Plain[Int] = 1", 2, "doesn't take type parameters");
    // variance is which bound the refinement gets
    rejects("type Cell[A] = { def get(): A }\nval c: Cell[Top] = new Cell[Int] { def get(): Int = 1 }", 2, "expected");
    check_runs("type Sink[-A] = { def put(x: A): Int }\nval s: Sink[Int] = new Sink[Top] { def put(x: Top): Int = 7 }\nprintln(s.put(1))", "", "7\n");
}

#[test]
fn type_arguments_are_worked_out() {
    check_runs(
        r#"
        import std.list._
        // from the arguments, from lambdas' results, and through nested calls
        val xs = cons(1, cons(2, cons(3, cons(4, cons(5, cons(6, cons(7, cons(8, cons(9, cons(10, nil()))))))))))
        println(sum(map(xs, x => x * 2)))
        println(mkString(map(xs, x => if (x % 2 == 0) "e" else "o"), ""))
        println(length(append(xs, reverse(xs))))
        "#,
        "",
        "110\noeoeoeoeoe\n20\n",
    );
}

#[test]
fn vars_and_loops() {
    check_runs(
        r#"
        var n = 7
        var fact = 1
        while (n > 1) { fact = fact * n; n = n - 1 }
        println(fact % 1000)
        val o = new { var count = 0 }
        o.count = o.count + 5
        println(o.count)
        "#,
        "",
        "40\n5\n",
    );
    rejects("val o = new { val a = 1 }\no.a = 2", 2, "`a` is a val, so it can't be assigned to");
    rejects("val x = 1\nx = 2", 2, "only a `var` or a field can be assigned to");
    rejects("var x = 1\nx = true", 2, "expected Int, but this has type Bool");
    rejects("val box = new { var inner = new { type T = Int } }\nval y: box.inner.T = 3", 2, "it goes through a var");
    rejects("(new { var a = 1 } : { var a: Top })", 1, "expected");
    check_runs("val v = (new { var a = 1 } : { val a: Top })\nprintln(1)", "", "1\n");
}

#[test]
fn modules_from_files() {
    let mut c = Compiler::new();
    c.module("geometry.points", "type P = { val x: Int }\ndef origin(): P = new { val x = 0 }");
    c.module("uses", "import geometry.points._\ndef shifted(n: Int): P = new { val x = origin().x + n }");
    check_runs_with(&c, "import uses\nimport geometry.points\nprintln(uses.shifted(7).x + points.origin().x)", "", "7\n");
    // errors in a module say which file they're in
    c.module("broken", "def f(x: Int): Int = x\nval y: Bool = f(1)");
    let Err(e) = c.check("import broken\nprintln(1)") else { panic!("accepted") };
    assert_eq!((e.file.as_str(), e.line), ("broken.dot", 2), "{e}");
    c.module("a", "import b\nval x = 1");
    c.module("b", "import a\nval y = 2");
    let Err(e) = c.check("import a") else { panic!("accepted") };
    assert!(e.message.contains("imports itself"), "{e}");
    let Err(e) = c.check("import nowhere") else { panic!("accepted") };
    assert!(e.message.contains("there's no module called `nowhere`"), "{e}");
}

#[test]
fn external_and_builtin_functions() {
    use crate::interp::HostFn;
    // an external function is called as the VM calls one: its arguments
    // from the pointer on, its result left in acc
    let src = "extern def triple(x: Int): Int\nextern def add3(a: Int, b: Int, c: Int): Int\nprintln(triple(14))\nval t = triple\nprintln(add3(t(2), 1, 10))";
    let hosts: HashMap<String, HostFn> = [
        (
            "triple".to_string(),
            HostFn::new(|c| {
                c.acc = 3 * c.arg(0)?;
                Ok(())
            }),
        ),
        (
            "add3".to_string(),
            HostFn::new(|c| {
                c.acc = c.arg(0)? + c.arg(1)? + c.arg(2)?;
                Ok(())
            }),
        ),
    ]
    .into();
    let module = Compiler::new().compile(src).unwrap_or_else(|e| panic!("{e}"));
    let mut optimized = module.clone();
    optimize(&mut optimized);
    for m in [&module, &optimized] {
        assert_eq!(String::from_utf8(run_with(m, b"", 64, &hosts).unwrap()).unwrap(), "42\n17\n");
        let ops = lower(m).unwrap();
        for machine in [Machine::cpu(), Machine::c(), Machine::cpu_xlen(16)] {
            let machine = hosts.iter().fold(guard(machine), |mm, (n, h)| mm.host(n, h.clone()));
            assert_eq!(String::from_utf8(machine.run(&ops, b"").unwrap().output).unwrap(), "42\n17\n");
        }
    }
    let c = Compiler::new();
    for (src, message) in [
        ("extern def f_x(x: Int): Int\nf_x(1)", "can't be an external function"),
        ("extern def main(x: Int): Int\nmain(1)", "can't be an external function"),
        ("extern def ten(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int, h: Int, i: Int, j: Int): Int\n0", "at most 9 parameters"),
        ("builtin def missing(x: Int): Int\nmissing(1)", "no built-in function called `missing`"),
        ("builtin def mem_new(n: Int, m: Int): Int\nmem_new(1, 2)", "takes 1 parameters, not 2"),
    ] {
        let Err(e) = c.check(src) else { panic!("accepted {src}") };
        assert!(e.message.contains(message), "{src}: {e}");
    }
}

#[test]
fn the_standard_library() {
    check_runs_with(
        &Compiler::new(),
        r#"
        import std.list._
        import std.option._
        import std.text._
        import std.array._
        import std.map as maps
        println(upper("dot") + " " + padLeft("7", 3))
        println(mkString(split("a,b,c", 44), "+"))
        println(getOrElse(toInt("-45"), 0) + getOrElse(toInt("x"), 100))
        val a = fromList(range(0, 4), 0)
        a.set(2, 20)
        println(sum(toList(a)))
        val Ints = maps.sorted(maps.ints)
        val m = Ints.put(Ints.put(Ints.empty(), 2, "b"), 1, "a")
        println(mkString(map(Ints.keys(m), (k: Int) => "" + k), ","))
        println(getOrElse(Ints.get(m, 1), "?"))
        "#,
        "",
        "DOT   7\na+b+c\n55\n24\n1,2\na\n",
    );
}

#[test]
fn calling_c() {
    use crate::interp::HostFn;
    use std::cell::RefCell;
    use std::rc::Rc;
    let src = include_str!("../../../../examples/dot/ffi/io.dot");
    let module = Compiler::new().compile(src).unwrap_or_else(|e| panic!("{e}"));
    let want = "wrote /tmp/dot-io-demo.txt\nread 29 characters\n> FIRST LINE\n> SECOND LINE\n> THIRD\n3 lines\nDOT_DEMO is set\n";
    // the C functions, as Rust host functions over pretend files
    let files: Rc<RefCell<HashMap<String, String>>> = Rc::default();
    let (w, r) = (files.clone(), files.clone());
    let hosts: HashMap<String, HostFn> = [
        (
            "write_file".to_string(),
            HostFn::new(move |c| {
                let (path, text) = (c.string(c.arg(0)?)?, c.string(c.arg(1)?)?);
                w.borrow_mut().insert(path, text);
                c.acc = 1;
                Ok(())
            }),
        ),
        (
            "read_file".to_string(),
            HostFn::new(move |c| {
                let path = c.string(c.arg(0)?)?;
                let text = r.borrow().get(&path).cloned();
                c.acc = match text {
                    Some(text) => c.fill(c.arg(1)?, c.arg(2)?, text.as_bytes())?,
                    None => -1,
                };
                Ok(())
            }),
        ),
        (
            "env_var".to_string(),
            HostFn::new(|c| {
                c.acc = c.fill(c.arg(1)?, c.arg(2)?, b"set")?;
                Ok(())
            }),
        ),
    ]
    .into();
    let mut optimized = module.clone();
    optimize(&mut optimized);
    for m in [&module, &optimized] {
        files.borrow_mut().clear();
        assert_eq!(String::from_utf8(run_with(m, b"", 64, &hosts).unwrap()).unwrap(), want);
        let ops = crate::asm::ir::lower_with(m, &crate::asm::ir::Options { cells: 20_000, ..Default::default() }).unwrap();
        for machine in [Machine::cpu(), Machine::c()] {
            files.borrow_mut().clear();
            let machine = hosts.iter().fold(guard(machine), |mm, (n, h)| mm.host(n, h.clone()));
            assert_eq!(String::from_utf8(machine.run(&ops, b"").unwrap().output).unwrap(), want);
        }
    }
}

#[test]
fn c_functions_written_with_the_macros() {
    // dot.h's `DOT_EXTERN` with each kind of parameter and result, and
    // bf.h's `BF_FUNCTION` for one that reads its argument's cell itself,
    // built natively through the C backend and through LLVM
    let src = r#"
        extern def answer(): Int
        extern def shout(s: String): Unit
        extern def is_even(n: Int): Bool
        extern def upper(c: Int): Int
        extern def sum9(a: Int, b: Int, c: Int, d: Int, e: Int, f: Int, g: Int, h: Int, i: Int): Int
        extern def second(s: String): Int
        extern def putint(x: Int): Unit
        println(answer())
        shout("hey")
        println(if (is_even(10) && !is_even(7)) "even" else "odd")
        printc(upper(97))
        println(sum9(1, 2, 3, 4, 5, 6, 7, 8, 9))
        println(second("A!"))
        putint(-12)
        println("")
    "#;
    let c = r#"
        #include <stdio.h>
        #include "dot.h"
        DOT_EXTERN(Int, answer) { return 42; }
        DOT_EXTERN(Unit, shout, (String, s)) { printf("%s!\n", s); }
        DOT_EXTERN(Bool, is_even, (Int, n)) { return n % 2 == 0; }
        DOT_EXTERN(Char, upper, (Char, c)) { return c >= 'a' && c <= 'z' ? c - 32 : c; }
        DOT_EXTERN(Int, sum9, (Int, a), (Int, b), (Int, c), (Int, d), (Int, e), (Int, f), (Int, g), (Int, h), (Int, i)) {
            return a + b + c + d + e + f + g + h + i;
        }
        // a string's cells: its length, then its characters
        DOT_EXTERN(Int, second, (Cells, cells)) { return cells[1]; }
        BF_FUNCTION(putint) { printf("%lld", (long long)BF_CELL(0)); }
    "#;
    let want = "42\nhey!\neven\nA45\n65\n-12\n";
    let Some(clang) = ["/opt/homebrew/opt/llvm/bin/clang", "clang"]
        .into_iter()
        .find(|c| std::process::Command::new(c).arg("--version").output().is_ok_and(|o| o.status.success()))
    else {
        return eprintln!("skipped: no clang");
    };
    let mut module = Compiler::new().compile(src).unwrap_or_else(|e| panic!("{e}"));
    optimize(&mut module);
    let dir = std::env::temp_dir().join(format!("bf-macros-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.c"), c).unwrap();
    std::fs::write(dir.join("dot.h"), C_HEADER).unwrap();
    std::fs::write(dir.join("bf.h"), crate::asm::C_HEADER).unwrap();
    std::fs::write(dir.join("runtime.c"), crate::asm::ir::llvm::RUNTIME).unwrap();
    let ops = crate::asm::ir::lower_with(&module, &crate::asm::ir::Options { cells: 100_000, ..Default::default() }).unwrap();
    for (name, file, code) in [("via_c", "p.c", crate::compile(&ops)), ("via_llvm", "p.ll", crate::asm::ir::llvm::emit(&module).unwrap())] {
        std::fs::write(dir.join(file), &code).unwrap();
        let mut cmd = std::process::Command::new(clang);
        cmd.args(["-O2", "-fwrapv", "-w", "-I"]).arg(&dir).arg("-o").arg(dir.join(name)).arg(dir.join(file)).arg(dir.join("lib.c"));
        if name == "via_llvm" {
            cmd.arg(dir.join("runtime.c"));
        }
        let built = cmd.output().unwrap();
        assert!(built.status.success(), "{name}: {}", String::from_utf8_lossy(&built.stderr));
        let out = std::process::Command::new(dir.join(name)).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&out.stdout), want, "{name}");
    }
}
