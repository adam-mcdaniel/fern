# fern

A language with Rust's syntax and an ML's type system, compiled to the VM
through `bf::ir`. It's an example of a whole compiler, organized to be
read: each stage is a file, and each file starts by explaining itself.

```sh
cargo run --release -p fern -- effects.fern                # effects.c, and the binary ./effects
cargo run --release -p fern -- effects.fern --release      # optimized
cargo run --release -p fern -- effects.fern --run          # and run it
cargo run --release -p fern -- game.fern -- screen.c -lSDL2   # C to link, after --
cargo run --release -p fern -- effects.fern --emit ops     # the VM's ops (for `bf`)
cargo run --release -p fern -- effects.fern --interpret    # run on the VM's interpreter
cargo run --release -p fern -- --test                         # every sample, both ways
cargo run --release -p fern -- --help                         # everything else
```

fern compiles to native code: it writes the program as C (`NAME.c`) and
has the C compiler (`cc`, or `$CC`) make the binary (`NAME`: the file's
name, or `-o NAME`). Anything after `--` goes to the C compiler: the C of
`extern fn`s (with `bf.h` on the include path), libraries. A program can
name its own C in `// links: FILE.c` lines (relative to its file), and
fern links that in too. Like Cargo, it
compiles in **debug** mode unless told `--release`:

| | debug (the default) | `--release` |
|---|---|---|
| the IR's optimizer | skipped | everything |
| the C compiler | `-O2` | `-O3` |
| building `game/nightshift.fern` (big) | about 18 s | about 19 s |
| a frame of it | about 1.6 ms | about 1.1 ms |

Release takes about as long to build as debug, for a big program: the
optimized program is much smaller, which more than makes up the
optimizer's time, but its functions keep more of their cells in
variables (below), which the C compiler takes longer over. The C
compiler works on the program in parts,
one for each core, all at once (`NAME.c` is still the whole program, in
one file). `--parallel` has loops run on all the cores where they can
(and it pays), if the C compiler has OpenMP (`-fopenmp`, which fern finds
out; macOS's `cc` hasn't, `CC=/opt/homebrew/opt/llvm/bin/clang` has).
It's off by default: a game's loops are too short for it, and it takes
the C compiler longer (NIGHT SHIFT: 17 s against 14). The VM's
own optimizer (`asm::opt`, which makes fewer of the VM's steps) is left out
of native builds: a C compiler does better without it.

The optimizing C backend (`--backend optimizing`, the default; `--backend
literal` is each op as its own line of C, to check against) keeps each
function's cells (the VM's registers
and the function's values, at fixed places from where the pointer was
when it was called) in C variables, which the C compiler can keep in
registers, rather than in the tape's memory, where any write through a
pointer might change them; they go to memory where something might look
(before a call, before returning). Checks keep that exact for any program
(see `bf`'s `backends/optimizing_c/promote.rs`); on a game's frame, it's
about three times as fast.

Either way a program prints the same (`--test` builds and runs each sample
both ways to check). A program that fails (an index out of bounds, running
out of memory, recursing too deep, `panic`) stops then and there with a
message that says which function it was in (`array index out of bounds
(in shift::scene::draw_shift)`), and a status of 1, so whatever ran it can
tell. The C's functions are named for fern's (`f_d412_step`), so a profiler
or a debugger says which they are.

An error says where it is, and shows it:

```text
game.fern:4:14: error: {x: Int, y: Int} has no field z
  |
4 |     println(p.z.show());
  |              ^
```

An error in one function doesn't stop the others being checked: fern says
all it finds (the first ten), and a function whose signature is wrong
isn't an error again wherever it's called. A variable that's never used is
a warning (unless its name starts with `_`). Whatever it's given, fern
says what's wrong rather than crash (`cargo test -p fern` checks that on a
thousand programs broken at random).

A program's memory is one array of 8-byte cells: the stack at one end, the
heap growing toward it from the other. Natively it may use up to 1 GB
(`--memory MB` says otherwise), but that's a ceiling, not what it takes:
the collector (mark and sweep, conservative, in the program itself) runs
whenever the heap has grown to twice what was alive after the last
collection (and at least 8 MB), so a program uses about twice what it
keeps alive, and pages it never touches cost nothing. A program keeping a
million-element list takes about 220 MB; one that makes garbage as fast as
it can, about 10 MB.

`--emit c`, `--emit ops`, `--emit core` and `--emit ir` print the program
as C, as VM ops, after type checking, and after the IR's optimizer;
`--interpret` runs it on the VM's own interpreter instead of building it
(far slower, but no C compiler needed; `--test --interpret` too).

Each pass can be turned off or on: `--disable inline,promote`, `--enable
gvn` (`--passes` lists them, with what each does, and which are on by
default). `--release` has all the IR optimizer's on, and debug none; the
optimizing backend's are on either way. `bf` takes the same options for
the C, the memory and the passes (`--backend`, `--parallel`, `--memory`,
`--enable`, `--disable`), meaning the same: `fern FILE.fern --emit ops >
FILE.bf` and then `bf FILE.bf > FILE.c` makes the same C as fern does
(byte for byte, with the same options). Everything fern does on the way to
a binary can be done that way, step by step:

```sh
fern game/emberwake.fern --release --emit ops > emberwake.bf
bf emberwake.bf --units 8 -o parts       # the C, in 8 files to compile at once
ls parts/*.c | xargs -P 8 -I{} cc -O3 -fwrapv -fno-slp-vectorize -c {} -o {}.o
cc parts/*.o game/screen.c $(pkg-config --cflags --libs sdl2) -o emberwake
```

(`--units` splits the C, as fern does when it builds, one part to a core;
`--inline-ops N` has the optimizing backend inline functions up to N ops
at every call, where fern, by default, inlines only what's called once;
the C's first line says the C compiler's flags fern uses.) That takes
about as long as fern's own build.

`-v`, `-vv` and `-vvv` (or `BF_LOG=1`, `2` or `3`) say on stderr what the
compiler is doing and how long each part takes: the phases (parsing, type
checking, CPS, the IR's optimizer, lowering, the asm optimizer, running);
then what each made and where the optimizers spent their time, pass by
pass; then each function and loop as it goes. `bf` takes the same flags.

## The arcade

`game/` is a suite of programs in fern, in a window: games, demos, a ray
tracer and an emulator. Build them all (it needs SDL2: `brew install
sdl2`), then start the menu:

```sh
fern/game/build.sh all && fern/game/arcade     # (or build.sh --release all)
```

| program | what it is | what it shows off |
|---|---|---|
| `breakout` | Breakout, with the mouse or the keys | structs, enums, `match` |
| `tetris` | Tetris: ghost piece, wall kicks, levels, a beep | bitwise ops on piece masks, a 7-bag shuffle |
| `asteroids` | vector-graphics Asteroids: rocks split, sparks fly | fixed-point trigonometry, Bresenham lines |
| `mines` | Minesweeper (right click flags) | flood fill by recursion |
| `maze` | a 3D maze, raycast like Wolfenstein 3D | a DDA per column, textures, a table of sines |
| `raytrace` | spheres, a mirror, shadows, highlights, a checkered floor | ray tracing in integers, square roots by Newton |
| `mandelbrot` | the Mandelbrot set: click to zoom, two million times | fixed point in 2^26ths, drawing a little each frame |
| `nbody` | two galaxies colliding, in 3D, in real time: drag to turn | a Barnes-Hut octree (`gravity.fern`), fixed point with the operators' traits |
| `updraft` | a glider with no engine over mountains, lakes and snow: circle in rising air (the birds and the beeping variometer find it), fly through beacons for daylight, land before night | a 3D landscape drawn a screen column at a time over a heightmap of noise, with haze, sunset and depth for what flies in it |
| `links` | golf, nine holes across wild country: fairways, greens and bunkers cut into a new landscape for each, the ball bouncing and rolling down its slopes | a course laid out by search (a playable way from tee to pin), ball physics on a heightmap, 3D shared with `updraft` (`voxel.fern`) |
| `umbra` | stealth: a thief in a dark house, after its jewels; lamps throw pools of light and every wall casts a shadow, guards sweep the rooms with lanterns, and in the light you're seen | real-time light and shadow (rays from each light, the fan between them filled), guards that see, hear, chase and search by the shortest way, houses split into rooms |
| `delve` | a dungeon crawl by torchlight: eight floors down to the Ember Crown, monsters that come at you each turn, gold, potions, oil, blades and armor; the torch burns down, and the dark is dangerous | a raycast view (textured walls, floor and ceiling, lit by the torch), pixel-art monsters written as text in the source, floors dug by placing rooms and joining them |
| `bumpercrop` | BUMPER CROP: pinball on a farm. Plant seeds in the table's plots; the ball grows them, and harvests them when they're ripe into your basket; shoot it into the barn to bank the basket times your multiplier before the ball drains, and bank the landlord's rent each week, through four seasons. Between weeks a market of seeds, thirty tools that bend the rules and improvements; fairs whose visitors change the rules; two farms, four farmers, four ribbons, saved | pinball physics in fixed point (capsules and circles, tapered flippers that pass on their surface's speed, eight substeps a frame), a table baked from its own collision shapes into a sunlit diorama (heights, slopes, cast shadows), plants drawn by rule at every stage of their growth, an autopilot that learns the table's shots for the title screen, string-band music made up as it plays |
| `tunnelvision` | TUNNEL VISION: an ant farm, a garden's soil behind glass in layers like sand art. Food turns up on the surface and buried (seeds, leaves, honeydew), and each kind goes to its own chamber; you dig the tunnels and hundreds of ants find their own way, slower uphill, jamming when crowded, stopped by rain pooling in low tunnels. A pile left too long spoils, and then the colony moves out. A dig budget, weekly choices (new chambers to place, stronger jaws, quicker feet), four maps, best scores saved | a distance field per chamber kind and per food pile (a flood through the tunnels, redone when they change) that every ant walks down, water flowing cell to cell, the soil baked into a picture (bands warped by noise, stones and roots as metaballs, tunnels rounded) and redrawn only round what's dug, a live sky running dawn to dusk across each week |
| `stella` | THE AMAZING STELLA: a trapeze act under the big top, played with one button. Hold to catch the nearest hook, let go to fly; chain catches into a combo, tuck into flips, fly through hoops, pop balloons, bounce off trampolines, rest on platforms between, and land on the far platform on your feet. Thirty acts in three tours and an endless Encore, three stars each (finish, beat the time, show the style), hints that teach the timing in the first acts, saved | a swing on a rigid rope (her speed turned along it, a kick at the bottom so a swing never dies), acts made by trying them (every moment of letting go is simulated, and the next hook goes where enough of them reach), an autopilot that looks ahead for the title screen, the hints and each act's time to beat, a curtain that closes while the next act is made, circus-band music made up as it plays |
| `perihelion` | a game of orbits: collect the crystals circling a star with little fuel, past planets and a rock belt; a dotted line shows where you'll coast | everything moving by gravity, the course predicted by simulating ahead, 3D drawing shared with `nbody` (`space.fern`) |
| `sand` | falling sand: sand, water, stone, plants, fire | a cellular automaton |
| `life` | Conway's Life, with age colors and trails | |
| `fire` | the PlayStation Doom fire, with "FERN" burning in it | |
| `chip8` | a CHIP-8 emulator: `chip8 GAME.ch8` | |
| `arcade` | the menu | running the others |

There are no floats in fern: everything in 3D is fixed point
(`math.fern`). The CHIP-8 emulator behaves like the original COSMAC VIP,
passing every test in [Timendus' test
suite](https://github.com/Timendus/chip8-test-suite) (opcodes, flags and
quirks); there are games for it in John Earnest's [CHIP-8
archive](https://github.com/JohnEarnest/chip8Archive).

- `screen.c` is C written with the IR's `bf.h`, on SDL2: a window, the
  keyboard and the mouse, a beep, loading a file named on the command
  line, and running another program. `screen.fern` declares those to fern
  (`extern fn`).
- `draw.fern` draws pixels, lines, rectangles and text (a 3x5 pixel font)
  into a framebuffer, an `Array<Int>` of `0xRRGGBB`s; `math.fern` has fixed
  point, sines, square roots and random numbers.

`build.sh` has fern build each program, linking in `screen.c` and SDL2. Each runs at 60 frames a
second with time to spare: a frame of the maze, 19,200 pixels each
textured and shaded, takes fern about 1.5 ms.

## The language

```rust
mod shapes;                                   // shapes.fern, or shapes/mod.fern
use shapes::{Circle, area};

#[derive(Eq, Ord, Show)]                      // impls written for you
enum Tree<T> { Leaf, Node(Tree<T>, T, Tree<T>) }

trait Size { fn size(self) -> Int; }          // traits, implemented per type
impl<T> Size for Tree<T> {
    fn size(self) -> Int {
        match self { Leaf => 0, Node(l, _, r) => l.size() + 1 + r.size() }
    }
}

fn largest<T: Ord>(xs: List<T>) -> Option<T> { ... }   // bounds
fn get_x(p) { p.x }                           // inferred: takes any record with an x

struct Point { x: Int, y: Int }
impl Point {                                  // methods
    pub fn new(x: Int, y: Int) -> Point { Point { x: x, y: y } }
    pub fn plus(self, o: Point) -> Point { Point::new(self.x + o.x, self.y + o.y) }
}
let p = Point::new(1, 2).plus(Point::new(3, 4));

effect Yield<T> { fn yield(value: T); }       // effects, and handlers for them
fn main() {
    let total = handle numbers() {
        return(u) => 0,
        yield(x) => x + resume(()),
    };
}
```

- **Types are inferred** (Hindley–Milner), so annotations are optional
  except where you want them. A function with type parameters (`<T>`) is
  checked against its signature, with `T` standing for any type.
- **`struct`s and `enum`s** are nominal; **records** (`{ x: 1, y: 2 }`) are
  structural, with row polymorphism: `fn get_x(p) { p.x }` takes any record
  with an `x`. `{ ..r, z: 3 }` adds a field.
- **A struct's fields can be set**, in place: `p.x = 1`, or `self.x = 1` in
  a method. A struct is shared, not copied (as in OCaml or Java), so
  whatever else holds it sees the change. So `=` on a name and `=` on a
  field are different things: `p = q` makes the name `p` (a `let mut`, or
  a `mut` parameter) stand for another struct, here and nowhere else;
  `p.x = 1` changes the struct itself, for everyone. A record's fields
  can't be set.
  (A struct of one field costs nothing, being just that field, unless that
  field is ever set.)
- **Traits** have supertraits (`trait Ord: Eq`), default methods, impls for
  type constructors with requirements (`impl<T: Show> Show for List<T>`),
  and `#[derive(Eq, Ord, Show)]`. Operators use them: `==` is `Eq`, `<` is
  `Ord`. They're coherent: no two impls overlap, and an impl lives with its
  trait or its type.
- **Associated types**: a trait can have `type Item;` (with traits it has to
  have, `type Item: Show + Ord;`), each impl says what it is (`type Item =
  Int;`), and signatures say `Self::Item`, or `C::Item` for a type parameter
  `C: Container`. Generic code can use a `C::Item` as its bounds say (its
  dictionaries are part of `C`'s), and where `C` is known, `C::Item` is
  just what `C`'s impl says.
- **Methods** belong to a type: `impl<T> Stack<T> { .. }`, or for some of
  its types, `impl Stack<Int> { .. }`, in the module that defines it (a
  built-in type's, in the standard library). Tuples and records have them
  too: `impl<A, B> (A, B) { .. }` (for each size of tuple), `impl {x: Int,
  y: Int} { .. }` (for records with exactly those fields, in any order). `x.name(..)` calls one with
  `self` first; `Type::name(..)` calls any of them, and `Type::name` is the
  function. A method's signature is written out in full, as a trait's
  methods' are (no `->` is `()`, no `with` is no effects), so calls to
  methods never wait on their bodies; `pub` makes one usable outside its
  module.
- **`x.name`** is found by `x`'s type: its own method, else a trait's (found
  by the method's name, so `fn f(x) { x.show() }` works for any `x` with
  `Show`), else a function in a field; and `x.field` is a struct's field or
  a record's. Where `x`'s type isn't known yet, that waits until the end of
  the function (any later use can tell it); if it never is, it's a trait's
  method or a record's field, or an error asking for an annotation.
- **Effects** are in function types, inferred like the rest: a function
  that `yield`s has `Yield<T>` in its type. `main` may only have `Io`
  (printing), so every other effect has to be handled. A handler can resume
  the code where it performed the operation, or not, which is how
  generators, exceptions and state are just library code (see `attempt` in
  the standard library, and `samples/effects.fern`). `with E` on a function
  says it may have *only* `E`.
- **Modules** are resolved at compile time, as in Rust: `mod`, `use` (with
  `{..}`, `as`, `*`), `pub`, `crate::`, `super::`, `self::`, and separate
  namespaces for types and values. The standard library (`std/std.fern`) is
  every module's prelude; a module's own names come first.
- **Matches** are checked for exhaustiveness, and say what they miss.
- **Operators** are traits, as in Rust: `a + b` is `Add`'s `a.add(b)`, and
  so on for `Sub`, `Mul`, `Div`, `Rem` and `Neg` (one each, so a type has
  just those that mean something for it), and `Num` is all of them but
  `Rem`, for code that does arithmetic on any number
  (`fn lerp<T: Num>(a: T, b: T, t: T) -> T`). For an `Int` they're the
  machine's own arithmetic; arithmetic on a type nothing decides is
  `Int`'s, as in Haskell. The bitwise operators (`&`, `|`, `^`, `<<`, `>>`)
  are `Int`'s alone. Literals: `42`, `0xff`, and `1.25`, a `Rational`.
- **Arrays** (`Array<T>`) are mutable and fixed in length: `array(n, x)`
  makes one of `n` `x`s, then `array_get(a, i)`, `array_set(a, i, x)` and
  `array_length(a)`, with indices checked.
- **C** is called through `extern fn name(x: Int, ...) -> T;`, for a
  function written with `bf.h` (see `game/screen.c`). Calling one has the
  `Io` effect, unless it says `with {}`: then it's pure, which fern takes on
  trust. (Those are the only two: C can't perform fern's own effects.) Every value is one cell: an `Int` or `Bool` is itself, and an
  `Array` or `String` is a pointer to its length followed by its elements.
  A program with an `extern fn` can't run in `fern` itself: compile it
  with `--emit c`, and the C with the C functions.

## The standard library

`std/std.fern`, all of it fern on the built-ins (no C, nothing else to
link), in every module. What's about one type is that type's methods; what
isn't is a function.

- **Comparing, showing and arithmetic**: `Eq`, `Ord` and `Show`, for
  `Int`, `Bool`, `String`, `()`, pairs and triples, lists, options,
  arrays, maps and sets; `max(a, b)`, `min(a, b)`; and the operators'
  traits, `Add`, `Sub`, `Mul`, `Div`, `Rem`, `Neg`, with `Num` for a type
  with all of them but `Rem` (`Int` and `Rational`).
- **`Rational`**: exact fractions, in place of floating point (`1.25` is
  one, and `0.1 + 0.2 == 0.3`), kept in lowest terms: `+ - * /`, comparing
  (without multiplying, so it can't overflow), `floor`, `ceil`, `round`,
  `pow`, `sqrt`, `to_decimal` (by long division), `Rational::parse`
  (`"3"`, `"-7/2"`, `"1.25"`), and `limit(max_den)`, the closest fraction
  with a small denominator (`pi.limit(1000)` is 355/113), which keeps long
  calculations from overflowing.
- **Numbers** (`Int`'s methods): `abs`, `sign`, `clamp`, `pow`, `gcd`,
  `lcm`, `isqrt`, `log2`, `count_ones`, `div_floor` and `mod_floor`
  (rounding down, where `/` and `%` round toward 0), `to_base`
  (`255.to_base(16)` is `"ff"`); and for characters, which are their codes:
  `is_digit`, `is_alpha`, `is_space`, ..., `to_upper`, `to_lower`,
  `to_char`, `digit_value`.
- **`Option` and `Result`**: `unwrap`, `unwrap_or`, `expect`, `map`,
  `and_then`, `or`, `ok_or`, `ok`, `map_err`, `is_some`, ...
- **`List`**: `len`, `get`, `map`, `filter`, `fold`, `fold_right`, `reduce`,
  `take`, `drop`, `zip`, `enumerate`, `find`, `position`, `any`, `all`,
  `partition`, `chunks`, `dedup`, `unique`, `maximum`, `sort` (a stable
  merge sort), `sort_by`, `sort_on`, and more; `sum` and `product` for
  lists of numbers, `join` and `concat` for lists of strings, `flatten`
  for lists of lists, `lookup` and `unzip` for lists of pairs. And the
  functions `range`, `range_step` and `repeat`.
- **`String`**: `len`, `chars`, `split`, `lines`, `words`, `trim`,
  `substring`, `starts_with`, `find`, `contains`, `replace`, `to_upper`,
  `pad_left`, `repeat`, `parse_int`, `parse_base`; `String::from_chars`.
- **`Array`**: `len`, `get`, `set`, `to_list`, `slice`, `copy`, `fill`,
  `reverse`, `update`, `fold`, `sort` (a heap sort, in place),
  `binary_search`, ...; `Array::new`, `Array::from_list`.
- **`Map<K, V>`**, an AVL tree (`get`, `insert`, `remove`, `update`, `keys`,
  `to_list`, ..., in log n steps, never changing a map: inserting gives a
  new one), and **`Set<T>`** (`insert`, `contains`, `union`,
  `intersection`, `difference`, ...); `Map::new`, `Map::from_list`.
- **Effects**: `Fail` (`attempt`, `or_default`, `need`), `State<S>`
  (`get`, `put`, `modify`, `run_state`), `Yield<T>` (`yield`, `collect`,
  `for_each`), and `Choose` (`choose`, `give_up`, `guard`, with
  `all_ways` and `first_way`: search written as if it always guessed
  right).

`samples/std_*.fern` show each part.

## The compiler

| stage | files | what it does |
|---|---|---|
| syntax | `lexer.rs`, `parser.rs`, `ast.rs` | text to tokens to a syntax tree, by recursive descent |
| modules | `modules.rs`, `derive.rs` | files to a module tree, every item named in full; `use`s worked out; derived impls written |
| types | `types.rs`, `checker.rs`, `expr.rs`, `traits.rs`, `exhaust.rs` | inference, producing `core.rs`'s untyped language |
| CPS | `direct.rs`, `cps.rs` | continuation-passing style, which is how handlers get `resume`, for the functions that can perform effects |
| code | `codegen.rs` | closure conversion, and the `bf::ir::Program`, with a small runtime |

### Type inference

- **Unification** (`types.rs`) solves the equations inference makes. Type
  variables have *levels*, how many generalizing scopes deep they were
  made, so generalizing quantifies only the variables that didn't escape
  into an outer scope.
- **Functions** are checked a recursive group at a time (Tarjan's algorithm
  on which call which), and each group is generalized, so a function is
  polymorphic before anything outside its group uses it. Local `let`s
  aren't generalized, which keeps traits simple.
- **Skolems** are what type parameters become while their function is
  checked: types equal only to themselves, so `fn f<T>(x: T) -> T { x + 1 }`
  is an error.
- **Rows** are one mechanism for records and effects: a list of labelled
  types ending in nothing or a variable. Unifying finds each label in the
  other row and grows rows that end in variables (Leijen's scoped labels).

### Traits are dictionaries

Using a trait method records a *requirement* (`Show<a>`) with a hole for its
dictionary. When a group is generalized, `traits.rs` meets each one: with a
dictionary the function was given, a supertrait's part of one, an impl
(whose own requirements are met the same way), or a new dictionary
parameter if it's on one of the function's type variables. A dictionary is
a block of closures, its methods, followed by its supertraits'
dictionaries. Where the impl is known at the call, the method is called
directly, and `==` and `<` on `Int`, `Bool` and `String` become machine
comparisons.

### Effects are continuations, where they need to be

In CPS every function takes `k`, what to do with its result, and `h`, the
handlers in effect, and calls `k` instead of returning. `handle` pushes a
frame on `h` holding the clauses and where the handle's result goes; an
operation finds the nearest frame for its effect and calls the clause with
`resume`, a closure over the operation's continuation. (These are deep
handlers; resuming more than once works when the resumptions run one after
another.)

Since CPS calls never return, the VM's stack would only grow: every call
counts its depth, and past 100 it returns a *thunk* (the call, as data) to
a loop in `main` that makes it there, a trampoline.

All that costs: a continuation closure for every call. So only functions
that need it are in CPS (`direct.rs`): a function that makes no lambdas,
calls no function values, has no `handle` and performs no operation, and
calls only functions like it, can't perform an effect, so it's compiled
straight to an IR function, with loops as loops and `let mut`s as
variables. That's most of the code that does the work in a program, and it
runs many times faster: the games are almost all direct.

## Limits, and where to go next

- No floats: `Rational`s are exact, but their numerators and denominators
  are 64-bit `Int`s, which a long calculation can overflow (`limit` is the
  remedy). An integer literal is always an `Int` (`r + 1` is an error;
  `r + 1.0` isn't).
- No higher-kinded traits (`Functor`).
- A trait's default methods go through its dictionary, so they keep a
  function in CPS; an impl can define its own (as `Ord for Int` does
  `min` and `max`).
