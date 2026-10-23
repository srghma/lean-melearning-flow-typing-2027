#![allow(dead_code)]
#![allow(unused_imports)]
//! Tests for the flow typing compiler's type checker (`infer.rs`) and translation (`core.rs`).
//!
//! The compiler's lexer and parser need crates from crates.io, so this harness skips them:
//! each test program is written directly as a parsed syntax tree (`parse::Item`), and then
//! goes through the compiler's own renaming, type inference and translation passes.
//! Run `python3 create_files.py` in the project root first, so that `flow-typing-compiler/`
//! exists, and then `cargo run` in this directory.

#[path = "../../../flow-typing-compiler/src/core.rs"]
mod core;
mod error;
#[path = "../../../flow-typing-compiler/src/infer.rs"]
mod infer;
#[path = "../../../flow-typing-compiler/src/out_of_scope.rs"]
mod out_of_scope;
/// The data types of the compiler's `parse.rs`, without the parser itself.
mod parse;
#[path = "../../../flow-typing-compiler/src/rename.rs"]
mod rename;

use parse::{Expr, Flow, Item, Literal, Pattern, PreType, PrimOp, PrimTy};

const S: std::ops::Range<usize> = 0..0;

fn sp(n: usize) -> std::ops::Range<usize> {
    n..n + 1
}

// ---- expressions
fn v(n: &'static str) -> Expr<'static> {
    Expr::Var(n, S)
}
fn t(e: Expr<'static>) -> Expr<'static> {
    Expr::Tilde(Box::new(e), S)
}
fn app(f: Expr<'static>, x: Expr<'static>) -> Expr<'static> {
    Expr::App(Box::new(f), Box::new(x), S)
}
fn app2(f: Expr<'static>, x: Expr<'static>, y: Expr<'static>) -> Expr<'static> {
    app(app(f, x), y)
}
fn assign(l: Expr<'static>, r: Expr<'static>) -> Expr<'static> {
    Expr::Assign(Box::new(l), Box::new(r), S)
}
fn tup(es: Vec<Expr<'static>>) -> Expr<'static> {
    Expr::Tuple(es, S)
}
fn unit() -> Expr<'static> {
    tup(vec![])
}
fn int(n: u64) -> Expr<'static> {
    Expr::Literal(Literal::Integer(n), S)
}
fn op(l: Expr<'static>, r: Expr<'static>, o: PrimOp) -> Expr<'static> {
    Expr::PrimOp(Box::new(l), Box::new(r), o, S)
}
fn seq(l: Expr<'static>, r: Expr<'static>) -> Expr<'static> {
    op(l, r, PrimOp::Seq)
}
fn lam(ps: Vec<(Flow, Pattern<'static>)>, b: Expr<'static>) -> Expr<'static> {
    Expr::Lambda(ps, Box::new(b), S)
}
fn let_(f: Flow, p: Pattern<'static>, val: Expr<'static>, b: Expr<'static>) -> Expr<'static> {
    Expr::Let {
        flow: f,
        pattern: p,
        value: Box::new(val),
        body: Box::new(b),
        span: S,
    }
}
fn case(f: Flow, s: Expr<'static>, bs: Vec<(Pattern<'static>, Expr<'static>)>) -> Expr<'static> {
    Expr::Case {
        flow: f,
        scrutinee: Box::new(s),
        branches: bs,
        span: S,
    }
}
// ---- patterns
fn pv(n: &'static str) -> Pattern<'static> {
    Pattern::Var(n, S)
}
fn pt(ps: Vec<Pattern<'static>>) -> Pattern<'static> {
    Pattern::Tuple(ps, S)
}
fn pnil() -> Pattern<'static> {
    Pattern::EmptyList(S)
}
fn pcons(h: Pattern<'static>, tl: Pattern<'static>) -> Pattern<'static> {
    Pattern::Cons(Box::new(h), Box::new(tl), S)
}
fn plain(p: Pattern<'static>) -> (Flow, Pattern<'static>) {
    (Flow::Plain, p)
}
fn flow(p: Pattern<'static>) -> (Flow, Pattern<'static>) {
    (Flow::Flow, p)
}
// ---- types
fn ty(n: &'static str) -> PreType<'static> {
    PreType::Var(n, S)
}
fn tint() -> PreType<'static> {
    PreType::Prim(PrimTy::Int, S)
}
fn tchar() -> PreType<'static> {
    PreType::Prim(PrimTy::Char, S)
}
fn tworld() -> PreType<'static> {
    PreType::Prim(PrimTy::World, S)
}
fn thandle() -> PreType<'static> {
    PreType::Prim(PrimTy::Handle, S)
}
fn tlist(a: PreType<'static>) -> PreType<'static> {
    PreType::App(Box::new(PreType::List(S)), Box::new(a), S)
}
fn arr(a: PreType<'static>, b: PreType<'static>) -> PreType<'static> {
    PreType::Arrow(Box::new(a), Box::new(b), S)
}
fn sl(a: PreType<'static>, b: PreType<'static>) -> PreType<'static> {
    PreType::Flow(Box::new(a), Box::new(b), S)
}
fn same(a: PreType<'static>) -> PreType<'static> {
    sl(a.clone(), a)
}
fn ttup(ts: Vec<PreType<'static>>) -> PreType<'static> {
    PreType::Tuple(ts, S)
}
fn tunit() -> PreType<'static> {
    ttup(vec![])
}
// ---- items
fn decl(n: &'static str, t: PreType<'static>) -> Item<'static> {
    Item::Decl {
        name: n,
        span: S,
        ty: t,
    }
}
fn def(n: &'static str, ps: Vec<(Flow, Pattern<'static>)>, e: Expr<'static>) -> Item<'static> {
    Item::Def {
        name: n,
        span: S,
        patterns: ps,
        expr: e,
    }
}

/// Runs the pipeline after parsing. Returns Ok(haskell) or Err(messages).
fn run(items: Vec<Item<'static>>) -> Result<String, ()> {
    let mut errors = error::Errors::default();
    let (decls, defs) = rename::rename(&mut errors, items);
    errors.emit("").ok_or(())?;
    let inferred = infer::infer(&mut errors, &decls, defs);
    errors.emit("").ok_or(())?;
    let (_decls, defs) = core::translate(&mut errors, decls, inferred);
    errors.emit("").ok_or(())?;
    let mut out = String::new();
    for def in defs {
        out.push_str(&format!("{} = {}\n", def.name, core::HaskellExpr(&def.expr)));
    }
    Ok(out)
}

fn check(name: &str, expect_ok: bool, items: Vec<Item<'static>>) -> bool {
    println!("==== {name} (expect {})", if expect_ok { "accept" } else { "reject" });
    let r = std::panic::catch_unwind(move || run(items));
    let ok = match r {
        Ok(Ok(out)) => {
            println!("ACCEPTED:\n{out}");
            expect_ok
        }
        Ok(Err(())) => {
            println!("REJECTED (type error)");
            !expect_ok
        }
        Err(_) => {
            println!("COMPILER PANIC");
            false
        }
    };
    println!("{}", if ok { "PASS" } else { "FAIL" });
    ok
}

fn prelude() -> Vec<Item<'static>> {
    vec![
        decl("consume", arr(ty("a"), tunit())),
        decl("dup", arr(same(ty("a")), ty("a"))),
        decl("readFile", arr(same(ttup(vec![tworld(), thandle()])), tlist(PreType::Prim(PrimTy::Char, S)))),
        // A function with a plain argument and a flow result.
        decl("focus", arr(tint(), same(tint()))),
    ]
}

fn with_prelude(mut items: Vec<Item<'static>>) -> Vec<Item<'static>> {
    let mut p = prelude();
    p.append(&mut items);
    p
}

fn main() {
    // Silence the debug output of the translation and the default panic message.
    std::panic::set_hook(Box::new(|info| println!("panic: {info}")));
    let mut results = Vec::new();

    // ---------- Regression tests: programs from examples.fl that must still compile.
    results.push(check(
        "examples: inc, fst, incFst",
        true,
        with_prelude(vec![
            decl("inc", arr(same(tint()), tunit())),
            def("inc", vec![flow(pv("x"))], assign(v("x"), op(v("x"), int(1), PrimOp::Add))),
            decl("fst", arr(sl(ttup(vec![ty("a"), ty("b")]), ttup(vec![ty("a'"), ty("b")])), sl(ty("a"), ty("a'")))),
            def("fst", vec![flow(pt(vec![pv("x"), pv("y")]))], t(v("x"))),
            decl("incFst", arr(same(ttup(vec![tint(), ty("a")])), tunit())),
            def("incFst", vec![flow(pv("x"))], app(v("inc"), t(app(v("fst"), t(v("x")))))),
        ]),
    ));
    results.push(check(
        "examples: swap, swapPair, united, idl",
        true,
        with_prelude(vec![
            decl("swap", arr(sl(ttup(vec![ty("a"), ty("b")]), ttup(vec![ty("c"), ty("d")])), sl(ttup(vec![ty("b"), ty("a")]), ttup(vec![ty("d"), ty("c")])))),
            def("swap", vec![flow(pt(vec![pv("x"), pv("y")]))], t(tup(vec![v("y"), v("x")]))),
            decl("swapPair", arr(sl(ttup(vec![ty("a"), ty("b")]), ttup(vec![ty("b"), ty("a")])), tunit())),
            def("swapPair", vec![flow(pt(vec![pv("x"), pv("y")]))], assign(v("y"), assign(v("x"), v("y")))),
            decl("united", arr(same(ty("a")), same(tunit()))),
            def("united", vec![flow(pv("x"))], t(unit())),
            decl("idl", arr(sl(ty("a"), ty("b")), sl(ty("a"), ty("b")))),
            def("idl", vec![flow(pv("x"))], t(v("x"))),
        ]),
    ));
    results.push(check(
        "examples: fcomp, join, funcurry, map, unmap, over",
        true,
        with_prelude(vec![
            decl("fcomp", arr(arr(sl(ty("b"), ty("b'")), sl(ty("c"), ty("c'"))), arr(arr(sl(ty("a"), ty("a'")), sl(ty("b"), ty("b'"))), arr(sl(ty("a"), ty("a'")), sl(ty("c"), ty("c'")))))),
            def("fcomp", vec![plain(pv("g")), plain(pv("f")), flow(pv("x"))], t(app(v("g"), t(app(v("f"), t(v("x"))))))),
            decl("join", arr(arr(sl(ty("a"), ty("a'")), sl(ty("b"), ty("b'"))), arr(arr(sl(ty("c"), ty("c'")), sl(ty("d"), ty("d'"))), arr(sl(ttup(vec![ty("a"), ty("c")]), ttup(vec![ty("a'"), ty("c'")])), sl(ttup(vec![ty("b"), ty("d")]), ttup(vec![ty("b'"), ty("d'")])))))),
            def("join", vec![plain(pv("f")), plain(pv("g")), flow(pt(vec![pv("x"), pv("y")]))], t(tup(vec![app(v("f"), t(v("x"))), app(v("g"), t(v("y")))]))),
            decl("funcurry", arr(arr(sl(ty("a"), ty("a'")), arr(sl(ty("b"), ty("b'")), sl(ty("c"), ty("c'")))), arr(sl(ttup(vec![ty("a"), ty("b")]), ttup(vec![ty("a'"), ty("b'")])), sl(ty("c"), ty("c'"))))),
            def("funcurry", vec![plain(pv("f")), flow(pt(vec![pv("x"), pv("y")]))], t(app2(v("f"), t(v("x")), t(v("y"))))),
            decl("map", arr(arr(ty("a"), ty("b")), arr(sl(ty("a"), ty("b")), tunit()))),
            def("map", vec![plain(pv("f")), flow(pv("x"))], assign(v("x"), app(v("f"), v("x")))),
            decl("unmap", arr(arr(sl(ty("a"), ty("b")), tunit()), arr(ty("a"), ty("b")))),
            def("unmap", vec![plain(pv("f")), plain(pv("x"))], seq(app(v("f"), t(v("x"))), v("x"))),
            decl("over", arr(arr(ty("a"), ty("b")), arr(arr(sl(ty("c"), ty("d")), sl(ty("a"), ty("b"))), arr(ty("c"), ty("d"))))),
            def("over", vec![plain(pv("f")), plain(pv("g")), plain(pv("x"))], seq(app2(v("map"), v("f"), t(app(v("g"), t(v("x"))))), v("x"))),
        ]),
    ));
    results.push(check(
        "examples: length (case ~xs), fileWords/avg (lens tuples in sequence)",
        true,
        with_prelude(vec![
            decl("length", arr(same(tlist(ty("a"))), tint())),
            def("length", vec![flow(pv("xs"))], case(Flow::Flow, v("xs"), vec![
                (pnil(), int(0)),
                (pcons(pv("y"), pv("ys")), op(int(1), app(v("length"), t(v("ys"))), PrimOp::Add)),
            ])),
            decl("count", arr(tlist(PreType::Prim(PrimTy::Char, S)), tint())),
            decl("fileWords", arr(same(ttup(vec![tworld(), thandle()])), tint())),
            def("fileWords", vec![flow(pt(vec![pv("w"), pv("f")]))], app(v("count"), app(v("readFile"), t(tup(vec![v("w"), v("f")]))))),
            decl("avg", arr(same(ttup(vec![tworld(), thandle()])), tint())),
            def("avg", vec![flow(pt(vec![pv("w"), pv("f")]))], op(
                app(v("fileWords"), t(tup(vec![v("w"), v("f")]))),
                app(v("fileWords"), t(tup(vec![v("w"), v("f")]))),
                PrimOp::Div,
            )),
        ]),
    ));
    results.push(check(
        "examples: onZero / main (flow lambda without captures)",
        true,
        with_prelude(vec![
            decl("inc", arr(same(tint()), tunit())),
            def("inc", vec![flow(pv("x"))], assign(v("x"), op(v("x"), int(1), PrimOp::Add))),
            decl("onZero", arr(arr(same(tint()), tunit()), tint())),
            def("onZero", vec![plain(pv("f"))], let_(Flow::Plain, pv("i"), int(0), seq(app(v("f"), t(v("i"))), v("i")))),
            decl("main", tint()),
            def("main", vec![], app(v("onZero"), lam(vec![flow(pv("i"))], assign(v("i"), op(v("i"), int(1), PrimOp::Add))))),
        ]),
    ));

    results.push(check(
        "examples: pop, push, split, usingFile",
        true,
        with_prelude(vec![
            decl("pop", arr(same(tlist(tint())), tint())),
            def("pop", vec![flow(pv("xs"))], case(Flow::Plain, v("xs"), vec![
                (pcons(pv("y"), pv("ys")), seq(assign(v("xs"), v("ys")), v("y"))),
            ])),
            decl("push", arr(tint(), arr(same(tlist(tint())), tunit()))),
            def("push", vec![plain(pv("x")), flow(pv("xs"))], assign(v("xs"), Expr::Cons(Box::new(v("x")), Box::new(v("xs")), S))),
            decl("split", arr(tchar(), arr(tlist(tchar()), ttup(vec![tlist(tchar()), tlist(tchar())])))),
            def("split", vec![plain(pv("c")), plain(pv("xs"))], case(Flow::Plain, v("xs"), vec![
                (pnil(), seq(app(v("consume"), v("c")), tup(vec![Expr::EmptyList(S), Expr::EmptyList(S)]))),
                (pcons(pv("x"), pv("xs")), case(Flow::Plain, op(app(v("dup"), t(v("x"))), app(v("dup"), t(v("c"))), PrimOp::Eq), vec![
                    (Pattern::Literal(Literal::Bool(true), S), seq(app(v("consume"), v("x")), seq(app(v("consume"), v("c")), tup(vec![Expr::EmptyList(S), v("xs")])))),
                    (Pattern::Literal(Literal::Bool(false), S), let_(Flow::Plain, pt(vec![pv("y"), pv("z")]), app2(v("split"), v("c"), v("xs")),
                        tup(vec![Expr::Cons(Box::new(v("x")), Box::new(v("y")), S), v("z")]))),
                ])),
            ])),
            decl("truncateFile", arr(tlist(tchar()), arr(same(tworld()), thandle()))),
            decl("closeFile", arr(thandle(), arr(same(tworld()), tunit()))),
            decl("usingFile", arr(tlist(tchar()), arr(arr(same(ttup(vec![tworld(), thandle()])), ty("a")), arr(same(tworld()), ty("a"))))),
            def("usingFile", vec![plain(pv("x")), plain(pv("f")), flow(pv("w"))],
                let_(Flow::Plain, pv("h"), app2(v("truncateFile"), v("x"), t(v("w"))),
                let_(Flow::Plain, pv("a"), app(v("f"), t(tup(vec![v("w"), v("h")]))),
                seq(app2(v("closeFile"), v("h"), t(v("w"))), v("a"))))),
        ]),
    ));
    results.push(check(
        "examples: badFileUsage (commented out in examples.fl, must be rejected)",
        false,
        with_prelude(vec![
            decl("msg", tlist(tchar())),
            decl("writeFile", arr(tlist(tchar()), arr(same(ttup(vec![tworld(), thandle()])), tunit()))),
            decl("usingFile", arr(tlist(tchar()), arr(arr(same(ttup(vec![tworld(), thandle()])), ty("a")), arr(same(tworld()), ty("a"))))),
            decl("badFileUsage", arr(tlist(tchar()), arr(same(tworld()), tunit()))),
            def("badFileUsage", vec![plain(pv("s")), flow(pv("w"))],
                {
                    let inner = lam(vec![flow(pt(vec![pv("w"), pv("f")]))], lam(vec![plain(pt(vec![]))], app2(v("writeFile"), v("s"), t(tup(vec![v("w"), v("f")])))));
                    app(app(app2(v("usingFile"), v("msg"), inner), t(v("w"))), unit())
                }),
        ]),
    ));

    // ---------- Bug 1a: the lens tuple ~(x, x) must be rejected (context split in ~⊗-I).
    results.push(check(
        "bug 1a: lens tuple ~(x, x)",
        false,
        with_prelude(vec![
            decl("dupl", arr(same(ty("a")), same(ttup(vec![ty("a"), ty("a")])))),
            def("dupl", vec![flow(pv("x"))], t(tup(vec![v("x"), v("x")]))),
        ]),
    ));
    // Bug 1b: case ~x of y -> ... x ... must be rejected (context split in ~⊕-E / ~Let).
    results.push(check(
        "bug 1b: case ~x of y -> dup ~x",
        false,
        with_prelude(vec![
            decl("bad", arr(same(tint()), tint())),
            def("bad", vec![flow(pv("x"))], case(Flow::Flow, v("x"), vec![(pv("y"), app(v("dup"), t(v("x"))))])),
        ]),
    ));
    results.push(check(
        "bug 1b': let y = ~x in dup ~x",
        false,
        with_prelude(vec![
            decl("bad", arr(same(tint()), tint())),
            def("bad", vec![flow(pv("x"))], let_(Flow::Flow, pv("y"), v("x"), app(v("dup"), t(v("x"))))),
        ]),
    ));
    // Bug 2: a flow lambda capturing x and leaving it live must be rejected.
    results.push(check(
        "bug 2: \\~y -> ~x with x captured",
        false,
        with_prelude(vec![
            decl("bad", arr(same(ty("a")), arr(same(tunit()), same(ty("a"))))),
            def("bad", vec![flow(pv("x"))], lam(vec![flow(pv("y"))], t(v("x")))),
        ]),
    ));
    results.push(check(
        "bug 2 (control): \\~y -> () with nothing captured",
        true,
        with_prelude(vec![
            decl("ok", arr(same(ty("a")), arr(same(tunit()), tunit()))),
            def("ok", vec![flow(pv("x"))], lam(vec![flow(pv("y"))], unit())),
        ]),
    ));
    // Bug 3: application with a plain argument in lens position.
    results.push(check(
        "bug 3: ~(focus n)",
        true,
        with_prelude(vec![
            decl("useFocus", arr(tint(), same(tint()))),
            def("useFocus", vec![plain(pv("n"))], t(app(v("focus"), v("n")))),
            decl("incFocus", arr(tint(), tint())),
            def("incFocus", vec![plain(pv("n"))], assign(app(v("focus"), v("n")), int(3))),
        ]),
    ));
    // Bug 4a: let with a lens scrutinee must compile instead of crashing.
    results.push(check(
        "bug 4a: let (x, y) = ~z in ()",
        true,
        with_prelude(vec![
            decl("letl", arr(same(ttup(vec![ty("a"), ty("b")])), tunit())),
            def("letl", vec![flow(pv("z"))], let_(Flow::Flow, pt(vec![pv("x"), pv("y")]), v("z"), unit())),
            decl("swapl", arr(sl(ttup(vec![ty("a"), ty("b")]), ttup(vec![ty("b"), ty("a")])), tunit())),
            def("swapl", vec![flow(pv("z"))], let_(Flow::Flow, pt(vec![pv("x"), pv("y")]), v("z"), assign(v("y"), assign(v("x"), v("y"))))),
        ]),
    ));
    // Bug 4b: literal lens must be a type error rather than a crash.
    results.push(check(
        "bug 4b: literal lens ~3",
        false,
        with_prelude(vec![
            decl("inc", arr(same(tint()), tunit())),
            def("inc", vec![flow(pv("x"))], assign(v("x"), op(v("x"), int(1), PrimOp::Add))),
            decl("lit", tunit()),
            def("lit", vec![], app(v("inc"), t(int(3)))),
        ]),
    ));

    let passed = results.iter().filter(|r| **r).count();
    println!("\n{passed}/{} tests passed", results.len());
    if passed != results.len() {
        std::process::exit(1);
    }
}
