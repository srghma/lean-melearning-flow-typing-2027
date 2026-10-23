# Comparing the Lean grammar of `λF` with the reference compiler

This report compares the Lean formalisation of `λF` (`RequestProject/FlowTyping/LambdaF.lean`
and `Syntax.lean`) with the flow-typing compiler that `create_files.py` generates in
`flow-typing-compiler/`. The compiler is written in Rust and translates `examples.fl` into
`flow/Examples.hs`.

**How the comparison was done.** I read the compiler source: `lex.rs`, `layout.rs`, `parse.rs`,
`rename.rs`, `infer.rs`, `core.rs` and `main.rs`. I did not build or run the compiler, so every
statement below about how it behaves comes from reading the code. The only claims checked by
Lean are the ones in §6, which are proved in
`RequestProject/FlowTyping/CompilerExamples.lean`.

## 1. Verdict

* **Our grammar is correct with respect to the paper.** `LinTm`, `LensTm` and `Tm` match Fig. 4
  constructor for constructor, and `LinTy`, `LensTy` and `TmTy` match the rules listed in
  Appendix A, with `inr` rules added. Comparing with the compiler found nothing that needs to
  change in the Lean grammar.
* **The compiler's core language is a fragment of `λF`, plus practical extensions.** Every
  `λF` construct that the compiler implements corresponds to a constructor of our grammar,
  with the same binding structure and the same evaluation order. The compiler leaves out a
  substantial part of `λF` (§4) and adds features that are not in the paper (§5).
* **The two implementations use the same de Bruijn convention.** `rename.rs` uses de Bruijn
  indices with the most recent binder at index 0 (`VecDeque::push_front`). A tuple pattern
  `(x, y)` binds `y = 0` and `x = 1`. These are exactly the conventions of our
  `letPair` / `letPairLens`.
* **The type translation `(−)°` is the same.** In `core.rs`, the conversion
  `impl From<rename::Type> for core::Type` translates flow function types exactly as our
  `LambdaF.PTy.circ` does:
  * `(A ⊸ B/B')° = A ⊸ B ⊗ (B' ⊸ 1)`
  * `(A/A' ⊸ B)° = A ⊸ B ⊗ A'`
  * `(A/A' ⊸ B/B')° = A ⊸ B ⊗ (B' ⊸ A')`
* **The compiler's checker is more permissive than the paper in a few places.** In those
  places the program is rejected (or the compiler crashes) only later, during translation or
  when GHC checks the output (§7). Two of these cases are formally shown to be rejected by
  our rules (§6).

## 2. Types

| paper / Lean (`PTy`, `FTy`) | compiler (`rename::Type`, `TType`) | remark |
|---|---|---|
| `T ::= A \| A/B` (`FTy.plain`, `FTy.slash`) | `TType::Plain`, `TType::Flow`; surface `a/b`, and `~a` for `a/a` | same |
| `α` (`tvar`) | `Type::Var` (named, e.g. `a`, `b'`) | in the compiler, top-level declarations are polymorphic in these variables (§5) |
| `T ⊸ T'` (`PTy.lolli : FTy → FTy → PTy`) | `Type::Arrow(TType, TType)`, surface `->` | same: both sides may be flow types |
| `A ⊗ B`, `1` | `Type::Tuple(Vec<_>)`, `(a, b, …)`, `()` | n-ary tuples instead of binary `⊗` (isomorphic) |
| `A ⊕ B` | `Either a b` | same |
| `0`, `A & B`, `⊤`, `!A` | — | **not implemented** |
| — | `Int`, `Bool`, `Char`, `String = List Char`, `World`, `Handle`, `List a`, `Tree a` | **extensions** (`Tree` is only a type: it has no constructors or patterns) |

## 3. Terms and typing rules: what corresponds

The compiler's typed intermediate language is `infer::Expr` (linear terms `t`), `infer::Lens`
(lens terms `u`) and `infer::ExprOrLens` (`s ::= t | ~u`). It corresponds to our `LinTm`,
`LensTm` and `Tm` as follows.

| paper rule | Lean | compiler (`infer.rs`) | agreement |
|---|---|---|---|
| Var | `LinTm.var`, `LinTy.var` | `Expr::Var`; the variable's entry becomes `None` (dead); using a dead variable is an error | same |
| FVar-Live / FVar-Dead | `LensTm.var`, `varLive` / `varDead` | `Lens::Var`; a dead variable gets type `()` = `1`, and the variable is set live with the new type | same |
| Assign `u ≔ t` | `LinTm.assign`, `LinTy.assign` | `Expr::Assign`, surface `u := t`; checks `t` first, then `u` | same, including the order `Γ₁ → Γ₂ → Γ₃` |
| ⊸-E, linear result | `LinTm.app`, `LinTy.app` | `Expr::App(Expr, ExprOrLens)` | same |
| ⊸-E, flow result | `LensTm.app`, `LensTy.app` | `Lens::App(Expr, ExprOrLens)` | same |
| ⊸-I / ~⊸-I | `LinTm.lam : FTy → Tm (n+1) → LinTm n`, `lam` / `lamSlash` | `Expr::Lambda{flow, pattern, body: ExprOrLens}`; `f p₁ … pₖ = e` and `\p₁ … pₖ -> e` are nested lambdas | same (see §7.2 for captured variables) |
| ⊗-I, 1-I | `LinTm.pair`, `LinTm.unit` | `Expr::Tuple` (n-ary, left to right) | same |
| ~⊗-I, ~1-I | `LensTm.pair`, `LensTm.unit` | `Lens::Tuple`, e.g. `~(x, y)`, `~()` | same syntax; the checker differs (§7.1) |
| Let, ⊗-E, 1-E (linear scrutinee) | `LinTm.letIn` / `letPair` / `letUnit` with `Tm.lin` | `Expr::Let{pattern, value: Expr}`; `t₁; t₂` (or a line break) means `let () = t₁ in t₂`, which is a `PrimOp::Seq` | same; bound pattern variables must be dead at the end of their scope (`Ctx::retract`), as in `Γ₃, x†` |
| ~Let, ~⊗-E, ~1-E (lens scrutinee) | `letInLens` / `letPairLens` / `letUnitLens` | `Expr::Let{value: Lens}` (`let p = ~u`), and flow lambda patterns `\~(x, y) -> …` | flow-bound variables must be live at the end of the body, with the declared output type, as in `Γ₄, x : A'`; but see §7.3 |
| ⊕-IL / ⊕-IR | `LinTm.inl` / `inr` (annotated with `A ⊕ B`) | `Expr::Left` / `Right` (no annotation; the type is inferred) | same up to annotations |
| ⊕-E / ~⊕-E | `LinTm.case` with `Tm.lin` / `Tm.lens` | `Expr::Case{scrutinee: ExprOrLens, branches}`, surface `case e of` / `case ~e of` | every branch must end with the same output context (the checker compares liveness and unifies types), as in the paper; `case ~u` is translated with a context split, as in `~⊕-E` |

A flow pattern parameter of a definition such as `fst ~(x, y) = ~x` is the paper's
`λz : (A ⊗ B)/(A' ⊗ B). let (x, y) = ~z in ~x` (Example 5.10, our `fstF`). Its body is a
**lens term** of the form `let (x, y) = ~z in u`. So even though the compiler has no
standalone syntax for lens-bodied binders, they are needed to give a meaning to its flow
patterns. Our grammar has them (`LensTm.letPair` and `letPairLens`).

## 4. In our grammar (and the paper) but not in the compiler

* Lens literals `lens x ← t₁ in t₂` (`LensTm.lens`) and `unlens u in t` (`LinTm.unlens`). There is
  no surface syntax for either. In `examples.fl`, functions such as `use` and `take` are written
  with assignment instead.
* Lens terms whose body is a binder: `let x = s in u`, `let (x, y) = s in u`, `let ∗ = s in u`,
  `case s of … → u`, and `false_A(s)` as a lens (`LensTm.letIn/letPair/letUnit/case/falseE`). In
  `infer_lens`, the cases `Let`, `Case`, `Lambda`, `Left`, `Right`, lists and `Assign` all reach
  `out_of_scope!()`, which is an `unimplemented!` panic.
* The additives and exponentials: `0`/`false`, `&`/`fst`/`snd`, `⊤`/`true`, and
  `!`/`promote`/`discard`/`copy`/`derelict`. Instead, the compiler relies on Linear Haskell
  (`consume`, `dup`, and unrestricted top-level definitions).
* `let p = ~u in t` passes the checker (`infer.rs`), but `core.rs` reaches `out_of_scope!()` on
  it (`infer::Expr::Let` with `ExprOrLens::Lens`). In practice only `case ~u of p -> t` works.

## 5. In the compiler but not in the paper

* Base types, literals, the arithmetic and equality primitives (`+ - * / ==`), and strings.
* Recursive types (`List`, `Tree`) and **general recursion**, through top-level definitions that
  refer to themselves (`exec`, `length`, `split`). `λL`/`λF` have no recursion, so our semantics
  `Eval` and type safety (Prop. 7.1) say nothing about such programs.
* Top-level declarations that can be used any number of times and are **polymorphic**
  (`Expr::Inst` creates a fresh instance of the declaration's type variables at each use).
  The paper's type variables are just atoms.
* Nested, n-ary patterns (tuples, `[]`, `x:xs`, `Left`/`Right`, literals). Matches **need not be
  exhaustive**. For example, `pop` only has a `y:ys` branch, while `⊕-E` always has both branches.
* Literal lenses (`Lens::Literal`, e.g. a constant used under `~`). The checker accepts them, but
  `core.rs` reaches `out_of_scope!()`.
* Library functions declared without a body (`dup :: ~a -> a`, `consume :: a -> ()`, file I/O),
  implemented in `FlowPrelude.hs` / `linear-base`. The declared type of `dup` drops the `Dupable`
  constraint (see the comment in `examples.fl`), so the flow-level checker would accept `dup`
  at any type, and only GHC enforces the constraint.

## 6. What is now checked in Lean (`RequestProject/FlowTyping/CompilerExamples.lean`)

These programs from `examples.fl` use no base types, recursion or library functions. Each is
written as a closed `LinTm 0` and proved well typed by the Appendix A rules, at the type
declared in `examples.fl`. The type variables `a, b, …` become arbitrary plain types.

| `examples.fl` | Lean term | theorem |
|---|---|---|
| `swap ~(x, y) = ~(y, x)` : `(a,b)/(c,d) -> (b,a)/(d,c)` | `swapF` | `swapF_typing` |
| `swapPair ~(x, y) = y := x := y` : `(a, b)/(b, a) -> ()` | `swapPairF` | `swapPairF_typing` |
| `united ~x = ~()` : `~a -> ~()` | `unitedF` | `unitedF_typing` |
| `map f ~x = x := f x` : `(a -> b) -> a/b -> ()` | `mapF` | `mapF_typing` |
| `unmap f x = f ~x; x` : `(a/b -> ()) -> a -> b` | `unmapF` | `unmapF_typing` |
| `fcomp g f ~x = ~(g ~(f ~x))` : `(b/b' -> c/c') -> (a/a' -> b/b') -> a/a' -> c/c'` | `fcompF` | `fcompF_typing` |
| `fst`, `take`, `idl` (identity flow function) | `fstF`, `take`, `example_5_6_slash` (already in `Examples.lean`) | existing theorems |

Two terms are proved to be rejected by the paper's rules (§7 explains why this matters):

* `LensTy.not_pair_same_var`: for every context, `~(x, x)` has no lens typing.
* `LinTy.not_lamSlash_capture_lens`: `λy : A/A'. ~x`, where `x` is a captured outer variable,
  has no typing.

All of these build with no `sorry`. They depend only on `propext`, `Classical.choice` and
`Quot.sound` (the two rejection theorems only on `propext`).

## 7. Places where the compiler's checker accepts more than the paper

These are differences between the code and the paper. None of them means our grammar is wrong.

> **Update: all four problems are now confirmed and fixed.** Each was reproduced by running the compiler's
> `rename.rs`, `infer.rs` and `core.rs` on syntax trees, using the harness in `compiler-fixes/harness`.
> One prediction below was slightly off: `case ~x of y -> dup ~x` did not panic but was
> translated to `dup ()`. The fixes are in `compiler-fixes/flow-typing-compiler.patch`, and
> `create_files.py` now generates the fixed sources. See `compiler-fixes/README.md`. The text below
> describes the original compiler.

1. **Lens scrutinees and lens tuples thread the context instead of splitting it.** The rules
   `~⊗-I`, `~Let`, `~⊗-E` and `~⊕-E` split the input context, `Γ₁, Γ₃`. `infer_lens` and
   `infer_expr` instead thread one context through the scrutinee and then the body (or through
   one tuple component and then the next). So the checker accepts `~(x, x)`, and
   `case ~x of y -> … x …`, where the body uses `x` while `y` is a view of it. The paper
   rejects both (`LensTy.not_pair_same_var` for the first; `LinTy.not_letInLens_reuse_var` and
   `LinTy.not_caseLens_reuse_var` for the second). In `core.rs` the translation *does*
   split the context, by the free variables of the scrutinee (`Ctx::corestrict`):
   * For the `case` example, translating the body's use of `x` reaches
     `expect("variable not live!")`, so the compiler should panic instead of reporting an error.
   * For `~(x, x)`, the second component finds `x` already removed and translates it as a
     dead variable, so the generated Haskell is probably ill-typed.
2. **Flow lambdas do not check that captured variables end dead.** `~⊸-I` requires
   `Γ₂, x : A ⊢ s : T ⊣ Γ₂†, x : A'`. For plain lambdas, `core.rs` checks this
   ("lambda had unused variables at end of body"). From reading the code, this check appears
   to be what rejects `badFileUsage` in `examples.fl`. The two `Flow::Flow` branches of the `Lambda` case have no such check, and
   neither does `infer.rs`. So `\~y -> ~x` with `x` captured seems to pass both phases. The
   paper rejects it (`LinTy.not_lamSlash_capture_lens`). The generated Haskell would then refer
   to a name that is bound only inside the lambda.
3. **A lens application with a plain argument seems to be translated incorrectly.** In
   `translate_lens`, the case `Lens::App(left, ExprOrLens::Expr(right))` (a function
   `A ⊸ B/B'` applied to a plain argument and used as a lens) produces
   `let (ab, ares) = al ar in (ares () ; (ab, Γ₃))`.
   * The intended result, according to the comment in the code, is a pair `(B, B' ⊸ Γ₃°)`;
     this is a pair `(B, Γ₃°)`.
   * It also applies the residual `B' ⊸ 1` to `()`.

   This case is not used in `examples.fl`, so the shipped `Examples.hs` is not affected.
4. **`let p = ~u in t` and literal lenses pass the checker but are `out_of_scope!()` in the
   translator** (§4, §5).

## 8. Small remark on our grammar

Fig. 4 writes `false_A(s)` with a plain type for both linear and lens terms, while the
Appendix A rule types `false_T(t) : T`, where `T` may be `A/A'`. Our `LensTm.falseE` follows
Fig. 4 and carries only the first type `C` of `C/C'`, so `C'` is not fixed by the syntax. This is
allowed by the paper as written. The compiler has neither form. If uniqueness of types were ever
wanted for `λF` lens terms, the annotation could be made an `FTy`.
