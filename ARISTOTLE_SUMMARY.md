# Summary of changes for run 5532afc0-823d-4cec-b570-243a6a283227
Our Lean grammar for `λF` is correct with respect to the paper. `LinTm`, `LensTm` and `Tm` match Fig. 4 constructor for constructor, and the typing rules match Appendix A. Comparing it with the compiler found nothing that needs to change on the Lean side. The full write-up is in `COMPILER_COMPARISON.md`.

I compared by reading the compiler's Rust source. I did not build or run it, because its crate dependencies could not be downloaded here. So everything below about how the compiler behaves comes from reading the code; only the Lean results are machine-checked.

**What matches**
- **Binders:** the compiler uses de Bruijn indices with the same convention as ours: the most recent binder is index 0, and a tuple pattern `(x, y)` binds `y = 0`, `x = 1`.
- **Type translation:** the compiler maps flow function types to Haskell types exactly as our `PTy.circ` does.
- **Rules:** every `λF` construct the compiler implements is one of our constructors, with the same evaluation order. This covers variables (live and dead), `:=`, both kinds of application, both kinds of lambda, tuples, let / pattern binding with plain or `~` scrutinee, `Left`/`Right`, and `case` / `case ~`.

**Where they differ**
- **Missing from the compiler:** `lens x ← t₁ in t₂`, `unlens`, let/case with a lens body, and `0`, `&`, `⊤`, `!`. Our grammar still needs the lens-bodied binders: a flow parameter like `fst ~(x, y) = ~x` means `λz. let (x, y) = ~z in ~x`.
- **Added by the compiler:** base types, lists, general recursion, polymorphic reusable top-level definitions, nested patterns that need not cover every case, and literal lenses. Our type-safety result says nothing about recursive or partial programs.

**Checked in Lean** (new file `RequestProject/FlowTyping/CompilerExamples.lean`; it builds with no `sorry` and uses only Lean's standard axioms)
- Six programs from `examples.fl` typecheck in our `λF` at the types declared there: `swap`, `swapPair`, `united`, `map`, `unmap` and `fcomp`.
- `LensTy.not_pair_same_var`: the lens tuple `~(x, x)` has no typing in any context.
- `LinTy.not_lamSlash_capture_lens`: `λy : A/A'. ~x`, with `x` captured from outside, has no typing.

**Likely problems in the compiler** (found by reading the code, not confirmed by running it)
1. Its type checker threads the context through lens tuples and `~` scrutinees, where the paper splits it. So it appears to accept `~(x, x)` and `case ~x of y -> … x …`. Its translation step does split the context, so the first probably produces ill-typed Haskell and the second should crash the compiler rather than give an error.
2. Flow lambdas are never checked to leave captured variables dead (plain lambdas are), so `\~y -> ~x` appears to be accepted.
3. Calling a function that returns a flow type with a plain argument, in lens position, seems to be translated to a pair of the wrong form. `examples.fl` never does this, so the shipped `Examples.hs` is not affected.
4. `let p = ~u in …` and literal lenses pass the type checker but hit `out_of_scope!()`, which crashes the compiler.

One minor note on our side: for lens terms, Fig. 4 writes `false_A(s)` with a plain type, while Appendix A types it as `false_T` where `T` may be `A/A'`. Our `LensTm.falseE` follows Fig. 4. The paper as written allows this.

I also updated `README.md` and added three rows to the Properties table, all marked proved. The work is committed and pushed, and the new files are published.

## Suggested follow-up

From reading the compiler source, I suspect three bugs. First, `infer.rs` doesn't split the context for lens tuples and `~` scrutinees. Second, the flow-lambda branches in `core.rs` never check that captured variables end up dead. Third, in `translate_lens`, the case for an application with a plain argument builds `(B, Γ₃)` instead of `(B, B' ⊸ Γ₃)`. I haven't run the compiler to confirm any of these. If you'd like, I can draft fixes or small `.fl` test cases for them.