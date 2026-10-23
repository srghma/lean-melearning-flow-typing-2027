# Summary of changes for run 78fed132-f3ab-4aae-8199-3df816867df6
I took "fix it" to mean the four compiler bugs suspected in the last report. All four are now confirmed and fixed. I couldn't build the full compiler or compile its Haskell output, though, because crates.io and GHC weren't available here.

**How I tested.** The compiler's lexer and parser need packages from crates.io, so I wrote a small test program in `compiler-fixes/harness/`. Each test is a program written directly as a parsed syntax tree, which then goes through the compiler's real `rename.rs`, `infer.rs` and `core.rs`. There are 15 tests:
- With the original sources, 6 fail. That confirms all four bugs.
- With the fixed sources, all 15 pass.
- The 7 regression tests cover the programs from `examples.fl` listed in `compiler-fixes/README.md`. Their translations match the shipped `flow/Examples.hs`, and `badFileUsage` is still rejected.

I checked the generated Haskell by reading it, not by compiling it.

**What was wrong and how it's fixed** (only `src/infer.rs` and `src/core.rs` change):
1. **Context not split.** The paper splits the context for lens tuples and for `~` scrutinees; the compiler didn't.
   - `~(x, x)` was accepted and produced ill-typed Haskell. Now a variable may appear in only one part of a lens tuple.
   - In `case ~u of …` and `let p = ~u in …`, the body could use the variables of `u`. The `case` form produced `dup ()`, and the `let` form crashed the compiler. (The earlier report predicted a crash for `case` too; it actually produced bad output instead.) Now this is a type error.
2. **Captured variables left live.** `\~y -> ~x`, with `x` captured, was accepted, and the output contained an unsolved type variable `?7`. Now every variable a lambda captures must be used up by the end of its body.
3. **Wrong translation of a lens application with a plain argument.** A function of type `A ⊸ B/B'` applied to a plain argument, used as a lens, produced `(ab, Γ₃)` and applied the leftover function to `()`. It now produces `(ab, \bp -> ares bp; Γ₃)`, of type \(B \otimes (B' \multimap \Gamma_3)\).
4. **Crashes on accepted programs.** `let p = ~u in t` passed the type checker but crashed the translator. It is now translated as a one-branch `case ~u of p -> t`. Literal lenses such as `inc ~3` also crashed the translator; they are now a type error, since the paper has no rule for them.

**Files**
- `compiler-fixes/flow-typing-compiler.patch`: the diff against the original sources.
- `create_files.py` now generates the fixed `infer.rs` and `core.rs`; every other generated file is unchanged.
- `compiler-fixes/regressions.fl`: the test programs in surface syntax, for running with the real compiler.
- `compiler-fixes/README.md`: details and before/after outputs.
- I updated `COMPILER_COMPARISON.md` §7 and `README.md`.

**Lean.** I added two theorems to `RequestProject/FlowTyping/CompilerExamples.lean`:
- `LinTy.not_letInLens_reuse_var`: `let y = ~x in x` can't be typed.
- `LinTy.not_caseLens_reuse_var`: the same for `case ~x of …` when a branch uses `x`.

Together with the existing `not_pair_same_var` and `not_lamSlash_capture_lens`, there is now a theorem behind each type-checker fix. The project builds with no `sorry`, and the new theorems use only the `propext` axiom. I added one row for them to the Properties table, marked proved, and updated the comments on the two existing compiler rows. Everything is committed and pushed.