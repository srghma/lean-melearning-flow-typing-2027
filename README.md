# Flow Typing: A New Lens on Linearity — Lean 4 formalisation

This is a formalisation of *Flow Typing: A New Lens on Linearity* (Wilshaw & Hutton), from `flow-typing.pdf`.
Everything builds without `sorry`, and nothing beyond Lean's standard axioms is used.

## Conventions

* Terms use de Bruijn indices and are indexed by the number of variables in scope: `Term n`
  (for `λL`) and `LinTm n` / `LensTm n` / `Tm n` (for `λF`). `Term 0` is the type of closed terms.
  Binders extend the scope, and the most recently bound variable is `var 0`. In
  `promote t₁ … tₖ for x₁ … xₖ in t`, the body has type `Term k`, so it is closed apart from the promoted variables.
* A context for `n` variables gives each position an entry: `live A` (`x : A`), `dead` (`x†`),
  or `absent` (the variable belongs to the other half of a context split `Γ₁, Γ₂`).
  Because contexts are indexed by position, the exchange rules hold automatically.

## Files (`RequestProject/FlowTyping/`)

The main article is `flow-typing.pdf`; the appendix is `flow-typing-appendix.pdf`.

| File | Contents | Paper |
|---|---|---|
| `Syntax.lean` | `Ty`, `Term`, `lensTy`, flow contexts, `(-)†`, context splits, `Γ°` | Fig. 1, Def. 3.2, Def. 4.2 |
| `LambdaL.lean` | `Lin` (conventional typing), `Flow` (flow typing) | Fig. 2, Fig. 3 |
| `Metatheory.lean` | `Flow.frame_rule`, `lin_iff_flow` | Lemma 4.7, Theorem 4.6 (= Lemma B.4) |
| `Translation.lean` | `Flow.lens_exists`: every flow judgement is a closed lens `(Γ₁°, Γ₂°) → (A, 1)` | §4.1 |
| `AppendixB.lean` | `Flow.dead_preserved`, `Flow.occurs_iff_usedUp`, `Flow.restrict_free`, `Flow.unique` | Lemmas B.1, B.2, B.3, B.5 |
| `LambdaF.lean` | syntax and typing of `λF` (`PTy`, `FTy`, `LinTm`, `LensTm`, `Tm`, `LinTy`, `LensTy`, `TmTy`) | Fig. 4, §5, Appendix A |
| `LambdaFMeta.lean`, `LambdaFFrame.lean` | framing, strengthening, `LinTy.frame_rule`, `LensTy.frame_rule` | Lemma 5.13 |
| `Embedding.lean` | `(-)°` on `λF` types, `Ty.toP_circ` (`B° = B`), `Lin.toLambdaF` | Theorem 7.2 (syntactic part) |
| `Examples.lean` | the lenses of §3 and Examples 5.2, 5.3, 5.6, 5.7, 5.10, 5.11 | §3, §5 |
| `Substitution.lean` | simultaneous substitution on `Term`, substitution lemma `Lin.subst` | used in Appendix D |
| `Semantics.lean` | values `IsValue`, big-step semantics `Eval`, `Eval.deterministic` | D.1, Prop. D.1, Lemma D.2 |
| `LogicalRelation.lean` | `LR.V`, `LR.T`, `LR.C`, `LR.Sem`; `V.wellTyped`, `sem_closed_iff`, symmetry, transitivity | Def. D.2, Lemmas D.3, D.4, D.6, D.7 |
| `Fundamental.lean` | `LR.fundamental`, `LR.sem_eval`, `type_safety` | Theorem D.5, Lemma D.9, Prop. 7.1 |
| `Congruence.lean` | `LR.Cong` (closure of `≈` under every typing rule), `LR.Cong.sem` | Theorem D.8 |
| `Category.lean` | the category `LR.LCat` of types and terms modulo `≈` | Prop. D.10 |
| `ContextIso.lean` | context isomorphisms `Γ ≅ Γ₁ ⊗ Γ₂` for splits, removing a variable | Def. C.1 |
| `Checker.lean` | a verified type checker for `λL` (`check_sound`), inhabitation `Inh` | used for Appendix C |
| `LensCombinators.lean` | closed `λL` terms used as lens combinators | Appendix C |
| `CompilerExamples.lean` | programs from the reference compiler's `examples.fl` (`swap`, `swapPair`, `united`, `map`, `unmap`, `fcomp`) typed in `λF`; `~(x, x)`, `λy : A/A'. ~x` (with `x` captured), `let y = ~x in x` and `case ~x of …` using `x` in a branch are not typable | comparison with the compiler, see `COMPILER_COMPARISON.md` |
| `LensTranslation.lean` | `LinTy.lensTrans`, `LensTy.lensTrans`, `TmTy.lensTrans` | Theorem C.2 |

## Deviations from the paper and gaps

* **Lemma 4.7** is proved without the hypothesis that `x` is not free in `t`, because it is not needed for `λL`.
  **Lemma 5.13** keeps that hypothesis, and it is needed there: in `λF` a dead variable can be brought back to life and used again.
* **The `λF` typing rules** follow Appendix A, including the flow `0`-elimination rule with a lens scrutinee.
  Rules for `inr` are included alongside the `inl` rules. `~1-E` is the nullary case of `~⊗-E`.
* **Theorem C.2** is stated as an existence result: for every `λF` judgement there is a closed `λL` term
  of the corresponding lens type. The proof builds the term from the combinators but does not export
  the translation as a function.
* **The logical relation** has no clause for type variables in the appendix. Here `V⟦α⟧` is empty.
  So no pair of values is related at a type variable.
* **Theorem D.8** says that `≈` is an equivalence relation (`LR.sem_refl`, `LR.Sem.symm`, `LR.Sem.trans`) and a congruence.
  The congruence part is `LR.Cong.sem`: `LR.Cong` closes `≈` under every typing rule, and `LR.Cong.sem` shows this adds nothing new.
* **Not formalised:** the logical-equivalence part of Theorem 7.2, Corollary 7.3, Theorem 7.4, the remaining
  results of Appendix D after D.10 (D.11 onwards), and the string-diagram material of Appendix E. They need an explicit
  translation function and a large amount of categorical infrastructure.
  The impossibility remarks (4.4, 5.4, 5.14) rely on cut elimination for classical linear logic, so they are not formalised either.

## Comparison with the reference compiler

`COMPILER_COMPARISON.md` compares this grammar with the Rust flow-typing compiler generated by `create_files.py`.
In short, the Lean grammar matches Fig. 4 and Appendix A of the paper. The compiler implements a fragment of `λF` (no `lens`/`unlens`, no lens-bodied binders, no `0`, `&`, `⊤`, `!`), extended with base types, lists, recursion, polymorphic top-level definitions and nested patterns.
Its checker threads the context in a few places where the paper splits it.

## Fixes to the reference compiler

`compiler-fixes/` holds fixes that make the reference compiler (generated by `create_files.py`)
follow the `λF` rules: context splitting for lens tuples and `~` scrutinees, captured variables of
lambdas must end dead, a corrected translation of lens applications with a plain argument, and no
more crashes on `let p = ~u` or literal lenses. `create_files.py` now generates the fixed sources.
See `compiler-fixes/README.md`.
