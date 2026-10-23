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

| File | Contents | Paper |
|---|---|---|
| `Syntax.lean` | `Ty`, `Term`, `lensTy`, flow contexts, `(-)†`, context splits, `Γ°` | Fig. 1, Def. 3.2, Def. 4.2 |
| `LambdaL.lean` | `Lin` (conventional typing), `Flow` (flow typing) | Fig. 2, Fig. 3 |
| `Metatheory.lean` | `Flow.frame_rule`, `lin_iff_flow` | Lemma 4.7, Theorem 4.6 |
| `Translation.lean` | `Flow.lens_exists`: every flow judgement is a closed lens `(Γ₁°, Γ₂°) → (A, 1)` | §4.1 |
| `LambdaF.lean` | syntax and typing of `λF` (`PTy`, `FTy`, `LinTm`, `LensTm`, `Tm`, `LinTy`, `LensTy`, `TmTy`) | Fig. 4, §5 |
| `LambdaFMeta.lean`, `LambdaFFrame.lean` | framing, strengthening, `LinTy.frame_rule`, `LensTy.frame_rule` | Lemma 5.13 |
| `Embedding.lean` | `(-)°` on `λF` types, `Ty.toP_circ` (`B° = B`), `Lin.toLambdaF` | Theorem 7.2 (syntactic part) |
| `Examples.lean` | the lenses of §3 and Examples 5.2, 5.3, 5.6, 5.7, 5.10, 5.11 | §3, §5 |

## Deviations from the paper and gaps

* **Lemma 4.7** is proved without the hypothesis that `x` is not free in `t`, because it is not needed for `λL`.
  **Lemma 5.13** keeps that hypothesis, and it is needed there: in `λF` a dead variable can be brought back to life and used again.
* **The `λF` typing rules.** The article gives the full rule listing only in an appendix it does not include.
  The formalisation contains every rule stated in Section 5 and completes the system in the way Section 5 describes:
  * the remaining linear-term rules are copied from Fig. 3;
  * pattern matches with a linear scrutinee and a body `s : T` follow Fig. 3;
  * `~1-E` is the nullary case of `~⊗-E`.

  It has no flow `0`-elimination rule with a lens scrutinee, because the paper does not give its exact form.
* **Section 7 is not formalised beyond its syntactic parts.** This covers Proposition 7.1, the
  logical-equivalence part of Theorem 7.2, Corollary 7.3 and Theorem 7.4. They depend on a big-step semantics and a logical relation that are only defined in the omitted appendix.
  The impossibility remarks (4.4, 5.4, 5.14) rely on cut elimination for classical linear logic, so they are not formalised either.
