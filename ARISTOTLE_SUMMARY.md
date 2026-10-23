# Summary of changes for run 6c2b81aa-2cee-4528-97d4-82eefadf9539
I've formalised Sections 2–5 of *Flow Typing: A New Lens on Linearity* in Lean 4, plus the syntactic parts of Theorem 7.2. The project builds with no `sorry` and uses only Lean's standard axioms. Section 7's semantic results are not formalised, because the semantics they rely on is only in an appendix that isn't in the PDF.

**Conventions (as you asked).** Terms use de Bruijn indices and are indexed by a natural number: `Term n` for the linear calculus `λL`, and `LinTm n` / `LensTm n` / `Tm n` for the flow calculus `λF`. Variables are `.var : Fin n → Term n`, so `Term 0` is the type of closed terms, and `var 0` is the most recently bound variable. In `promote … for x₁…xₖ in t` the body has type `Term k`, so it is closed apart from the promoted variables. A context gives each position an entry: `live A` (`x : A`), `dead` (`x†`), or `absent`. `absent` is how a context split `Γ₁, Γ₂` is expressed without names, and the exchange rules hold automatically.

**What's proved** (all in `RequestProject/FlowTyping/`):
- **Definitions:** the syntax of `λL` (Fig. 1), its conventional typing `Lin` (Fig. 2), flow typing `Flow` (Fig. 3), the lens type (Def. 3.2), and `Γ°`.
- **Theorem 4.6** (`lin_iff_flow`): `Γ ⊢ t : A ⟺ Γ ⊢ t : A ⊣ Γ†`, with corollaries for closed terms and for contexts where every variable is in scope.
- **Lemma 4.7** (`Flow.frame_rule`): both equivalences. I dropped the paper's "x not free in t" hypothesis, because it isn't needed for `λL`.
- **Section 4.1** (`Flow.lens_exists`): every `λL` flow judgement `Γ₁ ⊢ t : A ⊣ Γ₂` is realised by a closed, conventionally typed lens of type `(Γ₁°, Γ₂°) → (A, 1)`. This needed renaming lemmas, which are in `Translation.lean`.
- **`λF`:** its syntax (Fig. 4) and typing rules (Section 5), as three mutually inductive judgements.
- **Lemma 5.13** (`LinTy.frame_rule`, `LensTy.frame_rule`): for both linear and lens terms. Here the "not free" hypothesis is kept and is genuinely needed, because in `λF` a dead variable can be brought back to life and used again.
- **Theorem 7.2, syntactic part:** the `λF` type translation `(-)°`; every `λL` type satisfies `B° = B` (`Ty.toP_circ`); and every `λL` term `Γ ⊢ t : A` is a `λF` term with `Γ ⊢ t : A ⊣ Γ†` (`Lin.toLambdaF`).
- **Examples:** the first-projection and identity lenses from Section 3, and Examples 5.2, 5.3, 5.6, 5.7, 5.10 and 5.11 as checked typing derivations.

**Where I had to fill in or stop:**
- **`λF` typing rules:** the paper says the full rule listing is in an appendix, which isn't included in the PDF. I used every rule stated in Section 5 and completed the system as Section 5 describes: remaining rules copied from Fig. 3, and `~1-E` as the zero-component case of `~⊗-E`. I left out a flow `0`-elimination rule with a lens scrutinee, because the paper doesn't give its exact form.
- **Section 7 semantics:** Proposition 7.1, the logical-equivalence part of Theorem 7.2, Corollary 7.3 and Theorem 7.4 need the big-step semantics and logical relation from that same missing appendix, so they aren't formalised.
- **Impossibility remarks:** Remarks 4.4, 5.4 and 5.14 rely on cut elimination for classical linear logic, so they aren't formalised either.

`README.md` maps each file to the corresponding part of the paper and lists these deviations. All results are registered in the Properties table.