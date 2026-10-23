# Summary of changes for run 5758da02-9205-4b8c-b43b-1bbc584c7ea3
I used the appendix (`flow-typing-appendix.pdf`) to formalise much more of the paper, keeping the same conventions: de Bruijn terms `Term n` with `.var : Fin n → Term n`, and `Term 0` for closed terms. The whole project builds with no `sorry`. For the main new results I checked the axioms: only Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`) are used.

**New from the appendix (all in `RequestProject/FlowTyping/`)**
- **Appendix A:** I compared the `λF` rules with the full listing and added the one that was missing, the flow `0`-elimination rule with a lens scrutinee (`LambdaF.lean`).
- **Appendix B** (`AppendixB.lean`):
  - B.1: dead variables stay dead.
  - B.2: a variable occurs free exactly when it goes from live to dead.
  - B.3: restricting a judgement to its free variables.
  - B.5: the type and output context are unique.
  - B.4 is the existing Theorem 4.6.
- **Appendix C:**
  - Def. C.1, the context isomorphisms, is in `ContextIso.lean`.
  - **Theorem C.2** (`LensTranslation.lean`): every `λF` judgement is realised by a closed, well-typed `λL` lens term. It is stated as an existence result, not as a translation function you can run. The term is built from closed combinators in `LensCombinators.lean`, and a verified type checker (`Checker.lean`) is used to type-check them.
- **Appendix D:**
  - `Substitution.lean` adds substitution and its typing lemma.
  - `Semantics.lean`: the big-step semantics, determinism (Prop. D.1) and Lemma D.2.
  - `LogicalRelation.lean`: the logical relation (Def. D.2) and Lemmas D.3, D.4, D.6 and D.7.
  - `Fundamental.lean`: the fundamental theorem (D.5), Lemma D.9 and **type safety (Prop. 7.1)**.
  - `Congruence.lean`: **Theorem D.8**. The relation `≈` is an equivalence relation, and closing it under every typing rule adds no new pairs, so it is a congruence.
  - `Category.lean`: **Prop. D.10**. It builds a Mathlib category whose objects are types and whose morphisms are closed terms of type \(A \multimap B\) up to `≈`.

**Not formalised:** the semantic part of Theorem 7.2, Corollary 7.3, Theorem 7.4, Appendix D from D.11 onwards, and the string diagrams of Appendix E. These need an explicit translation function and a lot of category-theory infrastructure. The impossibility remarks (4.4, 5.4, 5.14) are also still not formalised.

**Differences from the paper:**
- The appendix gives no case of the logical relation for type variables; I made it empty, so no values are related at a type variable.
- I added typing rules for `inr` alongside the `inl` rules.

`README.md` now has the full file table and these notes. The Properties table has new rows for these results, all marked proved, and updated comments on the existing `λF` and Theorem 7.2 rows. All work is committed and pushed, and the Lean files, build configuration and README are published.