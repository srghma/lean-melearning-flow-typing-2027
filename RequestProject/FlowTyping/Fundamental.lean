module
public import RequestProject.FlowTyping.LogicalRelation

/-!
# The fundamental theorem of logical relations for `λL` (Theorem D.5)

* `LR.fundamental`: if `Γ ⊢ t : A` then `Γ ⊨ t ≈ t : A` (Theorem D.5).
* `type_safety`: Proposition 7.1 — a closed term of type `A` evaluates to a unique value,
  which is again a closed term of type `A`.
* `LR.sem_eval`: Lemma D.9 — if `⊢ t : A` and `t ⇓ v` then `⊨ t ≈ v : A`.
* `LR.sem_refl`: together with `LR.Sem.symm` and `LR.Sem.trans`, `Γ ⊨ - ≈ - : A` is an
  equivalence relation on well-typed terms (the first half of Theorem D.8).
-/

@[expose] public section

namespace FlowTyping

namespace LR

lemma C.left {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) {γ₁ γ₂ : Fin n → Term 0}
    (h : C Γ γ₁ γ₂) : C Γ₁ γ₁ γ₂ := fun i A hi => by
  rcases hs i with ⟨h1, _⟩ | ⟨_, h2⟩
  · rw [h1] at hi; cases hi
  · exact h i A (h2 ▸ hi)

lemma C.right {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) {γ₁ γ₂ : Fin n → Term 0}
    (h : C Γ γ₁ γ₂) : C Γ₂ γ₁ γ₂ := fun i A hi => by
  rcases hs i with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h i A (h2 ▸ hi)
  · rw [h1] at hi; cases hi

lemma C.splitN {n k : ℕ} {Γ : LCtx n} {Γs : Fin k → LCtx n} (hs : Γ.SplitN Γs)
    {γ₁ γ₂ : Fin n → Term 0} (h : C Γ γ₁ γ₂) (j : Fin k) : C (Γs j) γ₁ γ₂ := fun i A hi => by
  rcases hs i with ⟨_, h2⟩ | ⟨j', h1, h2⟩
  · rw [h2 j] at hi; cases hi
  · by_cases e : j = j'
    · subst e; exact h i A (h1 ▸ hi)
    · rw [h2 j e] at hi; cases hi

lemma C.cons {n : ℕ} {Γ : LCtx n} {γ₁ γ₂ : Fin n → Term 0} (h : C Γ γ₁ γ₂) {A : Ty}
    {v₁ v₂ : Term 0} (hv : V A v₁ v₂) :
    C (Fin.cons (some A) Γ : LCtx (n + 1)) (Fin.cons v₁ γ₁) (Fin.cons v₂ γ₂) := fun i B hi => by
  cases i using Fin.cases with
  | zero => simp only [Fin.cons_zero, Option.some.injEq] at hi ⊢; subst hi; exact hv
  | succ i => simp only [Fin.cons_succ] at hi ⊢; exact h i B hi

lemma wellTyped_subst {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (ht : Lin Γ t A)
    {γ₁ γ₂ : Fin n → Term 0} (hγ : C Γ γ₁ γ₂) : W A (t.subst γ₁) ∧ W A (t.subst γ₂) :=
  ⟨ht.subst_closed fun i B hi => (V.wellTyped B (hγ i B hi)).1,
    ht.subst_closed fun i B hi => (V.wellTyped B (hγ i B hi)).2⟩

/-- **Theorem D.5 (fundamental theorem).** If `Γ ⊢ t : A` then `Γ ⊨ t ≈ t : A`. -/
theorem fundamental {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) :
    Sem Γ t t A := by
  induction h with
  | var i A =>
    intro γ₁ γ₂ hγ
    exact V.toT (hγ i A (by simp [LCtx.single]))
  | letIn hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.letIn hs h₁ h₂) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, hv⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ _ _ ((hγ.right hs).cons hv)
    refine ⟨hW.1, hW.2, w₁, w₂, .letIn e₁ ?_, .letIn e₂ ?_, hw⟩ <;>
      rwa [Term.subst_liftSub_cons]
  | lam h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.lam h) hγ
    refine ⟨hW.1, hW.2, _, _, .lam _ _, .lam _ _, hW.1, hW.2, _, _, rfl, rfl,
      fun w₁ w₂ hw => ?_⟩
    rw [Term.subst_liftSub_cons, Term.subst_liftSub_cons]
    exact ih _ _ (hγ.cons hw)
  | app hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.app hs h₁ h₂) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, -, -, s₁, s₂, rfl, rfl, hs'⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, a₁, a₂, f₁, f₂, ha⟩ := ih₂ γ₁ γ₂ (hγ.right hs)
    obtain ⟨-, -, b₁, b₂, g₁, g₂, hb⟩ := hs' a₁ a₂ ha
    exact ⟨hW.1, hW.2, b₁, b₂, .app e₁ f₁ g₁, .app e₂ f₂ g₂, hb⟩
  | pair hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.pair hs h₁ h₂) hγ
    obtain ⟨-, -, a₁, a₂, e₁, e₂, ha⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, b₁, b₂, f₁, f₂, hb⟩ := ih₂ γ₁ γ₂ (hγ.right hs)
    exact ⟨hW.1, hW.2, _, _, .pair e₁ f₁, .pair e₂ f₂, a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩
  | letPair hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.letPair hs h₁ h₂) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ _ _ (((hγ.right hs).cons ha).cons hb)
    refine ⟨hW.1, hW.2, w₁, w₂, .letPair e₁ ?_, .letPair e₂ ?_, hw⟩ <;>
      rwa [Term.subst_liftSub₂_cons]
  | unit =>
    intro γ₁ γ₂ hγ
    exact ⟨.unit, .unit, _, _, .unit, .unit, rfl, rfl⟩
  | letUnit hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.letUnit hs h₁ h₂) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, rfl, rfl⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ γ₁ γ₂ (hγ.right hs)
    exact ⟨hW.1, hW.2, w₁, w₂, .letUnit e₁ f₁, .letUnit e₂ f₂, hw⟩
  | @inl _ _ _ _ B h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (Lin.inl (B := B) h) hγ
    obtain ⟨-, -, a₁, a₂, e₁, e₂, ha⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .inl _ _ e₁, .inl _ _ e₂, Or.inl ⟨a₁, a₂, rfl, rfl, ha⟩⟩
  | @inr _ _ _ A _ h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (Lin.inr (A := A) h) hγ
    obtain ⟨-, -, a₁, a₂, e₁, e₂, ha⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .inr _ _ e₁, .inr _ _ e₂, Or.inr ⟨a₁, a₂, rfl, rfl, ha⟩⟩
  | case hs h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.case hs h₁ h₂ h₃) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, hv⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    rcases hv with ⟨a₁, a₂, rfl, rfl, ha⟩ | ⟨a₁, a₂, rfl, rfl, ha⟩
    · obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ _ _ ((hγ.right hs).cons ha)
      refine ⟨hW.1, hW.2, w₁, w₂, .caseInl e₁ ?_, .caseInl e₂ ?_, hw⟩ <;>
        rwa [Term.subst_liftSub_cons]
    · obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₃ _ _ ((hγ.right hs).cons ha)
      refine ⟨hW.1, hW.2, w₁, w₂, .caseInr e₁ ?_, .caseInr e₂ ?_, hw⟩ <;>
        rwa [Term.subst_liftSub_cons]
  | falseE h ih =>
    intro γ₁ γ₂ hγ
    obtain ⟨-, -, v₁, v₂, -, -, hv⟩ := ih γ₁ γ₂ hγ
    exact hv.elim
  | withPair h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.withPair h₁ h₂) hγ
    exact ⟨hW.1, hW.2, _, _, .withPair _ _, .withPair _ _, _, _, _, _, rfl, rfl,
      ih₁ γ₁ γ₂ hγ, ih₂ γ₁ γ₂ hγ⟩
  | fst h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.fst h) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, b₁, a₂, b₂, rfl, rfl, ha, -⟩ := ih γ₁ γ₂ hγ
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ha
    exact ⟨hW.1, hW.2, w₁, w₂, .fst e₁ f₁, .fst e₂ f₂, hw⟩
  | snd h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.snd h) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, b₁, a₂, b₂, rfl, rfl, -, hb⟩ := ih γ₁ γ₂ hγ
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := hb
    exact ⟨hW.1, hW.2, w₁, w₂, .snd e₁ f₁, .snd e₂ f₂, hw⟩
  | trueI h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.trueI h) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, hv⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .trueI e₁, .trueI e₂, .trueI (V.wellTyped _ hv).1,
      .trueI (V.wellTyped _ hv).2, v₁, v₂, (V.isValue _ hv).1, (V.isValue _ hv).2, rfl, rfl⟩
  | @promote n k Γ Γs ts t As B hs hts hb ihs ihb =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.promote hs hts hb) hγ
    have key : ∀ j, ∃ a₁ a₂ : Term 0, Eval ((ts j).subst γ₁) a₁.bang ∧
        Eval ((ts j).subst γ₂) a₂.bang ∧ TT (V (As j)) (As j) a₁ a₂ := by
      intro j
      obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, ha⟩ := ihs j γ₁ γ₂ (hγ.splitN hs j)
      exact ⟨a₁, a₂, e₁, e₂, ha⟩
    choose a₁ a₂ e₁ e₂ ha using key
    have hC : C (fun j => some (Ty.bang (As j))) (fun j => (a₁ j).bang) (fun j => (a₂ j).bang) :=
      fun j A hj => by
        simp only [Option.some.injEq] at hj; subst hj
        exact ⟨a₁ j, a₂ j, rfl, rfl, ha j⟩
    exact ⟨hW.1, hW.2, _, _, .promote a₁ e₁, .promote a₂ e₂, _, _, rfl, rfl, ihb _ _ hC⟩
  | discard h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.discard h) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, -⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .discard e₁, .discard e₂, rfl, rfl⟩
  | copy h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.copy h) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, ha⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .copy e₁, .copy e₂, _, _, _, _, rfl, rfl,
      ⟨a₁, a₂, rfl, rfl, ha⟩, ⟨a₁, a₂, rfl, rfl, ha⟩⟩
  | derelict h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst (.derelict h) hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, ha⟩ := ih γ₁ γ₂ hγ
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ha
    exact ⟨hW.1, hW.2, w₁, w₂, .derelict e₁ f₁, .derelict e₂ f₂, hw⟩

/-- Reflexivity of `Γ ⊨ - ≈ - : A` on well-typed terms (Theorem D.8, with `LR.Sem.symm` and
`LR.Sem.trans`). -/
theorem sem_refl {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) : Sem Γ t t A :=
  fundamental h

/-- A closed well-typed term is related to itself. -/
theorem T.refl {t : Term 0} {A : Ty} (h : Lin (LCtx.empty 0) t A) : T A t t :=
  (sem_closed_iff t t A).1 (fundamental h)

/-- **Lemma D.9.** If `⊢ t : A` and `t ⇓ v`, then `⊨ t ≈ v : A`. -/
theorem sem_eval {t v : Term 0} {A : Ty} (h : Lin (LCtx.empty 0) t A) (he : Eval t v) :
    Sem (LCtx.empty 0) t v A := by
  rw [sem_closed_iff]
  obtain ⟨ht, -, v₁, v₂, e₁, -, hv⟩ := T.refl h
  rw [← e₁.deterministic he]
  have hv' : V A v₁ v₁ := V.trans A hv (V.symm A hv)
  exact ⟨ht, (V.wellTyped A hv').1, v₁, v₁, e₁, (V.isValue A hv').1.eval_self, hv'⟩

end LR

/-- **Proposition 7.1 (type safety).** If `t` is a closed term of type `A`, then there is a
unique value `v` with `t ⇓ v`, and `v` is again a closed term of type `A`. -/
theorem type_safety {t : Term 0} {A : Ty} (h : Lin (LCtx.empty 0) t A) :
    ∃ v, Eval t v ∧ IsValue v ∧ Lin (LCtx.empty 0) v A ∧ ∀ v', Eval t v' → v' = v := by
  obtain ⟨-, -, v, v', e, -, hv⟩ := LR.T.refl h
  exact ⟨v, e, (LR.V.isValue A hv).1, (LR.V.wellTyped A hv).1,
    fun v' e' => (e.deterministic e').symm⟩

end FlowTyping
