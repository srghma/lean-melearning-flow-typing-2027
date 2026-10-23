module
public import RequestProject.FlowTyping.Translation

/-!
# Parallel substitution for `λL`

Parallel substitution `Term.subst σ t` of de Bruijn terms, its algebraic laws, and the
substitution lemma for the conventional type system (`Lin.subst`).  These are the
prerequisites for the big-step semantics of Appendix D.1, whose rules substitute values for
bound variables (`t[v/x]`).
-/

@[expose] public section

namespace FlowTyping

/-! ## Renaming laws -/

lemma liftRen_comp {n m l : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin l) :
    liftRen ρ' ∘ liftRen ρ = liftRen (ρ' ∘ ρ) := by
  funext i; cases i using Fin.cases <;> rfl

lemma liftRen_id {n : ℕ} : liftRen (id : Fin n → Fin n) = id := by
  funext i; cases i using Fin.cases <;> rfl

lemma Term.rename_rename {n : ℕ} (t : Term n) :
    ∀ {m l : ℕ} (ρ : Fin n → Fin m) (ρ' : Fin m → Fin l),
      (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ) := by
  induction t with
  | promote k ts t ih => intro m l ρ ρ'; simp only [Term.rename, ih]
  | _ => intros; simp_all [Term.rename, liftRen_comp]

lemma Term.rename_id {n : ℕ} (t : Term n) : t.rename id = t := by
  induction t with
  | promote k ts t ih => simp only [Term.rename, ih]
  | _ => simp_all [Term.rename, liftRen_id]

/-! ## Substitution -/

/-- Lifting a substitution under a binder. -/
def liftSub {n m : ℕ} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cases (.var 0) (fun i => (σ i).shift)

@[simp] lemma liftSub_zero {n m : ℕ} (σ : Fin n → Term m) : liftSub σ 0 = .var 0 := rfl
@[simp] lemma liftSub_succ {n m : ℕ} (σ : Fin n → Term m) (i : Fin n) :
    liftSub σ i.succ = (σ i).shift := rfl

/-- Parallel substitution `t[σ]`: the variable `i` is replaced by `σ i`. -/
def Term.subst : {n m : ℕ} → (Fin n → Term m) → Term n → Term m
  | _, _, σ, .var i => σ i
  | _, _, σ, .letIn t₁ t₂ => .letIn (t₁.subst σ) (t₂.subst (liftSub σ))
  | _, _, σ, .lam A t => .lam A (t.subst (liftSub σ))
  | _, _, σ, .app t₁ t₂ => .app (t₁.subst σ) (t₂.subst σ)
  | _, _, σ, .pair t₁ t₂ => .pair (t₁.subst σ) (t₂.subst σ)
  | _, _, σ, .letPair t₁ t₂ => .letPair (t₁.subst σ) (t₂.subst (liftSub (liftSub σ)))
  | _, _, _, .unit => .unit
  | _, _, σ, .letUnit t₁ t₂ => .letUnit (t₁.subst σ) (t₂.subst σ)
  | _, _, σ, .inl A B t => .inl A B (t.subst σ)
  | _, _, σ, .inr A B t => .inr A B (t.subst σ)
  | _, _, σ, .case t t₁ t₂ => .case (t.subst σ) (t₁.subst (liftSub σ)) (t₂.subst (liftSub σ))
  | _, _, σ, .falseE B t => .falseE B (t.subst σ)
  | _, _, σ, .withPair t₁ t₂ => .withPair (t₁.subst σ) (t₂.subst σ)
  | _, _, σ, .fst t => .fst (t.subst σ)
  | _, _, σ, .snd t => .snd (t.subst σ)
  | _, _, σ, .trueI t => .trueI (t.subst σ)
  | _, _, σ, .promote k ts t => .promote k (fun j => (ts j).subst σ) t
  | _, _, σ, .discard t => .discard (t.subst σ)
  | _, _, σ, .copy t => .copy (t.subst σ)
  | _, _, σ, .derelict t => .derelict (t.subst σ)

lemma liftSub_liftRen {n m l : ℕ} (σ : Fin m → Term l) (ρ : Fin n → Fin m) :
    liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ) := by
  funext i; cases i using Fin.cases <;> rfl

lemma Term.subst_rename {n : ℕ} (t : Term n) :
    ∀ {m l : ℕ} (ρ : Fin n → Fin m) (σ : Fin m → Term l),
      (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
  induction t with
  | promote k ts t ih => intro m l ρ σ; simp only [Term.rename, Term.subst, ih]
  | _ => intros; simp_all [Term.rename, Term.subst, liftSub_liftRen]

lemma liftRen_liftSub {n m l : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin l) :
    (fun i => (liftSub σ i).rename (liftRen ρ)) = liftSub (fun i => (σ i).rename ρ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [liftSub_succ, Term.shift, Term.rename_rename]
    rfl

lemma Term.rename_subst {n : ℕ} (t : Term n) :
    ∀ {m l : ℕ} (σ : Fin n → Term m) (ρ : Fin m → Fin l),
      (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
  induction t with
  | promote k ts t ih => intro m l σ ρ; simp only [Term.rename, Term.subst, ih]
  | _ => intros; simp_all [Term.rename, Term.subst, liftRen_liftSub]

lemma liftSub_liftSub {n m l : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term l) :
    (fun i => (liftSub σ i).subst (liftSub τ)) = liftSub (fun i => (σ i).subst τ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [liftSub_succ, Term.shift, Term.subst_rename, Term.rename_subst]
    rfl

lemma Term.subst_subst {n : ℕ} (t : Term n) :
    ∀ {m l : ℕ} (σ : Fin n → Term m) (τ : Fin m → Term l),
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t with
  | promote k ts t ih => intro m l σ τ; simp only [Term.subst, ih]
  | _ => intros; simp_all [Term.subst, liftSub_liftSub]

lemma liftSub_var {n : ℕ} : liftSub (Term.var : Fin n → Term n) = Term.var := by
  funext i; cases i using Fin.cases <;> rfl

lemma Term.subst_var {n : ℕ} (t : Term n) : t.subst Term.var = t := by
  induction t with
  | promote k ts t ih => simp only [Term.subst, ih]
  | _ => simp_all [Term.subst, liftSub_var]

/-- Substituting into a closed term does nothing. -/
@[simp] lemma Term.subst_closed (t : Term 0) (σ : Fin 0 → Term 0) : t.subst σ = t := by
  have : σ = Term.var := funext fun i => i.elim0
  rw [this, Term.subst_var]

/-- Substituting closed terms into a weakened closed term does nothing. -/
lemma Term.subst_weaken {m : ℕ} (t : Term 0) (σ : Fin m → Term 0) : t.weaken.subst σ = t := by
  rw [Term.weaken, Term.subst_rename, Term.subst_closed]

/-- Substituting into a shifted term skips the first component. -/
lemma Term.subst_shift {n m : ℕ} (t : Term n) (σ : Fin (n + 1) → Term m) :
    t.shift.subst σ = t.subst (fun i => σ i.succ) := by
  rw [Term.shift, Term.subst_rename]; rfl

/-- `t[σ][v/x] = t[v, σ]` for closing substitutions. -/
lemma Term.subst_liftSub_cons {n : ℕ} (t : Term (n + 1)) (σ : Fin n → Term 0) (v : Term 0) :
    (t.subst (liftSub σ)).subst (fun _ => v) = t.subst (Fin.cons v σ) := by
  rw [Term.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => simp [Term.subst_shift]

/-- Two-variable version of `Term.subst_liftSub_cons`. -/
lemma Term.subst_liftSub₂_cons {n : ℕ} (t : Term (n + 2)) (σ : Fin n → Term 0) (v w : Term 0) :
    (t.subst (liftSub (liftSub σ))).subst ![w, v] = t.subst (Fin.cons w (Fin.cons v σ)) := by
  rw [Term.subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simp [Term.subst_shift]

/-! ## The substitution lemma for conventional typing -/

/-- `SubTyped Γ σ Δ`: the substitution `σ` maps the linear context `Γ` to `Δ`, i.e. `Δ` is the
disjoint union of contexts `Θ i`, one for each variable `i : A` of `Γ`, with `Θ i ⊢ σ i : A`. -/
def SubTyped {n m : ℕ} (Γ : LCtx n) (σ : Fin n → Term m) (Δ : LCtx m) : Prop :=
  ∃ Θ : Fin n → LCtx m, Δ.SplitN Θ ∧
    ∀ i, (Γ i = none → Θ i = LCtx.empty m) ∧ ∀ A, Γ i = some A → Lin (Θ i) (σ i) A

lemma LCtx.SplitN.eq_of_others {n k : ℕ} {Δ : LCtx n} {Θ : Fin k → LCtx n} (hs : Δ.SplitN Θ)
    (i : Fin k) (h : ∀ j, j ≠ i → Θ j = LCtx.empty n) : Δ = Θ i := by
  funext x
  rcases hs x with ⟨h1, h2⟩ | ⟨j, h1, h2⟩
  · rw [h1, h2]
  · by_cases hji : j = i
    · subst hji; exact h1.symm
    · rw [← h1, h j hji]
      have := h2 i (Ne.symm hji)
      rw [this]; rfl

lemma LCtx.SplitN.eq_empty {n k : ℕ} {Δ : LCtx n} {Θ : Fin k → LCtx n} (hs : Δ.SplitN Θ)
    (h : ∀ j, Θ j = LCtx.empty n) : Δ = LCtx.empty n := by
  funext x
  rcases hs x with ⟨h1, _⟩ | ⟨j, h1, _⟩
  · exact h1
  · rw [← h1, h j]

open Classical in
lemma SubTyped.splitN {n m k : ℕ} {Γ : LCtx n} {σ : Fin n → Term m} {Δ : LCtx m}
    (hσ : SubTyped Γ σ Δ) {Γs : Fin k → LCtx n} (hs : Γ.SplitN Γs) :
    ∃ Δs : Fin k → LCtx m, Δ.SplitN Δs ∧ ∀ l, SubTyped (Γs l) σ (Δs l) := by
  obtain ⟨Θ, hΘ, hT⟩ := hσ
  -- owner of each variable of `Γ`
  have own : ∀ i, Γ i ≠ none → ∃ l, Γs l i = Γ i ∧ ∀ l', l' ≠ l → Γs l' i = none := by
    intro i hi
    rcases hs i with ⟨h1, _⟩ | h
    · exact absurd h1 hi
    · exact h
  refine ⟨fun l x => if ∃ i, Γs l i ≠ none ∧ Θ i x ≠ none then Δ x else none, ?_, fun l => ?_⟩
  · intro x
    rcases hΘ x with ⟨h1, h2⟩ | ⟨i, h1, h2⟩
    · left; refine ⟨h1, fun l => ?_⟩
      beta_reduce; rw [if_neg]; push_neg; intro i _; exact h2 i
    · by_cases hx : Δ x = none
      · left; refine ⟨hx, fun l => by simp [hx]⟩
      · have hi : Γ i ≠ none := by
          intro hi; rw [(hT i).1 hi] at h1; exact hx h1.symm
        obtain ⟨l, hl1, hl2⟩ := own i hi
        right; refine ⟨l, ?_, fun l' hl' => ?_⟩
        · beta_reduce; rw [if_pos ⟨i, by rw [hl1]; exact hi, by rw [h1]; exact hx⟩]
        · beta_reduce; rw [if_neg]; push_neg
          intro i' hi'
          by_cases e : i' = i
          · subst e; exact absurd (hl2 l' hl') hi'
          · exact h2 i' e
  · refine ⟨fun i => if Γs l i = none then LCtx.empty m else Θ i, ?_, fun i => ⟨?_, ?_⟩⟩
    · intro x
      rcases hΘ x with ⟨h1, h2⟩ | ⟨i, h1, h2⟩
      · left; refine ⟨?_, fun i => ?_⟩
        · beta_reduce; rw [if_neg]; push_neg; intro i _; exact h2 i
        · beta_reduce; split_ifs <;> simp [LCtx.empty, h2 i]
      · by_cases hc : Γs l i = none
        · left
          refine ⟨?_, fun i' => ?_⟩
          · beta_reduce; rw [if_neg]; push_neg; intro i' hi'
            by_cases e : i' = i
            · subst e; exact absurd hc hi'
            · exact h2 i' e
          · beta_reduce; split_ifs
            · rfl
            · by_cases e : i' = i
              · subst e; contradiction
              · exact h2 i' e
        · by_cases hx : Δ x = none
          · left; refine ⟨by simp [hx], fun i' => ?_⟩
            beta_reduce; split_ifs
            · rfl
            · by_cases e : i' = i
              · subst e; rw [h1, hx]
              · exact h2 i' e
          · right; refine ⟨i, ?_, fun i' hi' => ?_⟩
            · beta_reduce; rw [if_neg hc, if_pos ⟨i, hc, by rw [h1]; exact hx⟩, h1]
            · beta_reduce; split_ifs
              · rfl
              · exact h2 i' hi'
    · intro h; simp [h]
    · intro A hA
      have hi : Γ i = some A := by
        rcases hs i with ⟨_, h2⟩ | ⟨l', h1, h2⟩
        · rw [h2 l] at hA; cases hA
        · by_cases e : l = l'
          · subst e; rw [← h1, hA]
          · rw [h2 l e] at hA; cases hA
      beta_reduce; rw [if_neg (by rw [hA]; simp)]
      exact (hT i).2 A hi

lemma LCtx.Split.toSplitN {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) :
    Γ.SplitN ![Γ₁, Γ₂] := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hn : Γ i = none
    · left; refine ⟨hn, fun j => ?_⟩
      fin_cases j <;> simp [h1, h2, hn]
    · right; refine ⟨1, by simp [h2], fun j hj => ?_⟩
      fin_cases j
      · simp [h1]
      · exact absurd rfl hj
  · by_cases hn : Γ i = none
    · left; refine ⟨hn, fun j => ?_⟩
      fin_cases j <;> simp [h1, h2, hn]
    · right; refine ⟨0, by simp [h2], fun j hj => ?_⟩
      fin_cases j
      · exact absurd rfl hj
      · simp [h1]

lemma LCtx.SplitN.toSplit {n : ℕ} {Γ : LCtx n} {Δs : Fin 2 → LCtx n} (hs : Γ.SplitN Δs) :
    Γ.Split (Δs 0) (Δs 1) := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨j, h1, h2⟩
  · left; rw [h2 0, h2 1, h1]; simp
  · fin_cases j
    · right; exact ⟨h2 1 (by decide), h1⟩
    · left; exact ⟨h2 0 (by decide), h1⟩

lemma SubTyped.split {n m : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {σ : Fin n → Term m} {Δ : LCtx m}
    (hσ : SubTyped Γ σ Δ) (hs : Γ.Split Γ₁ Γ₂) :
    ∃ Δ₁ Δ₂ : LCtx m, Δ.Split Δ₁ Δ₂ ∧ SubTyped Γ₁ σ Δ₁ ∧ SubTyped Γ₂ σ Δ₂ := by
  obtain ⟨Δs, h1, h2⟩ := hσ.splitN hs.toSplitN
  exact ⟨Δs 0, Δs 1, h1.toSplit, h2 0, h2 1⟩

lemma SubTyped.cons {n m : ℕ} {Γ : LCtx n} {σ : Fin n → Term m} {Δ : LCtx m}
    (hσ : SubTyped Γ σ Δ) (A : Ty) :
    SubTyped (Fin.cons (some A) Γ : LCtx (n + 1)) (liftSub σ) (Fin.cons (some A) Δ) := by
  obtain ⟨Θ, hΘ, hT⟩ := hσ
  refine ⟨Fin.cons (LCtx.single 0 A) (fun i => (Fin.cons none (Θ i) : LCtx (m + 1))), ?_, ?_⟩
  · intro x
    cases x using Fin.cases with
    | zero =>
      right; refine ⟨0, by simp [LCtx.single], fun j hj => ?_⟩
      cases j using Fin.cases with
      | zero => exact absurd rfl hj
      | succ j => rfl
    | succ x =>
      rcases hΘ x with ⟨h1, h2⟩ | ⟨i, h1, h2⟩
      · left; refine ⟨by simpa using h1, fun j => ?_⟩
        cases j using Fin.cases with
        | zero => simp [LCtx.single, Fin.succ_ne_zero]
        | succ j => simpa using h2 j
      · right; refine ⟨i.succ, by simpa using h1, fun j hj => ?_⟩
        cases j using Fin.cases with
        | zero => simp [LCtx.single, Fin.succ_ne_zero]
        | succ j => simpa using h2 j (fun e => hj (by rw [e]))
  · intro i
    cases i using Fin.cases with
    | zero =>
      refine ⟨fun h => by simp at h, fun B hB => ?_⟩
      simp only [Fin.cons_zero, Option.some.injEq] at hB; subst hB
      exact .var 0 A
    | succ i =>
      refine ⟨fun h => ?_, fun B hB => ?_⟩
      · simp only [Fin.cons_succ] at h ⊢
        rw [(hT i).1 h]
        funext x; cases x using Fin.cases <;> rfl
      · simp only [Fin.cons_succ] at hB ⊢
        exact ((hT i).2 B hB).shift

/-- **Substitution lemma** for the conventional type system of `λL`. -/
theorem Lin.subst {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) :
    ∀ {m : ℕ} {σ : Fin n → Term m} {Δ : LCtx m}, SubTyped Γ σ Δ → Lin Δ (t.subst σ) A := by
  induction h with
  | var i A =>
    intro m σ Δ ⟨Θ, hΘ, hT⟩
    rw [hΘ.eq_of_others i (fun j hj => (hT j).1 (by simp [LCtx.single, hj]))]
    exact (hT i).2 A (by simp [LCtx.single])
  | letIn hs _ _ ih₁ ih₂ =>
    intro m σ Δ hσ
    obtain ⟨Δ₁, Δ₂, hs', h₁, h₂⟩ := hσ.split hs
    exact .letIn hs' (ih₁ h₁) (ih₂ (h₂.cons _))
  | lam _ ih => intro m σ Δ hσ; exact .lam (ih (hσ.cons _))
  | app hs _ _ ih₁ ih₂ =>
    intro m σ Δ hσ
    obtain ⟨Δ₁, Δ₂, hs', h₁, h₂⟩ := hσ.split hs
    exact .app hs' (ih₁ h₁) (ih₂ h₂)
  | pair hs _ _ ih₁ ih₂ =>
    intro m σ Δ hσ
    obtain ⟨Δ₁, Δ₂, hs', h₁, h₂⟩ := hσ.split hs
    exact .pair hs' (ih₁ h₁) (ih₂ h₂)
  | letPair hs _ _ ih₁ ih₂ =>
    intro m σ Δ hσ
    obtain ⟨Δ₁, Δ₂, hs', h₁, h₂⟩ := hσ.split hs
    exact .letPair hs' (ih₁ h₁) (ih₂ ((h₂.cons _).cons _))
  | @unit n =>
    intro m σ Δ ⟨Θ, hΘ, hT⟩
    rw [hΘ.eq_empty (fun j => (hT j).1 rfl)]
    exact .unit
  | letUnit hs _ _ ih₁ ih₂ =>
    intro m σ Δ hσ
    obtain ⟨Δ₁, Δ₂, hs', h₁, h₂⟩ := hσ.split hs
    exact .letUnit hs' (ih₁ h₁) (ih₂ h₂)
  | inl _ ih => intro m σ Δ hσ; exact .inl (ih hσ)
  | inr _ ih => intro m σ Δ hσ; exact .inr (ih hσ)
  | case hs _ _ _ ih₁ ih₂ ih₃ =>
    intro m σ Δ hσ
    obtain ⟨Δ₁, Δ₂, hs', h₁, h₂⟩ := hσ.split hs
    exact .case hs' (ih₁ h₁) (ih₂ (h₂.cons _)) (ih₃ (h₂.cons _))
  | falseE _ ih => intro m σ Δ hσ; exact .falseE (ih hσ)
  | withPair _ _ ih₁ ih₂ => intro m σ Δ hσ; exact .withPair (ih₁ hσ) (ih₂ hσ)
  | fst _ ih => intro m σ Δ hσ; exact .fst (ih hσ)
  | snd _ ih => intro m σ Δ hσ; exact .snd (ih hσ)
  | trueI _ ih => intro m σ Δ hσ; exact .trueI (ih hσ)
  | promote hs _ hb ih _ =>
    intro m σ Δ hσ
    obtain ⟨Δs, hs', hΔ⟩ := hσ.splitN hs
    exact .promote hs' (fun j => ih j (hΔ j)) hb
  | discard _ ih => intro m σ Δ hσ; exact .discard (ih hσ)
  | copy _ ih => intro m σ Δ hσ; exact .copy (ih hσ)
  | derelict _ ih => intro m σ Δ hσ; exact .derelict (ih hσ)

/-- Closing a well-typed term with well-typed closed terms gives a well-typed closed term. -/
theorem Lin.subst_closed {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A)
    {γ : Fin n → Term 0} (hγ : ∀ i A, Γ i = some A → Lin (LCtx.empty 0) (γ i) A) :
    Lin (LCtx.empty 0) (t.subst γ) A :=
  h.subst ⟨fun _ => LCtx.empty 0, fun _ => Or.inl ⟨rfl, fun _ => rfl⟩,
    fun i => ⟨fun _ => rfl, hγ i⟩⟩

end FlowTyping
