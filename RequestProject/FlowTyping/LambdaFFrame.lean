module
public import RequestProject.FlowTyping.LambdaFMeta

/-!
# The frame rule for `λF` (Lemma 5.13)
-/

@[expose] public section

namespace FlowTyping

namespace LambdaF

/-! ## Strengthening -/

lemma FCtx.update_cons {n : ℕ} (a e : FEntry) (Γ : FCtx n) (i : Fin n) :
    Function.update (Fin.cons a Γ : FCtx (n + 1)) i.succ e = Fin.cons a (Function.update Γ i e) :=
  (Fin.cons_update _ _ _ _).symm

lemma FCtx.update_dag {n : ℕ} (Γ : FCtx n) (i : Fin n) :
    Function.update Γ.dag i .absent = FCtx.dag (Function.update Γ i .absent) := by
  funext j; by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma FCtx.Split.update_left {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) {i : Fin n}
    (h : Γ₂ i = .absent) :
    FCtx.Split (Function.update Γ i .absent) (Function.update Γ₁ i .absent) Γ₂ := fun j => by
  by_cases hj : j = i
  · subst hj; simp [h]
  · simpa [Function.update_of_ne hj] using hs j

lemma FCtx.Split.update_right {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) {i : Fin n}
    (h : Γ₁ i = .absent) :
    FCtx.Split (Function.update Γ i .absent) Γ₁ (Function.update Γ₂ i .absent) := fun j => by
  by_cases hj : j = i
  · subst hj; simp [h]
  · simpa [Function.update_of_ne hj] using hs j

lemma FCtx.Split.update_right_dag {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂.dag)
    {i : Fin n} (h : Γ₁ i = .absent) :
    FCtx.Split (Function.update Γ i .absent) Γ₁ (FCtx.dag (Function.update Γ₂ i .absent)) := by
  rw [← FCtx.update_dag]; exact hs.update_right h

/-- Case analysis on which half of a split a variable belongs to. -/
lemma FCtx.Split.side {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) (i : Fin n) :
    Γ₂ i = .absent ∨ Γ₁ i = .absent := by
  rcases hs i with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inr h1
  · exact Or.inl h1

mutual
/-- Strengthening for linear terms: a variable that does not occur can be removed. -/
theorem LinTy.strengthen {n : ℕ} {Γ Δ : FCtx n} {t : LinTm n} {A : PTy} :
    LinTy Γ t A Δ → ∀ i, ¬ t.Occurs i →
      LinTy (Function.update Γ i .absent) t A (Function.update Δ i .absent)
  | .var (i := j) hΓ, i, hx => by
    simp only [LinTm.Occurs] at hx
    rw [Function.update_comm hx]
    exact .var (by rw [Function.update_of_ne hx]; exact hΓ)
  | .assign h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    exact .assign (h₁.strengthen i hx.2) (h₂.strengthen i hx.1)
  | .unlens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · exact .unlens (hs.update_left h) h₁ h₂ (hs'.update_left (by simp [h]))
    · have e₂ := h₂.strengthen i hx.2
      rw [FCtx.update_dag] at e₂
      exact .unlens (hs.update_right h) (h₁.strengthen i hx.1) e₂ (hs'.update_right_dag h)
  | .letIn h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.strengthen i.succ hx.2
    rw [FCtx.update_cons, FCtx.update_cons] at this
    exact .letIn (h₁.strengthen i hx.1) this
  | .letInLens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · have h4 : _ := (by simpa using h₂.absent_iff i.succ : _ ↔ _).2 h
      exact .letInLens (hs.update_left h) (h₁.strengthen i hx.1) h₂ (hs'.update_left h4)
    · have h2 := (h₁.absent_iff i).2 h
      have := h₂.strengthen i.succ hx.2
      rw [FCtx.update_cons, FCtx.update_cons] at this
      exact .letInLens (hs.update_right h) h₁ this (hs'.update_right h2)
  | .lam hs h hs', i, hx => by
    simp only [LinTm.Occurs] at hx
    rcases hs.side i with h' | h'
    · exact .lam (hs.update_left h') h (hs'.update_left (by simp [h']))
    · have := h.strengthen i.succ hx
      rw [FCtx.update_cons, FCtx.update_cons, FCtx.update_dag] at this
      exact .lam (hs.update_right h') this (hs'.update_right_dag h')
  | .lamSlash hs h hs', i, hx => by
    simp only [LinTm.Occurs] at hx
    rcases hs.side i with h' | h'
    · exact .lamSlash (hs.update_left h') h (hs'.update_left (by simp [h']))
    · have := h.strengthen i.succ hx
      rw [FCtx.update_cons, FCtx.update_cons, FCtx.update_dag] at this
      exact .lamSlash (hs.update_right h') this (hs'.update_right_dag h')
  | .app h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    exact .app (h₁.strengthen i hx.1) (h₂.strengthen i hx.2)
  | .pair h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    exact .pair (h₁.strengthen i hx.1) (h₂.strengthen i hx.2)
  | .letPair h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.strengthen i.succ.succ hx.2
    rw [FCtx.update_cons, FCtx.update_cons, FCtx.update_cons, FCtx.update_cons] at this
    exact .letPair (h₁.strengthen i hx.1) this
  | .letPairLens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · have h4 : _ := (by simpa using h₂.absent_iff i.succ.succ : _ ↔ _).2 h
      exact .letPairLens (hs.update_left h) (h₁.strengthen i hx.1) h₂ (hs'.update_left h4)
    · have h2 := (h₁.absent_iff i).2 h
      have := h₂.strengthen i.succ.succ hx.2
      rw [FCtx.update_cons, FCtx.update_cons, FCtx.update_cons, FCtx.update_cons] at this
      exact .letPairLens (hs.update_right h) h₁ this (hs'.update_right h2)
  | .unit, _, _ => .unit
  | .letUnit h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    exact .letUnit (h₁.strengthen i hx.1) (h₂.strengthen i hx.2)
  | .letUnitLens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · exact .letUnitLens (hs.update_left h) (h₁.strengthen i hx.1) h₂
        (hs'.update_left ((h₂.absent_iff i).2 h))
    · exact .letUnitLens (hs.update_right h) h₁ (h₂.strengthen i hx.2)
        (hs'.update_right ((h₁.absent_iff i).2 h))
  | .inl h, i, hx => .inl (h.strengthen i hx)
  | .inr h, i, hx => .inr (h.strengthen i hx)
  | .case h₁ h₂ h₃, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    have e₂ := h₂.strengthen i.succ hx.2.1
    have e₃ := h₃.strengthen i.succ hx.2.2
    rw [FCtx.update_cons, FCtx.update_cons] at e₂ e₃
    exact .case (h₁.strengthen i hx.1) e₂ e₃
  | .caseLens hs h₁ h₂ h₃ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · have h4 : _ := (by simpa using h₂.absent_iff i.succ : _ ↔ _).2 h
      exact .caseLens (hs.update_left h) (h₁.strengthen i hx.1) h₂ h₃ (hs'.update_left h4)
    · have h2 := (h₁.absent_iff i).2 h
      have e₂ := h₂.strengthen i.succ hx.2.1
      have e₃ := h₃.strengthen i.succ hx.2.2
      rw [FCtx.update_cons, FCtx.update_cons] at e₂ e₃
      exact .caseLens (hs.update_right h) h₁ e₂ e₃ (hs'.update_right h2)
  | .falseE h, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs] at hx
    exact .falseE (h.strengthen i hx)
  | .withPair hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · exact .withPair (hs.update_left h) h₁ h₂ (hs'.update_left (by simp [h]))
    · have e₁ := h₁.strengthen i hx.1
      have e₂ := h₂.strengthen i hx.2
      rw [FCtx.update_dag] at e₁ e₂
      exact .withPair (hs.update_right h) e₁ e₂ (hs'.update_right_dag h)
  | .fst h, i, hx => .fst (h.strengthen i hx)
  | .snd h, i, hx => .snd (h.strengthen i hx)
  | .trueI h, i, hx => .trueI (h.strengthen i hx)
  | .promote (Γs := Γs) hts hb, i, hx => by
    simp only [LinTm.Occurs, not_exists] at hx
    exact .promote (Γs := fun j => Function.update (Γs j) i .absent)
      (fun j => (hts j).strengthen i (hx j)) hb
  | .discard h, i, hx => .discard (h.strengthen i hx)
  | .copy h, i, hx => .copy (h.strengthen i hx)
  | .derelict h, i, hx => .derelict (h.strengthen i hx)

/-- Strengthening for lens terms: a variable that does not occur can be removed. -/
theorem LensTy.strengthen {n : ℕ} {Γ Δ : FCtx n} {u : LensTm n} {A B : PTy} :
    LensTy Γ u A B Δ → ∀ i, ¬ u.Occurs i →
      LensTy (Function.update Γ i .absent) u A B (Function.update Δ i .absent)
  | .varLive (i := j) hΓ, i, hx => by
    simp only [LensTm.Occurs] at hx
    rw [Function.update_comm hx]
    exact .varLive (by rw [Function.update_of_ne hx]; exact hΓ)
  | .varDead (i := j) hΓ, i, hx => by
    simp only [LensTm.Occurs] at hx
    rw [Function.update_comm hx]
    exact .varDead (by rw [Function.update_of_ne hx]; exact hΓ)
  | .lens h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, not_or] at hx
    have := h₂.strengthen i.succ hx.2
    rw [FCtx.update_cons, FCtx.update_cons] at this
    exact .lens (h₁.strengthen i hx.1) this
  | .letIn h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.strengthen i.succ hx.2
    rw [FCtx.update_cons, FCtx.update_cons] at this
    exact .letIn (h₁.strengthen i hx.1) this
  | .letInLens hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · have h4 : _ := (by simpa using h₂.absent_iff i.succ : _ ↔ _).2 h
      exact .letInLens (hs.update_left h) (h₁.strengthen i hx.1) h₂ (hs'.update_left h4)
    · have h2 := (h₁.absent_iff i).2 h
      have := h₂.strengthen i.succ hx.2
      rw [FCtx.update_cons, FCtx.update_cons] at this
      exact .letInLens (hs.update_right h) h₁ this (hs'.update_right h2)
  | .app h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, not_or] at hx
    exact .app (h₁.strengthen i hx.1) (h₂.strengthen i hx.2)
  | .pair hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · exact .pair (hs.update_left h) (h₁.strengthen i hx.1) h₂
        (hs'.update_left ((h₂.absent_iff i).2 h))
    · exact .pair (hs.update_right h) h₁ (h₂.strengthen i hx.2)
        (hs'.update_right ((h₁.absent_iff i).2 h))
  | .unit, _, _ => .unit
  | .letPair h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.strengthen i.succ.succ hx.2
    rw [FCtx.update_cons, FCtx.update_cons, FCtx.update_cons, FCtx.update_cons] at this
    exact .letPair (h₁.strengthen i hx.1) this
  | .letPairLens hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · have h4 : _ := (by simpa using h₂.absent_iff i.succ.succ : _ ↔ _).2 h
      exact .letPairLens (hs.update_left h) (h₁.strengthen i hx.1) h₂ (hs'.update_left h4)
    · have h2 := (h₁.absent_iff i).2 h
      have := h₂.strengthen i.succ.succ hx.2
      rw [FCtx.update_cons, FCtx.update_cons, FCtx.update_cons, FCtx.update_cons] at this
      exact .letPairLens (hs.update_right h) h₁ this (hs'.update_right h2)
  | .letUnit h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    exact .letUnit (h₁.strengthen i hx.1) (h₂.strengthen i hx.2)
  | .letUnitLens hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · exact .letUnitLens (hs.update_left h) (h₁.strengthen i hx.1) h₂
        (hs'.update_left ((h₂.absent_iff i).2 h))
    · exact .letUnitLens (hs.update_right h) h₁ (h₂.strengthen i hx.2)
        (hs'.update_right ((h₁.absent_iff i).2 h))
  | .case h₁ h₂ h₃, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    have e₂ := h₂.strengthen i.succ hx.2.1
    have e₃ := h₃.strengthen i.succ hx.2.2
    rw [FCtx.update_cons, FCtx.update_cons] at e₂ e₃
    exact .case (h₁.strengthen i hx.1) e₂ e₃
  | .caseLens hs h₁ h₂ h₃ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    rcases hs.side i with h | h
    · have h4 : _ := (by simpa using h₂.absent_iff i.succ : _ ↔ _).2 h
      exact .caseLens (hs.update_left h) (h₁.strengthen i hx.1) h₂ h₃ (hs'.update_left h4)
    · have h2 := (h₁.absent_iff i).2 h
      have e₂ := h₂.strengthen i.succ hx.2.1
      have e₃ := h₃.strengthen i.succ hx.2.2
      rw [FCtx.update_cons, FCtx.update_cons] at e₂ e₃
      exact .caseLens (hs.update_right h) h₁ e₂ e₃ (hs'.update_right h2)
  | .falseE h, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs] at hx
    exact .falseE (h.strengthen i hx)

/-- Strengthening for terms `s ::= t | ~u`. -/
theorem TmTy.strengthen {n : ℕ} {Γ Δ : FCtx n} {s : Tm n} {T : FTy} :
    TmTy Γ s T Δ → ∀ i, ¬ s.Occurs i →
      TmTy (Function.update Γ i .absent) s T (Function.update Δ i .absent)
  | .lin h, i, hx => .lin (h.strengthen i hx)
  | .lens h, i, hx => .lens (h.strengthen i hx)
end

/-! ## Lemma 5.13 -/

lemma FCtx.overlay_single {n : ℕ} {Γ : FCtx n} {i : Fin n} (h : Γ i = .absent) (e : FEntry) :
    Γ.overlay (Function.update (fun _ => .absent) i e) = Function.update Γ i e := by
  funext j; by_cases hj : j = i
  · subst hj; simp [h]
  · simp [Function.update_of_ne hj]

lemma FCtx.disj_single {n : ℕ} {Γ : FCtx n} {i : Fin n} (h : Γ i = .absent) (e : FEntry) :
    Γ.Disj (Function.update (fun _ => .absent) i e) := fun j => by
  by_cases hj : j = i
  · subst hj; exact Or.inl h
  · right; simp [Function.update_of_ne hj]

lemma FCtx.update_update_absent {n : ℕ} {Γ : FCtx n} {i : Fin n} (h : Γ i = .absent)
    (e : FEntry) : Function.update (Function.update Γ i e) i .absent = Γ := by
  rw [Function.update_idem, Function.update_eq_self_iff.2 h.symm]

/-- **Lemma 5.13 (Frame rule), linear terms.**  Let `x` (the de Bruijn position `i`) be a
variable that is not in `Γ₁`, `Γ₂` and does not occur free in `t`.  Then
`Γ₁ ⊢ t : A ⊣ Γ₂ ⟺ Γ₁, x : B ⊢ t : A ⊣ Γ₂, x : B ⟺ Γ₁, x† ⊢ t : A ⊣ Γ₂, x†`. -/
theorem LinTy.frame_rule {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t : LinTm n} {A : PTy} {i : Fin n}
    (h₁ : Γ₁ i = .absent) (h₂ : Γ₂ i = .absent) (hx : ¬ t.Occurs i) (B : PTy) :
    (LinTy Γ₁ t A Γ₂ ↔
      LinTy (Function.update Γ₁ i (.live B)) t A (Function.update Γ₂ i (.live B))) ∧
    (LinTy Γ₁ t A Γ₂ ↔
      LinTy (Function.update Γ₁ i .dead) t A (Function.update Γ₂ i .dead)) := by
  have key : ∀ e : FEntry,
      (LinTy Γ₁ t A Γ₂ ↔ LinTy (Function.update Γ₁ i e) t A (Function.update Γ₂ i e)) := by
    intro e
    constructor
    · intro h
      have := h.frame _ (FCtx.disj_single h₁ e)
      rwa [FCtx.overlay_single h₁, FCtx.overlay_single h₂] at this
    · intro h
      have := h.strengthen i hx
      rwa [FCtx.update_update_absent h₁, FCtx.update_update_absent h₂] at this
  exact ⟨key _, key _⟩

/-- **Lemma 5.13 (Frame rule), lens terms.**  Let `x` (the de Bruijn position `i`) be a
variable that is not in `Γ₁`, `Γ₂` and does not occur free in `u`.  Then
`Γ₁ ⊢ u : A/A' ⊣ Γ₂ ⟺ Γ₁, x : B ⊢ u : A/A' ⊣ Γ₂, x : B ⟺ Γ₁, x† ⊢ u : A/A' ⊣ Γ₂, x†`. -/
theorem LensTy.frame_rule {n : ℕ} {Γ₁ Γ₂ : FCtx n} {u : LensTm n} {A A' : PTy} {i : Fin n}
    (h₁ : Γ₁ i = .absent) (h₂ : Γ₂ i = .absent) (hx : ¬ u.Occurs i) (B : PTy) :
    (LensTy Γ₁ u A A' Γ₂ ↔
      LensTy (Function.update Γ₁ i (.live B)) u A A' (Function.update Γ₂ i (.live B))) ∧
    (LensTy Γ₁ u A A' Γ₂ ↔
      LensTy (Function.update Γ₁ i .dead) u A A' (Function.update Γ₂ i .dead)) := by
  have key : ∀ e : FEntry,
      (LensTy Γ₁ u A A' Γ₂ ↔
        LensTy (Function.update Γ₁ i e) u A A' (Function.update Γ₂ i e)) := by
    intro e
    constructor
    · intro h
      have := h.frame _ (FCtx.disj_single h₁ e)
      rwa [FCtx.overlay_single h₁, FCtx.overlay_single h₂] at this
    · intro h
      have := h.strengthen i hx
      rwa [FCtx.update_update_absent h₁, FCtx.update_update_absent h₂] at this
  exact ⟨key _, key _⟩

end LambdaF

end FlowTyping
