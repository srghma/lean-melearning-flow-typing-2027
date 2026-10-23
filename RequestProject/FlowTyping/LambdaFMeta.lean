module
public import RequestProject.FlowTyping.LambdaF
public import Mathlib.Tactic

/-!
# Metatheory of `λF`: the frame rule (Lemma 5.13)
-/

@[expose] public section

namespace FlowTyping

namespace LambdaF

@[simp] lemma FEntry.dag_absent : FEntry.absent.dag = .absent := rfl
@[simp] lemma FEntry.dag_dead : FEntry.dead.dag = .dead := rfl
@[simp] lemma FEntry.dag_live (A : PTy) : (FEntry.live A).dag = .dead := rfl
@[simp] lemma FEntry.dag_eq_absent {e : FEntry} : e.dag = .absent ↔ e = .absent := by
  cases e <;> simp [FEntry.dag]
@[simp] lemma FCtx.dag_apply {n : ℕ} (Γ : FCtx n) (i : Fin n) : Γ.dag i = (Γ i).dag := rfl

lemma FCtx.Split.absent_iff {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) (i : Fin n) :
    Γ i = .absent ↔ Γ₁ i = .absent ∧ Γ₂ i = .absent := by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, ← h2]

/-- Absent-preservation for the rules with two context splits. -/
lemma FCtx.split₂_absent {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} (hs : Γ.Split Γ₁ Γ₃)
    (hs' : Δ.Split Γ₂ Γ₄) (h₁ : ∀ i, Γ₂ i = .absent ↔ Γ₁ i = .absent)
    (h₂ : ∀ i, Γ₄ i = .absent ↔ Γ₃ i = .absent) (i : Fin n) :
    Δ i = .absent ↔ Γ i = .absent := by
  rw [hs.absent_iff, hs'.absent_iff, h₁, h₂]

/-- Absent-preservation for the rules whose output context is `Γ₁, Γ₂†`. -/
lemma FCtx.split_dag_absent {n : ℕ} {Γ Γ₁ Γ₂ Δ : FCtx n} (hs : Γ.Split Γ₁ Γ₂)
    (hs' : Δ.Split Γ₁ Γ₂.dag) (i : Fin n) : Δ i = .absent ↔ Γ i = .absent := by
  rw [hs.absent_iff, hs'.absent_iff]; simp

mutual
/-- The input and output contexts of a linear-term judgement contain the same variables. -/
theorem LinTy.absent_iff {n : ℕ} {Γ Δ : FCtx n} {t : LinTm n} {A : PTy} :
    LinTy Γ t A Δ → ∀ i, Δ i = .absent ↔ Γ i = .absent
  | .var (i := j) hΓ, i => by
    by_cases hij : i = j
    · subst hij; simp [hΓ]
    · simp [Function.update_of_ne hij]
  | .assign h₁ h₂, i => by rw [h₂.absent_iff, h₁.absent_iff]
  | .unlens hs _ _ hs', i => FCtx.split_dag_absent hs hs' i
  | .letIn h₁ h₂, i => by
    have := h₂.absent_iff i.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .letInLens hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff
      (fun i => by simpa using h₂.absent_iff i.succ) i
  | .lam hs _ hs', i => FCtx.split_dag_absent hs hs' i
  | .lamSlash hs _ hs', i => FCtx.split_dag_absent hs hs' i
  | .app h₁ h₂, i => by rw [h₂.absent_iff, h₁.absent_iff]
  | .pair h₁ h₂, i => by rw [h₂.absent_iff, h₁.absent_iff]
  | .letPair h₁ h₂, i => by
    have := h₂.absent_iff i.succ.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .letPairLens hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff
      (fun i => by simpa using h₂.absent_iff i.succ.succ) i
  | .unit, _ => Iff.rfl
  | .letUnit h₁ h₂, i => by rw [h₂.absent_iff, h₁.absent_iff]
  | .letUnitLens hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff h₂.absent_iff i
  | .inl h, i => h.absent_iff i
  | .inr h, i => h.absent_iff i
  | .case h₁ h₂ _, i => by
    have := h₂.absent_iff i.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .caseLens hs h₁ h₂ _ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff
      (fun i => by simpa using h₂.absent_iff i.succ) i
  | .falseE h, i => h.absent_iff i
  | .withPair hs _ _ hs', i => FCtx.split_dag_absent hs hs' i
  | .fst h, i => h.absent_iff i
  | .snd h, i => h.absent_iff i
  | .trueI h, i => h.absent_iff i
  | .promote (Γs := Γs) hts _, i => by
    have key : ∀ m : ℕ, ∀ hm : m < _ + 1, Γs ⟨m, hm⟩ i = .absent ↔ Γs 0 i = .absent := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        have := (hts ⟨m, by omega⟩).absent_iff i
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        rw [this, ih]
    exact key _ _
  | .discard h, i => h.absent_iff i
  | .copy h, i => h.absent_iff i
  | .derelict h, i => h.absent_iff i

/-- The input and output contexts of a lens-term judgement contain the same variables. -/
theorem LensTy.absent_iff {n : ℕ} {Γ Δ : FCtx n} {u : LensTm n} {A B : PTy} :
    LensTy Γ u A B Δ → ∀ i, Δ i = .absent ↔ Γ i = .absent
  | .varLive (i := j) hΓ, i => by
    by_cases hij : i = j
    · subst hij; simp [hΓ]
    · simp [Function.update_of_ne hij]
  | .varDead (i := j) hΓ, i => by
    by_cases hij : i = j
    · subst hij; simp [hΓ]
    · simp [Function.update_of_ne hij]
  | .lens h₁ h₂, i => by
    have := h₂.absent_iff i.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .letIn h₁ h₂, i => by
    have := h₂.absent_iff i.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .letInLens hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff
      (fun i => by simpa using h₂.absent_iff i.succ) i
  | .app h₁ h₂, i => by rw [h₂.absent_iff, h₁.absent_iff]
  | .pair hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff h₂.absent_iff i
  | .unit, _ => Iff.rfl
  | .letPair h₁ h₂, i => by
    have := h₂.absent_iff i.succ.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .letPairLens hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff
      (fun i => by simpa using h₂.absent_iff i.succ.succ) i
  | .letUnit h₁ h₂, i => by rw [h₂.absent_iff, h₁.absent_iff]
  | .letUnitLens hs h₁ h₂ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff h₂.absent_iff i
  | .case h₁ h₂ _, i => by
    have := h₂.absent_iff i.succ; simp only [Fin.cons_succ] at this
    rw [this, h₁.absent_iff]
  | .caseLens hs h₁ h₂ _ hs', i => FCtx.split₂_absent hs hs' h₁.absent_iff
      (fun i => by simpa using h₂.absent_iff i.succ) i
  | .falseE h, i => h.absent_iff i

/-- The input and output contexts of a judgement contain the same variables. -/
theorem TmTy.absent_iff {n : ℕ} {Γ Δ : FCtx n} {s : Tm n} {T : FTy} :
    TmTy Γ s T Δ → ∀ i, Δ i = .absent ↔ Γ i = .absent
  | .lin h, i => h.absent_iff i
  | .lens h, i => h.absent_iff i
end

end LambdaF

end FlowTyping

namespace FlowTyping

namespace LambdaF

/-! ## Framing -/

/-- Overlay of entries: `e` takes precedence unless it is absent. -/
def FEntry.overlay : FEntry → FEntry → FEntry
  | .absent, e => e
  | e, _ => e

/-- Overlay of contexts. -/
def FCtx.overlay {n : ℕ} (Γ Θ : FCtx n) : FCtx n := fun i => (Γ i).overlay (Θ i)

@[simp] lemma FEntry.overlay_absent_left (e : FEntry) : FEntry.absent.overlay e = e := rfl
@[simp] lemma FEntry.overlay_absent_right (e : FEntry) : e.overlay .absent = e := by
  cases e <;> rfl
@[simp] lemma FEntry.overlay_dead (e : FEntry) : FEntry.dead.overlay e = .dead := rfl
@[simp] lemma FEntry.overlay_live (A : PTy) (e : FEntry) : (FEntry.live A).overlay e = .live A :=
  rfl
@[simp] lemma FCtx.overlay_apply {n : ℕ} (Γ Θ : FCtx n) (i : Fin n) :
    Γ.overlay Θ i = (Γ i).overlay (Θ i) := rfl

/-- `Θ` is disjoint from `Γ`. -/
def FCtx.Disj {n : ℕ} (Γ Θ : FCtx n) : Prop := ∀ i, Γ i = .absent ∨ Θ i = .absent

lemma FCtx.cons_overlay {n : ℕ} (a : FEntry) (Γ Θ : FCtx n) :
    FCtx.overlay (Fin.cons a Γ : FCtx (n + 1)) (Fin.cons .absent Θ) =
      Fin.cons a (Γ.overlay Θ) := by
  funext i; cases i using Fin.cases <;> simp

lemma FCtx.Disj.cons {n : ℕ} {Γ Θ : FCtx n} (h : Γ.Disj Θ) (a : FEntry) :
    FCtx.Disj (Fin.cons a Γ : FCtx (n + 1)) (Fin.cons .absent Θ) := fun i => by
  cases i using Fin.cases with
  | zero => simp
  | succ i => simpa using h i

lemma FCtx.Disj.of_iff {n : ℕ} {Γ Δ Θ : FCtx n} (h : Γ.Disj Θ)
    (hΔ : ∀ i, Δ i = .absent ↔ Γ i = .absent) : Δ.Disj Θ := fun i => by
  rw [hΔ]; exact h i

lemma FCtx.Split.disj_left {n : ℕ} {Γ Γ₁ Γ₂ Θ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) (h : Γ.Disj Θ) :
    Γ₁.Disj Θ := fun i => by
  rcases h i with h' | h'
  · left; exact ((hs.absent_iff i).1 h').1
  · right; exact h'

lemma FCtx.Split.overlay_left {n : ℕ} {Γ Γ₁ Γ₂ Θ : FCtx n} (hs : Γ.Split Γ₁ Γ₂)
    (h : Γ.Disj Θ) : (Γ.overlay Θ).Split (Γ₁.overlay Θ) Γ₂ := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h i with h3 | h3 <;> simp_all

lemma FCtx.update_overlay {n : ℕ} (Γ Θ : FCtx n) (i : Fin n) (e : FEntry)
    (h : Θ i = .absent) :
    FCtx.overlay (Function.update Γ i e) Θ = Function.update (Γ.overlay Θ) i e := by
  funext j; by_cases hj : j = i
  · subst hj; simp [h]
  · simp [Function.update_of_ne hj]

mutual
/-- Framing for linear terms: variables not in the contexts can be added. -/
theorem LinTy.frame {n : ℕ} {Γ Δ : FCtx n} {t : LinTm n} {A : PTy} :
    LinTy Γ t A Δ → ∀ Θ : FCtx n, Γ.Disj Θ → LinTy (Γ.overlay Θ) t A (Δ.overlay Θ)
  | .var (i := i) hΓ, Θ, hΘ => by
    have hi : Θ i = .absent := (hΘ i).resolve_left (by simp [hΓ])
    rw [FCtx.update_overlay _ _ _ _ hi]; exact .var (by simp [hΓ])
  | .assign h₁ h₂, Θ, hΘ => .assign (h₁.frame Θ hΘ) (h₂.frame Θ (hΘ.of_iff h₁.absent_iff))
  | .unlens hs h₁ h₂ hs', Θ, hΘ =>
    .unlens (hs.overlay_left hΘ) h₁ h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split_dag_absent hs hs')))
  | .letIn h₁ h₂, Θ, hΘ => by
    have := h₂.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay] at this
    exact .letIn (h₁.frame Θ hΘ) this
  | .letInLens hs h₁ h₂ hs', Θ, hΘ =>
    .letInLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff
        (fun i => by simpa using h₂.absent_iff i.succ))))
  | .lam hs h hs', Θ, hΘ =>
    .lam (hs.overlay_left hΘ) h (hs'.overlay_left (hΘ.of_iff (FCtx.split_dag_absent hs hs')))
  | .lamSlash hs h hs', Θ, hΘ =>
    .lamSlash (hs.overlay_left hΘ) h
      (hs'.overlay_left (hΘ.of_iff (FCtx.split_dag_absent hs hs')))
  | .app h₁ h₂, Θ, hΘ => .app (h₁.frame Θ hΘ) (h₂.frame Θ (hΘ.of_iff h₁.absent_iff))
  | .pair h₁ h₂, Θ, hΘ => .pair (h₁.frame Θ hΘ) (h₂.frame Θ (hΘ.of_iff h₁.absent_iff))
  | .letPair h₁ h₂, Θ, hΘ => by
    have := h₂.frame _ (((hΘ.of_iff h₁.absent_iff).cons (.live _)).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay, FCtx.cons_overlay, FCtx.cons_overlay] at this
    exact .letPair (h₁.frame Θ hΘ) this
  | .letPairLens hs h₁ h₂ hs', Θ, hΘ =>
    .letPairLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff
        (fun i => by simpa using h₂.absent_iff i.succ.succ))))
  | .unit, _, _ => .unit
  | .letUnit h₁ h₂, Θ, hΘ => .letUnit (h₁.frame Θ hΘ) (h₂.frame Θ (hΘ.of_iff h₁.absent_iff))
  | .letUnitLens hs h₁ h₂ hs', Θ, hΘ =>
    .letUnitLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff h₂.absent_iff)))
  | .inl h, Θ, hΘ => .inl (h.frame Θ hΘ)
  | .inr h, Θ, hΘ => .inr (h.frame Θ hΘ)
  | .case h₁ h₂ h₃, Θ, hΘ => by
    have e₂ := h₂.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    have e₃ := h₃.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay] at e₂ e₃
    exact .case (h₁.frame Θ hΘ) e₂ e₃
  | .caseLens hs h₁ h₂ h₃ hs', Θ, hΘ =>
    .caseLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂ h₃
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff
        (fun i => by simpa using h₂.absent_iff i.succ))))
  | .falseE h, Θ, hΘ => .falseE (h.frame Θ hΘ)
  | .withPair hs h₁ h₂ hs', Θ, hΘ =>
    .withPair (hs.overlay_left hΘ) h₁ h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split_dag_absent hs hs')))
  | .fst h, Θ, hΘ => .fst (h.frame Θ hΘ)
  | .snd h, Θ, hΘ => .snd (h.frame Θ hΘ)
  | .trueI h, Θ, hΘ => .trueI (h.frame Θ hΘ)
  | .promote (Γs := Γs) hts hb, Θ, hΘ => by
    have key : ∀ j : Fin (_ + 1), (Γs j).Disj Θ := by
      intro ⟨m, hm⟩
      induction m with
      | zero => exact hΘ
      | succ m ih =>
        have := (hts ⟨m, by omega⟩).absent_iff
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        exact (ih (by omega)).of_iff this
    exact .promote (Γs := fun j => (Γs j).overlay Θ)
      (fun j => (hts j).frame Θ (key j.castSucc)) hb
  | .discard h, Θ, hΘ => .discard (h.frame Θ hΘ)
  | .copy h, Θ, hΘ => .copy (h.frame Θ hΘ)
  | .derelict h, Θ, hΘ => .derelict (h.frame Θ hΘ)

/-- Framing for lens terms: variables not in the contexts can be added. -/
theorem LensTy.frame {n : ℕ} {Γ Δ : FCtx n} {u : LensTm n} {A B : PTy} :
    LensTy Γ u A B Δ → ∀ Θ : FCtx n, Γ.Disj Θ → LensTy (Γ.overlay Θ) u A B (Δ.overlay Θ)
  | .varLive (i := i) hΓ, Θ, hΘ => by
    have hi : Θ i = .absent := (hΘ i).resolve_left (by simp [hΓ])
    rw [FCtx.update_overlay _ _ _ _ hi]; exact .varLive (by simp [hΓ])
  | .varDead (i := i) hΓ, Θ, hΘ => by
    have hi : Θ i = .absent := (hΘ i).resolve_left (by simp [hΓ])
    rw [FCtx.update_overlay _ _ _ _ hi]; exact .varDead (by simp [hΓ])
  | .lens h₁ h₂, Θ, hΘ => by
    have := h₂.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay] at this
    exact .lens (h₁.frame Θ hΘ) this
  | .letIn h₁ h₂, Θ, hΘ => by
    have := h₂.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay] at this
    exact .letIn (h₁.frame Θ hΘ) this
  | .letInLens hs h₁ h₂ hs', Θ, hΘ =>
    .letInLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff
        (fun i => by simpa using h₂.absent_iff i.succ))))
  | .app h₁ h₂, Θ, hΘ => .app (h₁.frame Θ hΘ) (h₂.frame Θ (hΘ.of_iff h₁.absent_iff))
  | .pair hs h₁ h₂ hs', Θ, hΘ =>
    .pair (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff h₂.absent_iff)))
  | .unit, _, _ => .unit
  | .letPair h₁ h₂, Θ, hΘ => by
    have := h₂.frame _ (((hΘ.of_iff h₁.absent_iff).cons (.live _)).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay, FCtx.cons_overlay, FCtx.cons_overlay] at this
    exact .letPair (h₁.frame Θ hΘ) this
  | .letPairLens hs h₁ h₂ hs', Θ, hΘ =>
    .letPairLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff
        (fun i => by simpa using h₂.absent_iff i.succ.succ))))
  | .letUnit h₁ h₂, Θ, hΘ => .letUnit (h₁.frame Θ hΘ) (h₂.frame Θ (hΘ.of_iff h₁.absent_iff))
  | .letUnitLens hs h₁ h₂ hs', Θ, hΘ =>
    .letUnitLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff h₂.absent_iff)))
  | .case h₁ h₂ h₃, Θ, hΘ => by
    have e₂ := h₂.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    have e₃ := h₃.frame _ ((hΘ.of_iff h₁.absent_iff).cons (.live _))
    rw [FCtx.cons_overlay, FCtx.cons_overlay] at e₂ e₃
    exact .case (h₁.frame Θ hΘ) e₂ e₃
  | .caseLens hs h₁ h₂ h₃ hs', Θ, hΘ =>
    .caseLens (hs.overlay_left hΘ) (h₁.frame Θ (hs.disj_left hΘ)) h₂ h₃
      (hs'.overlay_left (hΘ.of_iff (FCtx.split₂_absent hs hs' h₁.absent_iff
        (fun i => by simpa using h₂.absent_iff i.succ))))
  | .falseE h, Θ, hΘ => .falseE (h.frame Θ hΘ)

/-- Framing for terms `s ::= t | ~u`. -/
theorem TmTy.frame {n : ℕ} {Γ Δ : FCtx n} {s : Tm n} {T : FTy} :
    TmTy Γ s T Δ → ∀ Θ : FCtx n, Γ.Disj Θ → TmTy (Γ.overlay Θ) s T (Δ.overlay Θ)
  | .lin h, Θ, hΘ => .lin (h.frame Θ hΘ)
  | .lens h, Θ, hΘ => .lens (h.frame Θ hΘ)
end

end LambdaF

end FlowTyping

namespace FlowTyping

namespace LambdaF

/-! ## Free variables -/

mutual
/-- `LinTm.Occurs i t`: the variable `i` occurs free in the linear term `t`. -/
def LinTm.Occurs : {n : ℕ} → Fin n → LinTm n → Prop
  | _, i, .var j => j = i
  | _, i, .assign u t => u.Occurs i ∨ t.Occurs i
  | _, i, .unlens u t => u.Occurs i ∨ t.Occurs i
  | _, i, .letIn s t => s.Occurs i ∨ t.Occurs i.succ
  | _, i, .lam _ s => s.Occurs i.succ
  | _, i, .app t s => t.Occurs i ∨ s.Occurs i
  | _, i, .pair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .letPair s t => s.Occurs i ∨ t.Occurs i.succ.succ
  | _, _, .unit => False
  | _, i, .letUnit s t => s.Occurs i ∨ t.Occurs i
  | _, i, .inl _ _ t => t.Occurs i
  | _, i, .inr _ _ t => t.Occurs i
  | _, i, .case s t₁ t₂ => s.Occurs i ∨ t₁.Occurs i.succ ∨ t₂.Occurs i.succ
  | _, i, .falseE _ s => s.Occurs i
  | _, i, .withPair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .fst t => t.Occurs i
  | _, i, .snd t => t.Occurs i
  | _, i, .trueI t => t.Occurs i
  | _, i, .promote _ ts _ => ∃ j, (ts j).Occurs i
  | _, i, .discard t => t.Occurs i
  | _, i, .copy t => t.Occurs i
  | _, i, .derelict t => t.Occurs i

/-- `LensTm.Occurs i u`: the variable `i` occurs free in the lens term `u`. -/
def LensTm.Occurs : {n : ℕ} → Fin n → LensTm n → Prop
  | _, i, .var j => j = i
  | _, i, .lens t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ
  | _, i, .letIn s u => s.Occurs i ∨ u.Occurs i.succ
  | _, i, .app t s => t.Occurs i ∨ s.Occurs i
  | _, i, .pair u₁ u₂ => u₁.Occurs i ∨ u₂.Occurs i
  | _, i, .letPair s u => s.Occurs i ∨ u.Occurs i.succ.succ
  | _, _, .unit => False
  | _, i, .letUnit s u => s.Occurs i ∨ u.Occurs i
  | _, i, .case s u₁ u₂ => s.Occurs i ∨ u₁.Occurs i.succ ∨ u₂.Occurs i.succ
  | _, i, .falseE _ s => s.Occurs i

/-- `Tm.Occurs i s`: the variable `i` occurs free in the term `s`. -/
def Tm.Occurs : {n : ℕ} → Fin n → Tm n → Prop
  | _, i, .lin t => t.Occurs i
  | _, i, .lens u => u.Occurs i
end

end LambdaF

end FlowTyping

namespace FlowTyping

namespace LambdaF

/-! ## Variables that do not occur are unchanged -/

/-- Pointwise description of the output context `Γ₁, Γ₂†` of the rules `⊸-I`, `&-I` and
`Unlens`. -/
lemma FCtx.split_dag {n : ℕ} {Γ Γ₁ Γ₂ Δ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) (hs' : Δ.Split Γ₁ Γ₂.dag)
    (i : Fin n) :
    (Γ₂ i = .absent ∧ Γ₁ i = Γ i ∧ Δ i = Γ i) ∨
      (Γ₁ i = .absent ∧ Γ₂ i = Γ i ∧ Δ i = (Γ i).dag) := by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs' i with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp_all

lemma FCtx.split_dag_eq {n : ℕ} {Γ Γ₁ Γ₂ Δ : FCtx n} (hs : Γ.Split Γ₁ Γ₂)
    (hs' : Δ.Split Γ₁ Γ₂.dag) {i : Fin n} (h : (Γ₂ i).dag = Γ₂ i) : Δ i = Γ i := by
  rcases FCtx.split_dag hs hs' i with ⟨-, -, h'⟩ | ⟨-, h2, h'⟩
  · exact h'
  · rw [h', ← h2, h]

lemma FCtx.split₂_eq {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} (hs : Γ.Split Γ₁ Γ₃)
    (hs' : Δ.Split Γ₂ Γ₄) {i : Fin n} (h₁ : Γ₂ i = Γ₁ i) (h₂ : Γ₄ i = Γ₃ i) : Δ i = Γ i := by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs' i with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp_all

lemma promote_chain_eq {n k : ℕ} {Γs : Fin (k + 1) → FCtx n} {i : Fin n}
    (h : ∀ j : Fin k, Γs j.succ i = Γs j.castSucc i) (j : Fin (k + 1)) : Γs j i = Γs 0 i := by
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => rfl
  | succ m ih =>
    have := h ⟨m, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at this
    rw [this, ih]

mutual
/-- A variable that does not occur in a linear term is not changed by its judgement. -/
theorem LinTy.unchanged {n : ℕ} {Γ Δ : FCtx n} {t : LinTm n} {A : PTy} :
    LinTy Γ t A Δ → ∀ i, ¬ t.Occurs i → Δ i = Γ i
  | .var (i := j) _, i, hx => by
    simp only [LinTm.Occurs] at hx
    exact Function.update_of_ne (Ne.symm hx) _ _
  | .assign h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    rw [h₂.unchanged i hx.1, h₁.unchanged i hx.2]
  | .unlens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    have e₁ := h₁.unchanged i hx.1
    have e₂ := h₂.unchanged i hx.2
    refine FCtx.split_dag_eq hs hs' ?_
    rw [← e₁]; simpa using e₂
  | .letIn h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ hx.2; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .letInLens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1)
      (by simpa using h₂.unchanged i.succ hx.2)
  | .lam hs h hs', i, hx => by
    simp only [LinTm.Occurs] at hx
    exact FCtx.split_dag_eq hs hs' (by simpa using h.unchanged i.succ hx)
  | .lamSlash hs h hs', i, hx => by
    simp only [LinTm.Occurs] at hx
    exact FCtx.split_dag_eq hs hs' (by simpa using h.unchanged i.succ hx)
  | .app h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    rw [h₂.unchanged i hx.2, h₁.unchanged i hx.1]
  | .pair h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    rw [h₂.unchanged i hx.2, h₁.unchanged i hx.1]
  | .letPair h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ.succ hx.2; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .letPairLens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1)
      (by simpa using h₂.unchanged i.succ.succ hx.2)
  | .unit, _, _ => rfl
  | .letUnit h₁ h₂, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    rw [h₂.unchanged i hx.2, h₁.unchanged i hx.1]
  | .letUnitLens hs h₁ h₂ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1) (h₂.unchanged i hx.2)
  | .inl h, i, hx => h.unchanged i hx
  | .inr h, i, hx => h.unchanged i hx
  | .case h₁ h₂ _, i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ hx.2.1; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .caseLens hs h₁ h₂ _ hs', i, hx => by
    simp only [LinTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1)
      (by simpa using h₂.unchanged i.succ hx.2.1)
  | .falseE h, i, hx => h.unchanged i hx
  | .withPair hs h₁ _ hs', i, hx => by
    simp only [LinTm.Occurs, not_or] at hx
    exact FCtx.split_dag_eq hs hs' (by simpa using h₁.unchanged i hx.1)
  | .fst h, i, hx => h.unchanged i hx
  | .snd h, i, hx => h.unchanged i hx
  | .trueI h, i, hx => h.unchanged i hx
  | .promote (Γs := Γs) hts _, i, hx => by
    simp only [LinTm.Occurs, not_exists] at hx
    exact promote_chain_eq (fun j => (hts j).unchanged i (hx j)) _
  | .discard h, i, hx => h.unchanged i hx
  | .copy h, i, hx => h.unchanged i hx
  | .derelict h, i, hx => h.unchanged i hx

/-- A variable that does not occur in a lens term is not changed by its judgement. -/
theorem LensTy.unchanged {n : ℕ} {Γ Δ : FCtx n} {u : LensTm n} {A B : PTy} :
    LensTy Γ u A B Δ → ∀ i, ¬ u.Occurs i → Δ i = Γ i
  | .varLive (i := j) _, i, hx => by
    simp only [LensTm.Occurs] at hx
    exact Function.update_of_ne (Ne.symm hx) _ _
  | .varDead (i := j) _, i, hx => by
    simp only [LensTm.Occurs] at hx
    exact Function.update_of_ne (Ne.symm hx) _ _
  | .lens h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ hx.2; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .letIn h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ hx.2; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .letInLens hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1)
      (by simpa using h₂.unchanged i.succ hx.2)
  | .app h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, not_or] at hx
    rw [h₂.unchanged i hx.2, h₁.unchanged i hx.1]
  | .pair hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1) (h₂.unchanged i hx.2)
  | .unit, _, _ => rfl
  | .letPair h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ.succ hx.2; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .letPairLens hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1)
      (by simpa using h₂.unchanged i.succ.succ hx.2)
  | .letUnit h₁ h₂, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    rw [h₂.unchanged i hx.2, h₁.unchanged i hx.1]
  | .letUnitLens hs h₁ h₂ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1) (h₂.unchanged i hx.2)
  | .case h₁ h₂ _, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    have := h₂.unchanged i.succ hx.2.1; simp only [Fin.cons_succ] at this
    rw [this, h₁.unchanged i hx.1]
  | .caseLens hs h₁ h₂ _ hs', i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs, not_or] at hx
    exact FCtx.split₂_eq hs hs' (h₁.unchanged i hx.1)
      (by simpa using h₂.unchanged i.succ hx.2.1)
  | .falseE h, i, hx => by
    simp only [LensTm.Occurs, Tm.Occurs] at hx
    exact h.unchanged i hx

/-- A variable that does not occur in a term is not changed by its judgement. -/
theorem TmTy.unchanged {n : ℕ} {Γ Δ : FCtx n} {s : Tm n} {T : FTy} :
    TmTy Γ s T Δ → ∀ i, ¬ s.Occurs i → Δ i = Γ i
  | .lin h, i, hx => h.unchanged i hx
  | .lens h, i, hx => h.unchanged i hx
end

end LambdaF

end FlowTyping
