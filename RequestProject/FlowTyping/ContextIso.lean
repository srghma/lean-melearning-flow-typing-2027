module
public import RequestProject.FlowTyping.LensCombinators
public import RequestProject.FlowTyping.Embedding

/-!
# Packing contexts: splits and merges (Appendix C, Definition C.1)

For a context split `Γ = Γ₁, Γ₂`, the terms `split(ψ) : Γ° ⊸ Γ₁° ⊗ Γ₂°` and
`merge(ψ) : Γ₁° ⊗ Γ₂° ⊸ Γ°` of Definition C.1 exist as closed well-typed `λL` terms
(`Ctx.split_iso`).  We also record how `(-)°` interacts with `(-)†`, extension of contexts and
updates of a single variable, both for `λL` flow contexts and for `λF` contexts.
-/

@[expose] public section

namespace FlowTyping

open LambdaF

/-! ## `λL` flow contexts -/

lemma Ctx.toTy_succ {n : ℕ} (Γ : Ctx (n + 1)) :
    Γ.toTy = match Γ 0 with
      | .live A => .tensor (Ctx.toTy (Fin.tail Γ)) A
      | _ => Ctx.toTy (Fin.tail Γ) := rfl

/-- `Γ°` only depends on the live variables of `Γ`. -/
lemma Ctx.toTy_congr : ∀ {n : ℕ} {Γ Δ : Ctx n}, (∀ i A, Γ i = .live A ↔ Δ i = .live A) →
    Γ.toTy = Δ.toTy
  | 0, _, _, _ => rfl
  | n + 1, Γ, Δ, h => by
    have ih := Ctx.toTy_congr (Γ := Fin.tail Γ) (Δ := Fin.tail Δ) (fun i A => h i.succ A)
    rw [Ctx.toTy_succ, Ctx.toTy_succ]
    cases hΓ : Γ 0 with
    | live A =>
      have : Δ 0 = .live A := (h 0 A).1 hΓ
      simp only [this, ih]
    | absent | dead =>
      cases hΔ : Δ 0 with
      | live A => have := (h 0 A).2 hΔ; rw [hΓ] at this; cases this
      | absent | dead => simp only [ih]

/-- `(Γ†)° = 1`. -/
lemma Ctx.toTy_dag : ∀ {n : ℕ} (Γ : Ctx n), Γ.dag.toTy = .one
  | 0, _ => rfl
  | n + 1, Γ => by
    rw [Ctx.toTy_succ]
    have : Fin.tail Γ.dag = Ctx.dag (Fin.tail Γ) := rfl
    have h0 : Γ.dag 0 = (Γ 0).dag := rfl
    rw [h0, this, Ctx.toTy_dag]
    cases Γ 0 <;> rfl

/-- A context all of whose variables are dead has `Γ° = 1`. -/
lemma Ctx.toTy_allDead {n : ℕ} : Ctx.toTy (fun _ : Fin n => Entry.dead) = .one := by
  have : (fun _ : Fin n => Entry.dead) = Ctx.dag (fun _ : Fin n => Entry.dead) := by
    funext i; rfl
  rw [this, Ctx.toTy_dag]

/-- The context whose only variable is `i : A`. -/
def Ctx.single {n : ℕ} (i : Fin n) (A : Ty) : Ctx n := fun j => if j = i then .live A else .absent

lemma Ctx.toTy_single : ∀ {n : ℕ} (i : Fin n) (A : Ty), (Ctx.single i A).toTy = .tensor .one A
  | 0, i, _ => i.elim0
  | n + 1, i, A => by
    rw [Ctx.toTy_succ]
    cases i using Fin.cases with
    | zero =>
      have h0 : Ctx.single (0 : Fin (n + 1)) A 0 = .live A := by simp [Ctx.single]
      have ht : Fin.tail (Ctx.single (0 : Fin (n + 1)) A) = fun _ => .absent := by
        funext j; simp [Ctx.single, Fin.tail, Fin.succ_ne_zero]
      have : Ctx.toTy (fun _ : Fin n => Entry.absent) = .one :=
        (Ctx.toTy_congr (Δ := fun _ : Fin n => Entry.dead) (fun _ _ => by simp)).trans
          Ctx.toTy_allDead
      simp only [h0, ht, this]
    | succ i =>
      have h0 : Ctx.single i.succ A 0 = .absent := by
        simp [Ctx.single, (Fin.succ_ne_zero i).symm]
      have ht : Fin.tail (Ctx.single i.succ A) = Ctx.single i A := by
        funext j; simp [Ctx.single, Fin.tail]
      simp only [h0, ht, Ctx.toTy_single i A]

lemma Ctx.Split.tail {n : ℕ} {Γ Γ₁ Γ₂ : Ctx (n + 1)} (hs : Γ.Split Γ₁ Γ₂) :
    Ctx.Split (Fin.tail Γ) (Fin.tail Γ₁) (Fin.tail Γ₂) := fun i => hs i.succ

/-- **Definition C.1.** For a context split `Γ = Γ₁, Γ₂`, there are closed well-typed terms
`split : Γ° ⊸ Γ₁° ⊗ Γ₂°` and `merge : Γ₁° ⊗ Γ₂° ⊸ Γ°`. -/
theorem Ctx.split_iso : ∀ {n : ℕ} {Γ Γ₁ Γ₂ : Ctx n}, Γ.Split Γ₁ Γ₂ →
    Inh (.lolli Γ.toTy (.tensor Γ₁.toTy Γ₂.toTy)) ∧
    Inh (.lolli (.tensor Γ₁.toTy Γ₂.toTy) Γ.toTy)
  | 0, _, _, _, _ => ⟨Comb.oneSplit, Comb.oneMerge⟩
  | n + 1, Γ, Γ₁, Γ₂, hs => by
    obtain ⟨ihs, ihm⟩ := Ctx.split_iso hs.tail
    rw [Ctx.toTy_succ Γ, Ctx.toTy_succ Γ₁, Ctx.toTy_succ Γ₂]
    rcases hs 0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      cases Γ 0 with
      | live A => exact ⟨Comb.tensorR ihs, Comb.mergeR ihm⟩
      | absent | dead => exact ⟨ihs, ihm⟩
    · rw [h1, h2]
      cases Γ 0 with
      | live A => exact ⟨Comb.tensorL ihs, Comb.mergeL ihm⟩
      | absent | dead => exact ⟨ihs, ihm⟩

/-- Removing a live variable from a context. -/
theorem Ctx.remove_iso {n : ℕ} {Γ : Ctx n} {i : Fin n} {A : Ty} (h : Γ i = .live A) :
    Inh (.lolli Γ.toTy (.tensor (Ctx.toTy (Function.update Γ i .absent)) A)) ∧
    Inh (.lolli (.tensor (Ctx.toTy (Function.update Γ i .absent)) A) Γ.toTy) := by
  have hs : Γ.Split (Function.update Γ i .absent) (Ctx.single i A) := fun j => by
    by_cases hj : j = i
    · subst hj; left; simp [Ctx.single, h]
    · right; simp [Ctx.single, hj]
  obtain ⟨s, m⟩ := Ctx.split_iso hs
  rw [Ctx.toTy_single] at s m
  exact ⟨Comb.unitSplit s, Comb.unitMerge m⟩

lemma Ctx.toTy_update_dead {n : ℕ} (Γ : Ctx n) (i : Fin n) :
    Ctx.toTy (Function.update Γ i .dead) = Ctx.toTy (Function.update Γ i .absent) :=
  Ctx.toTy_congr fun j A => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]

/-! ## `λF` contexts -/

/-- The `λL` flow context underlying `Γ°`. -/
def LambdaF.FCtx.toCtx {n : ℕ} (Γ : FCtx n) : Ctx n := fun i => (Γ i).circ

lemma LambdaF.FCtx.circ_eq {n : ℕ} (Γ : FCtx n) : Γ.circ = Γ.toCtx.toTy := rfl

lemma LambdaF.FCtx.toCtx_cons {n : ℕ} (e : FEntry) (Γ : FCtx n) :
    FCtx.toCtx (Fin.cons e Γ : FCtx (n + 1)) = Fin.cons e.circ Γ.toCtx := by
  funext i; cases i using Fin.cases <;> rfl

lemma LambdaF.FCtx.circ_cons_live {n : ℕ} (A : PTy) (Γ : FCtx n) :
    FCtx.circ (Fin.cons (.live A) Γ : FCtx (n + 1)) = .tensor Γ.circ A.circ := by
  rw [FCtx.circ_eq, FCtx.toCtx_cons]; rfl

lemma LambdaF.FCtx.circ_cons_dead {n : ℕ} (Γ : FCtx n) :
    FCtx.circ (Fin.cons .dead Γ : FCtx (n + 1)) = Γ.circ := by
  rw [FCtx.circ_eq, FCtx.toCtx_cons]; rfl

lemma LambdaF.FCtx.circ_dag {n : ℕ} (Γ : FCtx n) : Γ.dag.circ = .one := by
  have : Γ.dag.toCtx = Γ.toCtx.dag := by
    funext i; simp only [FCtx.toCtx, FCtx.dag, Ctx.dag]; cases Γ i <;> rfl
  rw [FCtx.circ_eq, this, Ctx.toTy_dag]

lemma LambdaF.FCtx.circ_allDead {n : ℕ} : FCtx.circ (fun _ : Fin n => FEntry.dead) = .one :=
  Ctx.toTy_allDead

lemma LambdaF.FCtx.toCtx_update {n : ℕ} (Γ : FCtx n) (i : Fin n) (e : FEntry) :
    FCtx.toCtx (Function.update Γ i e) = Function.update Γ.toCtx i e.circ := by
  funext j; by_cases hj : j = i
  · subst hj; simp [FCtx.toCtx]
  · simp [FCtx.toCtx, Function.update_of_ne hj]

lemma LambdaF.FCtx.Split.toCtx {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) :
    Γ.toCtx.Split Γ₁.toCtx Γ₂.toCtx := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; simp [FCtx.toCtx, h1, h2, FEntry.circ]
  · right; simp [FCtx.toCtx, h1, h2, FEntry.circ]

/-- Splitting and merging `λF` contexts. -/
theorem LambdaF.FCtx.split_iso {n : ℕ} {Γ Γ₁ Γ₂ : FCtx n} (hs : Γ.Split Γ₁ Γ₂) :
    Inh (.lolli Γ.circ (.tensor Γ₁.circ Γ₂.circ)) ∧
    Inh (.lolli (.tensor Γ₁.circ Γ₂.circ) Γ.circ) :=
  Ctx.split_iso hs.toCtx

/-- Merging into a context of the form `Γ₁, Γ₂†`. -/
theorem LambdaF.FCtx.merge_dag {n : ℕ} {Δ Γ₁ Γ₂ : FCtx n} (hs : Δ.Split Γ₁ Γ₂.dag) :
    Inh (.lolli (.tensor Γ₁.circ .one) Δ.circ) := by
  have := (FCtx.split_iso hs).2
  rwa [FCtx.circ_dag] at this

/-- The packing of contexts used by the translation of `Var` and `FVar-Live`. -/
theorem LambdaF.FCtx.remove_iso {n : ℕ} {Γ : FCtx n} {i : Fin n} {A : PTy}
    (h : Γ i = .live A) :
    Inh (.lolli Γ.circ (.tensor (FCtx.circ (Function.update Γ i .absent)) A.circ)) ∧
    Inh (.lolli (.tensor (FCtx.circ (Function.update Γ i .absent)) A.circ) Γ.circ) := by
  have h' : Γ.toCtx i = .live A.circ := by simp [FCtx.toCtx, h, FEntry.circ]
  rw [FCtx.circ_eq, FCtx.circ_eq, FCtx.toCtx_update]
  exact Ctx.remove_iso h'

lemma LambdaF.FCtx.circ_update_dead {n : ℕ} (Γ : FCtx n) (i : Fin n) :
    FCtx.circ (Function.update Γ i .dead) = FCtx.circ (Function.update Γ i .absent) := by
  rw [FCtx.circ_eq, FCtx.circ_eq, FCtx.toCtx_update, FCtx.toCtx_update]
  exact Ctx.toTy_update_dead _ _

lemma LambdaF.FCtx.circ_of_dead {n : ℕ} {Γ : FCtx n} {i : Fin n} (h : Γ i = .dead) :
    Γ.circ = FCtx.circ (Function.update Γ i .absent) := by
  rw [← FCtx.circ_update_dead]
  congr 1
  funext j; by_cases hj : j = i
  · subst hj; simp [h]
  · simp [Function.update_of_ne hj]

lemma LambdaF.FCtx.update_update {n : ℕ} (Γ : FCtx n) (i : Fin n) (e e' : FEntry) :
    Function.update (Function.update Γ i e) i e' = Function.update Γ i e' := by
  simp

end FlowTyping
