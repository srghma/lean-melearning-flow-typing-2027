module
public import RequestProject.FlowTyping.Metatheory
public import RequestProject.FlowTyping.LambdaF

/-!
# `λF` extends `λL`

* `LambdaF.PTy.circ`, `LambdaF.FTy.circ`, `LambdaF.FCtx.circ`: the operator `(-)°` mapping
  `λF` types and contexts to `λL` types (Section 5.2).
* `Ty.toP`, `Term.toF`: every `λL` type and term is a `λF` type and term.
* `Ty.toP_circ`: every `λL` type `B` satisfies `B° = B` (Theorem 7.2).
* `Flow.toLambdaF`: every `λL` flow derivation is a `λF` derivation.
* `Lin.toLambdaF`: if `Γ ⊢ t : A` in `λL` then `Γ ⊢ t : A ⊣ Γ†` in `λF` (Theorem 7.2).
-/

@[expose] public section

namespace FlowTyping

open LambdaF

/-! ## The operator `(-)°` on `λF` types -/

/-- `(-)°` on plain `λF` types: it commutes with every type former except flow functions,
for which
`(A/A' ⊸ B/B')° = A° ⊸ (B° ⊗ (B'° ⊸ A'°))`, `(A/A' ⊸ B)° = A° ⊸ (B° ⊗ A'°)`,
`(A ⊸ B/B')° = A° ⊸ (B° ⊗ (B'° ⊸ 1))` and `(A ⊸ B)° = A° ⊸ B°`. -/
def LambdaF.PTy.circ : PTy → Ty
  | .tvar a => .tvar a
  | .lolli (.plain A) (.plain B) => .lolli A.circ B.circ
  | .lolli (.plain A) (.slash B B') => .lolli A.circ (.tensor B.circ (.lolli B'.circ .one))
  | .lolli (.slash A A') (.plain B) => .lolli A.circ (.tensor B.circ A'.circ)
  | .lolli (.slash A A') (.slash B B') =>
    .lolli A.circ (.tensor B.circ (.lolli B'.circ A'.circ))
  | .tensor A B => .tensor A.circ B.circ
  | .one => .one
  | .plus A B => .plus A.circ B.circ
  | .zero => .zero
  | .with A B => .with A.circ B.circ
  | .top => .top
  | .bang A => .bang A.circ
termination_by A => sizeOf A
decreasing_by all_goals (simp_wf <;> omega)

/-- `(-)°` on a context entry. -/
def LambdaF.FEntry.circ : FEntry → Entry
  | .absent => .absent
  | .dead => .dead
  | .live A => .live A.circ

/-- `(-)°` on `λF` contexts, as a `λL` type: `(∅)° = 1`, `(Γ, x : A)° = Γ° ⊗ A°`,
`(Γ, x†)° = Γ°`. -/
def LambdaF.FCtx.circ {n : ℕ} (Γ : FCtx n) : Ty := Ctx.toTy (fun i => (Γ i).circ)

/-- The lens interpretation of a lens judgement `Γ₁ ⊢ u : A/B ⊣ Γ₂`: a closed `λL` lens of
type `(Γ₁°, Γ₂°) → (A°, B°)`. -/
def LambdaF.lensJudgementTy {n : ℕ} (Γ₁ Γ₂ : FCtx n) (A B : PTy) : Ty :=
  lensTy Γ₁.circ Γ₂.circ A.circ B.circ

/-! ## Including `λL` into `λF` -/

/-- Every `λL` type is a (plain) `λF` type. -/
def Ty.toP : Ty → PTy
  | .tvar a => .tvar a
  | .lolli A B => .lolli (.plain A.toP) (.plain B.toP)
  | .tensor A B => .tensor A.toP B.toP
  | .one => .one
  | .plus A B => .plus A.toP B.toP
  | .zero => .zero
  | .with A B => .with A.toP B.toP
  | .top => .top
  | .bang A => .bang A.toP

/-- **Theorem 7.2 (types).** Every `λL` type `B` satisfies `B° = B`. -/
theorem Ty.toP_circ (B : Ty) : B.toP.circ = B := by
  induction B with
  | tvar => simp [Ty.toP, PTy.circ]
  | lolli A B ihA ihB => simp [Ty.toP, PTy.circ, ihA, ihB]
  | tensor A B ihA ihB => simp [Ty.toP, PTy.circ, ihA, ihB]
  | one => simp [Ty.toP, PTy.circ]
  | plus A B ihA ihB => simp [Ty.toP, PTy.circ, ihA, ihB]
  | zero => simp [Ty.toP, PTy.circ]
  | «with» A B ihA ihB => simp [Ty.toP, PTy.circ, ihA, ihB]
  | top => simp [Ty.toP, PTy.circ]
  | bang A ih => simp [Ty.toP, PTy.circ, ih]

/-- Every `λL` term is a linear `λF` term. -/
def Term.toF : {n : ℕ} → Term n → LinTm n
  | _, .var i => .var i
  | _, .letIn t₁ t₂ => .letIn (.lin t₁.toF) t₂.toF
  | _, .lam A t => .lam (.plain A.toP) (.lin t.toF)
  | _, .app t₁ t₂ => .app t₁.toF (.lin t₂.toF)
  | _, .pair t₁ t₂ => .pair t₁.toF t₂.toF
  | _, .letPair t₁ t₂ => .letPair (.lin t₁.toF) t₂.toF
  | _, .unit => .unit
  | _, .letUnit t₁ t₂ => .letUnit (.lin t₁.toF) t₂.toF
  | _, .inl A B t => .inl A.toP B.toP t.toF
  | _, .inr A B t => .inr A.toP B.toP t.toF
  | _, .case t t₁ t₂ => .case (.lin t.toF) t₁.toF t₂.toF
  | _, .falseE B t => .falseE B.toP (.lin t.toF)
  | _, .withPair t₁ t₂ => .withPair t₁.toF t₂.toF
  | _, .fst t => .fst t.toF
  | _, .snd t => .snd t.toF
  | _, .trueI t => .trueI t.toF
  | _, .promote k ts t => .promote k (fun j => (ts j).toF) t.toF
  | _, .discard t => .discard t.toF
  | _, .copy t => .copy t.toF
  | _, .derelict t => .derelict t.toF

/-- Every `λL` flow context entry is a `λF` context entry. -/
def Entry.toF : Entry → FEntry
  | .absent => .absent
  | .dead => .dead
  | .live A => .live A.toP

/-- Every `λL` flow context is a `λF` context. -/
def Ctx.toF {n : ℕ} (Γ : Ctx n) : FCtx n := fun i => (Γ i).toF

lemma Ctx.toF_cons {n : ℕ} (a : Entry) (Γ : Ctx n) :
    Ctx.toF (Fin.cons a Γ : Ctx (n + 1)) = Fin.cons a.toF Γ.toF := by
  funext i; cases i using Fin.cases <;> rfl

lemma Ctx.toF_dag {n : ℕ} (Γ : Ctx n) : Γ.dag.toF = Γ.toF.dag := by
  funext i; simp only [Ctx.toF, Ctx.dag, FCtx.dag]; cases Γ i <;> rfl

lemma Ctx.toF_update {n : ℕ} (Γ : Ctx n) (i : Fin n) (e : Entry) :
    Ctx.toF (Function.update Γ i e) = Function.update Γ.toF i e.toF := by
  funext j; by_cases hj : j = i
  · subst hj; simp [Ctx.toF]
  · simp [Ctx.toF, Function.update_of_ne hj]

lemma Entry.toF_eq_absent {e : Entry} : e.toF = .absent ↔ e = .absent := by
  cases e <;> simp [Entry.toF]

lemma Ctx.Split.toF {n : ℕ} {Γ Γ₁ Γ₂ : Ctx n} (hs : Γ.Split Γ₁ Γ₂) :
    Γ.toF.Split Γ₁.toF Γ₂.toF := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨by simp [Ctx.toF, h1, Entry.toF], by simp [Ctx.toF, h2]⟩
  · right; exact ⟨by simp [Ctx.toF, h1, Entry.toF], by simp [Ctx.toF, h2]⟩

/-- Every flow derivation of `λL` (Fig. 3) is a derivation of the same judgement in `λF`. -/
theorem Flow.toLambdaF {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    LinTy Γ.toF t.toF A.toP Δ.toF := by
  induction h with
  | @var n Γ i A hΓ =>
    rw [Ctx.toF_update]; exact .var (by simp [Ctx.toF, hΓ, Entry.toF])
  | letIn _ _ ih₁ ih₂ =>
    rw [Ctx.toF_cons, Ctx.toF_cons] at ih₂
    exact .letIn ih₁ ih₂
  | lam hs _ hs' ih =>
    rw [Ctx.toF_cons, Ctx.toF_cons, Ctx.toF_dag] at ih
    have hs'' := hs'.toF; rw [Ctx.toF_dag] at hs''
    exact .lam hs.toF (.lin ih) hs''
  | app _ _ ih₁ ih₂ => exact .app ih₁ (.lin ih₂)
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | letPair _ _ ih₁ ih₂ =>
    rw [Ctx.toF_cons, Ctx.toF_cons, Ctx.toF_cons, Ctx.toF_cons] at ih₂
    exact .letPair ih₁ ih₂
  | unit => exact .unit
  | letUnit _ _ ih₁ ih₂ => exact .letUnit ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ =>
    rw [Ctx.toF_cons, Ctx.toF_cons] at ih₂ ih₃
    exact .case ih₁ ih₂ ih₃
  | falseE _ ih => exact .falseE ih
  | withPair hs _ _ hs' ih₁ ih₂ =>
    rw [Ctx.toF_dag] at ih₁ ih₂
    have hs'' := hs'.toF; rw [Ctx.toF_dag] at hs''
    exact .withPair hs.toF ih₁ ih₂ hs''
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | trueI _ ih => exact .trueI ih
  | @promote n k Γs ts t As B _ _ ih ihb =>
    exact .promote (Γs := fun j => (Γs j).toF) (As := fun j => (As j).toP) ih ihb
  | discard _ ih => exact .discard ih
  | copy _ ih => exact .copy ih
  | derelict _ ih => exact .derelict ih

/-- **Theorem 7.2 (typing).**  If `Γ ⊢ t : A` is a `λL` term, then `t` is also a `λF` term
with `Γ ⊢ t : A ⊣ Γ†`. -/
theorem Lin.toLambdaF {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) :
    LinTy Γ.embed.toF t.toF A.toP Γ.embed.toF.dag := by
  rw [← Ctx.toF_dag]; exact ((lin_iff_flow Γ t A).1 h).toLambdaF

end FlowTyping
