module
public import RequestProject.FlowTyping.LambdaL
public import Mathlib.Tactic

/-!
# Metatheory of flow typing for `λL` (Section 4.6)

* `FlowTyping.Flow.frame_rule` — Lemma 4.7 (frame rule).
* `FlowTyping.lin_iff_flow` — Theorem 4.6: `Γ ⊢ t : A  ⟺  Γ ⊢ t : A ⊣ Γ†`.
-/

@[expose] public section

namespace FlowTyping

/-! ## Auxiliary operations on entries and contexts -/

/-- How a single variable may evolve through a `λL` flow judgement: it is either unchanged,
or it was live and becomes dead. -/
def Entry.Step (e e' : Entry) : Prop := e' = e ∨ (∃ A, e = .live A) ∧ e' = .dead

/-- The type consumed at a variable that goes from `e` to `e'`. -/
def Entry.consumed : Entry → Entry → Option Ty
  | .live A, .dead => some A
  | _, _ => none

/-- The part of a flow context consumed by a judgement `Γ ⊢ t : A ⊣ Δ`. -/
def Ctx.consumed {n : ℕ} (Γ Δ : Ctx n) : LCtx n := fun i => (Γ i).consumed (Δ i)

/-- Overlay of entries: `e` takes precedence unless it is absent. -/
def Entry.overlay : Entry → Entry → Entry
  | .absent, e => e
  | e, _ => e

/-- Overlay of contexts (used to frame a context with extra variables). -/
def Ctx.overlay {n : ℕ} (Γ Θ : Ctx n) : Ctx n := fun i => (Γ i).overlay (Θ i)

/-! ## Basic facts -/

lemma Entry.Step.refl (e : Entry) : e.Step e := Or.inl rfl

lemma Entry.Step.trans {a b c : Entry} (h₁ : a.Step b) (h₂ : b.Step c) : a.Step c := by
  unfold Entry.Step at *
  rcases h₁ with rfl | ⟨⟨A, rfl⟩, rfl⟩ <;> rcases h₂ with rfl | ⟨⟨B, h⟩, rfl⟩ <;> simp_all

lemma Entry.Step.antisymm {a b : Entry} (h₁ : a.Step b) (h₂ : b.Step a) : a = b := by
  unfold Entry.Step at *
  rcases h₁ with rfl | ⟨⟨A, rfl⟩, rfl⟩ <;> rcases h₂ with h | ⟨⟨B, h⟩, h'⟩ <;> simp_all

lemma Entry.Step.dag (e : Entry) : e.Step e.dag := by
  cases e <;> simp [Entry.Step, Entry.dag]

@[simp] lemma Entry.dag_absent : Entry.absent.dag = .absent := rfl
@[simp] lemma Entry.dag_dead : Entry.dead.dag = .dead := rfl
@[simp] lemma Entry.dag_live (A : Ty) : (Entry.live A).dag = .dead := rfl
@[simp] lemma Entry.dag_eq_absent {e : Entry} : e.dag = .absent ↔ e = .absent := by
  cases e <;> simp [Entry.dag]
@[simp] lemma Entry.dag_dag (e : Entry) : e.dag.dag = e.dag := by cases e <;> rfl
@[simp] lemma Ctx.dag_apply {n : ℕ} (Γ : Ctx n) (i : Fin n) : Γ.dag i = (Γ i).dag := rfl

/-- Pointwise description of the output context `Γ₁, Γ₂†` of the rules `⊸-I` and `&-I`. -/
lemma Ctx.split_dag {n : ℕ} {Γ Γ₁ Γ₂ Δ : Ctx n} (hs : Γ.Split Γ₁ Γ₂) (hs' : Δ.Split Γ₁ Γ₂.dag)
    (i : Fin n) :
    (Γ₂ i = .absent ∧ Γ₁ i = Γ i ∧ Δ i = Γ i) ∨
      (Γ₁ i = .absent ∧ Γ₂ i = Γ i ∧ Δ i = (Γ i).dag) := by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs' i with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp_all

/-- A relation that holds along every step of a chain holds between any two points
of the chain (given reflexivity and transitivity). -/
lemma chain_rel_le {α : Type*} {k : ℕ} (R : α → α → Prop) (hr : ∀ a, R a a)
    (ht : ∀ a b c, R a b → R b c → R a c) (f : Fin (k + 1) → α)
    (h : ∀ j : Fin k, R (f j.castSucc) (f j.succ)) {a b : Fin (k + 1)} (hab : a ≤ b) :
    R (f a) (f b) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact hr _
  | succ m hm ih =>
    refine ht _ _ _ (ih (by omega)) ?_
    have := h ⟨m, by omega⟩
    simpa using this

/-- Every variable either is unchanged, or goes from live to dead, through a `λL` flow
judgement.  In particular `Γ₁` and `Γ₂` contain the same variables. -/
theorem Flow.step {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    ∀ i, (Γ i).Step (Δ i) := by
  induction h with
  | @var n Γ i A hΓ =>
    intro j
    by_cases hj : j = i
    · subst hj; simp [Entry.Step, hΓ]
    · simp [Function.update_of_ne hj, Entry.Step.refl]
  | letIn _ _ ih₁ ih₂ => exact fun i => (ih₁ i).trans (by simpa using ih₂ i.succ)
  | @lam n Γ Γ₁ Γ₂ Δ t A B hs _ hs' _ =>
    intro i
    rcases Ctx.split_dag hs hs' i with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
    · exact Entry.Step.refl _
    · exact Entry.Step.dag _
  | app _ _ ih₁ ih₂ => exact fun i => (ih₁ i).trans (ih₂ i)
  | pair _ _ ih₁ ih₂ => exact fun i => (ih₁ i).trans (ih₂ i)
  | letPair _ _ ih₁ ih₂ => exact fun i => (ih₁ i).trans (by simpa using ih₂ i.succ.succ)
  | unit => exact fun i => Entry.Step.refl _
  | letUnit _ _ ih₁ ih₂ => exact fun i => (ih₁ i).trans (ih₂ i)
  | inl _ ih => exact ih
  | inr _ ih => exact ih
  | case _ _ _ ih₁ ih₂ _ => exact fun i => (ih₁ i).trans (by simpa using ih₂ i.succ)
  | falseE _ ih => exact ih
  | @withPair n Γ Γ₁ Γ₂ Δ t₁ t₂ A B hs _ _ hs' _ _ =>
    intro i
    rcases Ctx.split_dag hs hs' i with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
    · exact Entry.Step.refl _
    · exact Entry.Step.dag _
  | fst _ ih => exact ih
  | snd _ ih => exact ih
  | trueI _ ih => exact ih
  | @promote n k Γs ts t As B _ _ ih _ =>
    intro i
    exact chain_rel_le (fun a b : Ctx n => a i |>.Step (b i)) (fun a => Entry.Step.refl _)
      (fun _ _ _ h₁ h₂ => h₁.trans h₂) Γs (fun j => ih j i) (Fin.zero_le _)
  | discard _ ih => exact ih
  | copy _ ih => exact ih
  | derelict _ ih => exact ih

@[simp] lemma Entry.overlay_absent_left (e : Entry) : Entry.absent.overlay e = e := rfl
@[simp] lemma Entry.overlay_absent_right (e : Entry) : e.overlay .absent = e := by
  cases e <;> rfl
@[simp] lemma Entry.overlay_dead (e : Entry) : Entry.dead.overlay e = .dead := rfl
@[simp] lemma Entry.overlay_live (A : Ty) (e : Entry) : (Entry.live A).overlay e = .live A := rfl
@[simp] lemma Ctx.overlay_apply {n : ℕ} (Γ Θ : Ctx n) (i : Fin n) :
    Γ.overlay Θ i = (Γ i).overlay (Θ i) := rfl

lemma Ctx.cons_overlay {n : ℕ} (a : Entry) (Γ Θ : Ctx n) :
    Ctx.overlay (Fin.cons a Γ : Ctx (n + 1)) (Fin.cons .absent Θ) = Fin.cons a (Γ.overlay Θ) := by
  funext i; cases i using Fin.cases <;> simp

lemma Entry.Step.absent_iff {e e' : Entry} (h : e.Step e') : e' = .absent ↔ e = .absent := by
  rcases h with rfl | ⟨⟨A, rfl⟩, rfl⟩ <;> simp

lemma Flow.absent_iff {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) (i : Fin n) :
    Δ i = .absent ↔ Γ i = .absent := (h.step i).absent_iff

/-- In a promotion chain, all contexts contain the same variables. -/
lemma chain_absent_iff {n k : ℕ} {Γs : Fin (k + 1) → Ctx n}
    (h : ∀ j : Fin k, ∀ i, (Γs j.castSucc i).Step (Γs j.succ i)) (j : Fin (k + 1)) (i : Fin n) :
    Γs j i = .absent ↔ Γs 0 i = .absent :=
  (chain_rel_le (fun a b : Ctx n => (a i).Step (b i)) (fun _ => Entry.Step.refl _)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) Γs (fun j => h j i) (Fin.zero_le j)).absent_iff

/-- General frame lemma: adding variables that are not in the contexts. -/
theorem Flow.frame {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    (Θ : Ctx n) (hΘ : ∀ i, Γ i = .absent ∨ Θ i = .absent) :
    Flow (Γ.overlay Θ) t A (Δ.overlay Θ) := by
  induction h with
  | @var n Γ i A hΓ =>
    have : Ctx.overlay (Function.update Γ i .dead) Θ = Function.update (Γ.overlay Θ) i .dead := by
      funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [this]; exact .var (by simp [hΓ])
  | @letIn n Γ₁ Γ₂ Γ₃ t₁ t₂ A B h₁ h₂ ih₁ ih₂ =>
    refine .letIn (ih₁ Θ hΘ) ?_
    have := ih₂ (Fin.cons .absent Θ) (fun i => by
      cases i using Fin.cases with
      | zero => simp
      | succ i => simpa [h₁.absent_iff] using hΘ i)
    simpa [Ctx.cons_overlay] using this
  | @lam n Γ Γ₁ Γ₂ Δ t A B hs h hs' _ =>
    have hΔ : ∀ i, Δ i = .absent ↔ Γ i = .absent := fun i => by
      rcases Ctx.split_dag hs hs' i with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> simp [h]
    refine .lam (Γ₁ := Γ₁.overlay Θ) (Γ₂ := Γ₂) (fun i => ?_) h (fun i => ?_)
    · rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hΘ i with h3 | h3 <;> simp_all
    · rcases hΘ i with h3 | h3
      · have h4 := (hΔ i).2 h3
        clear hΔ
        rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      · rcases hs' i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  | app _ _ ih₁ ih₂ =>
    exact .app (ih₁ Θ hΘ) (ih₂ Θ fun i => by rw [Flow.absent_iff ‹_› i]; exact hΘ i)
  | pair _ _ ih₁ ih₂ =>
    exact .pair (ih₁ Θ hΘ) (ih₂ Θ fun i => by rw [Flow.absent_iff ‹_› i]; exact hΘ i)
  | @letPair n Γ₁ Γ₂ Γ₃ t₁ t₂ A B C h₁ h₂ ih₁ ih₂ =>
    refine .letPair (ih₁ Θ hΘ) ?_
    have := ih₂ (Fin.cons .absent (Fin.cons .absent Θ)) (fun i => by
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa [h₁.absent_iff] using hΘ i)
    simpa [Ctx.cons_overlay] using this
  | unit => exact .unit
  | letUnit _ _ ih₁ ih₂ =>
    exact .letUnit (ih₁ Θ hΘ) (ih₂ Θ fun i => by rw [Flow.absent_iff ‹_› i]; exact hΘ i)
  | inl _ ih => exact .inl (ih Θ hΘ)
  | inr _ ih => exact .inr (ih Θ hΘ)
  | @case n Γ₁ Γ₂ Γ₃ t₁ t₂ t₃ A B C h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    have hΘ' : ∀ (X : Ty) i, (Fin.cons (.live X) Γ₂ : Ctx (n + 1)) i = .absent ∨
        (Fin.cons .absent Θ : Ctx (n + 1)) i = .absent := fun X i => by
      cases i using Fin.cases with
      | zero => simp
      | succ i => simpa [h₁.absent_iff] using hΘ i
    have e₂ := ih₂ _ (hΘ' A)
    have e₃ := ih₃ _ (hΘ' B)
    simp only [Ctx.cons_overlay] at e₂ e₃
    exact .case (ih₁ Θ hΘ) e₂ e₃
  | falseE _ ih => exact .falseE (ih Θ hΘ)
  | @withPair n Γ Γ₁ Γ₂ Δ t₁ t₂ A B hs h₁ h₂ hs' _ _ =>
    have hΔ : ∀ i, Δ i = .absent ↔ Γ i = .absent := fun i => by
      rcases Ctx.split_dag hs hs' i with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> simp [h]
    refine .withPair (Γ₁ := Γ₁.overlay Θ) (Γ₂ := Γ₂) (fun i => ?_) h₁ h₂ (fun i => ?_)
    · rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hΘ i with h3 | h3 <;> simp_all
    · rcases hΘ i with h3 | h3
      · have h4 := (hΔ i).2 h3
        clear hΔ
        rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      · rcases hs' i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  | fst _ ih => exact .fst (ih Θ hΘ)
  | snd _ ih => exact .snd (ih Θ hΘ)
  | trueI _ ih => exact .trueI (ih Θ hΘ)
  | @promote n k Γs ts t As B hts ht ih _ =>
    have hst : ∀ j : Fin k, ∀ i, (Γs j.castSucc i).Step (Γs j.succ i) := fun j => (hts j).step
    exact .promote (Γs := fun j => (Γs j).overlay Θ) (fun j => ih j Θ fun i => by
      rw [chain_absent_iff hst]; exact hΘ i) ht
  | discard _ ih => exact .discard (ih Θ hΘ)
  | copy _ ih => exact .copy (ih Θ hΘ)
  | derelict _ ih => exact .derelict (ih Θ hΘ)

lemma Entry.Step.eq_of_eq {a b c : Entry} (h₁ : a.Step b) (h₂ : b.Step c) (h : a = c) :
    b = a := by
  subst h; exact (h₁.antisymm h₂).symm

lemma Ctx.update_cons {n : ℕ} (a e : Entry) (Γ : Ctx n) (i : Fin n) :
    Function.update (Fin.cons a Γ : Ctx (n + 1)) i.succ e = Fin.cons a (Function.update Γ i e) :=
  (Fin.cons_update _ _ _ _).symm

lemma Ctx.update_dag {n : ℕ} (Γ : Ctx n) (i : Fin n) :
    Function.update Γ.dag i .absent = Ctx.dag (Function.update Γ i .absent) := by
  funext j; by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- Strengthening: a variable that is unchanged by a judgement can be removed. -/
theorem Flow.strengthen {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    (i : Fin n) (hi : Γ i = Δ i) :
    Flow (Function.update Γ i .absent) t A (Function.update Δ i .absent) := by
  induction h with
  | @var n Γ j A hΓ =>
    by_cases hij : i = j
    · subst hij; simp [hΓ] at hi
    · rw [Function.update_comm (Ne.symm hij)]
      exact .var (by rw [Function.update_of_ne (Ne.symm hij)]; exact hΓ)
  | @letIn n Γ₁ Γ₂ Γ₃ t₁ t₂ A B h₁ h₂ ih₁ ih₂ =>
    have e : Γ₂ i = Γ₁ i := (h₁.step i).eq_of_eq (by simpa using h₂.step i.succ) hi
    refine .letIn (ih₁ i e.symm) ?_
    have := ih₂ i.succ (by simpa [e] using hi)
    rw [Ctx.update_cons, Ctx.update_cons] at this; exact this
  | @lam n Γ Γ₁ Γ₂ Δ t A B hs h hs' ih =>
    rcases Ctx.split_dag hs hs' i with ⟨h2, h1, hΔ⟩ | ⟨h1, h2, hΔ⟩
    · refine .lam (Γ₁ := Function.update Γ₁ i .absent) (Γ₂ := Γ₂) (fun j => ?_) h (fun j => ?_)
      · by_cases hj : j = i
        · subst hj; simp [h2]
        · simpa [Function.update_of_ne hj] using hs j
      · by_cases hj : j = i
        · subst hj; simp [h2]
        · simpa [Function.update_of_ne hj] using hs' j
    · have := ih i.succ (by simp only [Fin.cons_succ, Ctx.dag_apply, h2]; rw [← hΔ]; exact hi)
      rw [Ctx.update_cons, Ctx.update_cons, Ctx.update_dag] at this
      refine .lam (Γ₁ := Γ₁) (Γ₂ := Function.update Γ₂ i .absent) (fun j => ?_) this (fun j => ?_)
      · by_cases hj : j = i
        · subst hj; simp [h1]
        · simpa [Function.update_of_ne hj] using hs j
      · by_cases hj : j = i
        · subst hj; simp [h1]
        · simpa [Function.update_of_ne hj] using hs' j
  | @app n Γ₁ Γ₂ Γ₃ t₁ t₂ A B h₁ h₂ ih₁ ih₂ =>
    have e : Γ₂ i = Γ₁ i := (h₁.step i).eq_of_eq (h₂.step i) hi
    exact .app (ih₁ i e.symm) (ih₂ i (e.trans hi))
  | @pair n Γ₁ Γ₂ Γ₃ t₁ t₂ A B h₁ h₂ ih₁ ih₂ =>
    have e : Γ₂ i = Γ₁ i := (h₁.step i).eq_of_eq (h₂.step i) hi
    exact .pair (ih₁ i e.symm) (ih₂ i (e.trans hi))
  | @letPair n Γ₁ Γ₂ Γ₃ t₁ t₂ A B C h₁ h₂ ih₁ ih₂ =>
    have e : Γ₂ i = Γ₁ i := (h₁.step i).eq_of_eq (by simpa using h₂.step i.succ.succ) hi
    refine .letPair (ih₁ i e.symm) ?_
    have := ih₂ i.succ.succ (by simpa [e] using hi)
    rw [Ctx.update_cons, Ctx.update_cons, Ctx.update_cons, Ctx.update_cons] at this; exact this
  | unit => exact .unit
  | @letUnit n Γ₁ Γ₂ Γ₃ t₁ t₂ A h₁ h₂ ih₁ ih₂ =>
    have e : Γ₂ i = Γ₁ i := (h₁.step i).eq_of_eq (h₂.step i) hi
    exact .letUnit (ih₁ i e.symm) (ih₂ i (e.trans hi))
  | inl _ ih => exact .inl (ih i hi)
  | inr _ ih => exact .inr (ih i hi)
  | @case n Γ₁ Γ₂ Γ₃ t₁ t₂ t₃ A B C h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    have e : Γ₂ i = Γ₁ i := (h₁.step i).eq_of_eq (by simpa using h₂.step i.succ) hi
    have e₂ := ih₂ i.succ (by simpa [e] using hi)
    have e₃ := ih₃ i.succ (by simpa [e] using hi)
    rw [Ctx.update_cons, Ctx.update_cons] at e₂ e₃
    exact .case (ih₁ i e.symm) e₂ e₃
  | falseE _ ih => exact .falseE (ih i hi)
  | @withPair n Γ Γ₁ Γ₂ Δ t₁ t₂ A B hs h₁ h₂ hs' ih₁ ih₂ =>
    rcases Ctx.split_dag hs hs' i with ⟨h2, h1, hΔ⟩ | ⟨h1, h2, hΔ⟩
    · refine .withPair (Γ₁ := Function.update Γ₁ i .absent) (Γ₂ := Γ₂) (fun j => ?_) h₁ h₂
        (fun j => ?_)
      · by_cases hj : j = i
        · subst hj; simp [h2]
        · simpa [Function.update_of_ne hj] using hs j
      · by_cases hj : j = i
        · subst hj; simp [h2]
        · simpa [Function.update_of_ne hj] using hs' j
    · have e₁ := ih₁ i (by simp only [Ctx.dag_apply, h2]; rw [← hΔ]; exact hi)
      have e₂ := ih₂ i (by simp only [Ctx.dag_apply, h2]; rw [← hΔ]; exact hi)
      simp only [Ctx.update_dag] at e₁ e₂
      refine .withPair (Γ₁ := Γ₁) (Γ₂ := Function.update Γ₂ i .absent) (fun j => ?_) e₁ e₂
        (fun j => ?_)
      · by_cases hj : j = i
        · subst hj; simp [h1]
        · simpa [Function.update_of_ne hj] using hs j
      · by_cases hj : j = i
        · subst hj; simp [h1]
        · simpa [Function.update_of_ne hj] using hs' j
  | fst _ ih => exact .fst (ih i hi)
  | snd _ ih => exact .snd (ih i hi)
  | trueI _ ih => exact .trueI (ih i hi)
  | @promote n k Γs ts t As B hts ht ih _ =>
    have hR : ∀ {a b : Fin (k + 1)}, a ≤ b → (Γs a i).Step (Γs b i) := fun hab =>
      chain_rel_le (fun a b : Ctx n => (a i).Step (b i)) (fun _ => Entry.Step.refl _)
        (fun _ _ _ h₁ h₂ => h₁.trans h₂) Γs (fun j => (hts j).step i) hab
    have e : ∀ j, Γs j i = Γs 0 i := fun j =>
      (hR (Fin.zero_le j)).eq_of_eq (hR (Fin.le_last j)) hi
    exact .promote (Γs := fun j => Function.update (Γs j) i .absent)
      (fun j => ih j i ((e _).trans (e _).symm)) ht
  | discard _ ih => exact .discard (ih i hi)
  | copy _ ih => exact .copy (ih i hi)
  | derelict _ ih => exact .derelict (ih i hi)

@[simp] lemma Entry.consumed_self (e : Entry) : e.consumed e = none := by
  cases e <;> rfl
@[simp] lemma Entry.consumed_live_dead (A : Ty) : (Entry.live A).consumed .dead = some A := rfl
@[simp] lemma Entry.consumed_absent (e : Entry) : Entry.absent.consumed e = none := rfl
@[simp] lemma Entry.consumed_dead (e : Entry) : Entry.dead.consumed e = none := rfl
@[simp] lemma Ctx.consumed_apply {n : ℕ} (Γ Δ : Ctx n) (i : Fin n) :
    Γ.consumed Δ i = (Γ i).consumed (Δ i) := rfl

lemma Ctx.consumed_cons {n : ℕ} (a b : Entry) (Γ Δ : Ctx n) :
    Ctx.consumed (Fin.cons a Γ : Ctx (n + 1)) (Fin.cons b Δ) = Fin.cons (a.consumed b) (Γ.consumed Δ) := by
  funext i; cases i using Fin.cases <;> simp

lemma Entry.Step.of_live {A : Ty} {e : Entry} (h : (Entry.live A).Step e) :
    e = .live A ∨ e = .dead := by
  rcases h with h | ⟨-, h⟩ <;> simp [h]

lemma Entry.Step.of_dead {e : Entry} (h : Entry.dead.Step e) : e = .dead := by
  rcases h with h | ⟨⟨A, h'⟩, h⟩ <;> simp_all

/-- Consumption along two consecutive steps splits disjointly. -/
lemma Entry.consumed_split {a b c : Entry} (h₁ : a.Step b) (h₂ : b.Step c) :
    (a.consumed b = none ∧ b.consumed c = a.consumed c) ∨
      (b.consumed c = none ∧ a.consumed b = a.consumed c) := by
  rcases h₁ with rfl | ⟨⟨A, rfl⟩, rfl⟩
  · simp
  · rcases h₂ with rfl | ⟨⟨B, h⟩, rfl⟩ <;> simp_all

/-- Consumption along a chain of steps: at most one step consumes, and it consumes what the
whole chain consumes. -/
lemma Entry.consumed_chain {k : ℕ} (e : Fin (k + 1) → Entry)
    (h : ∀ j : Fin k, (e j.castSucc).Step (e j.succ)) :
    ((e 0).consumed (e (Fin.last k)) = none ∧ ∀ j : Fin k, (e j.castSucc).consumed (e j.succ) = none) ∨
      ∃ j : Fin k, (e j.castSucc).consumed (e j.succ) = (e 0).consumed (e (Fin.last k)) ∧
        ∀ j', j' ≠ j → (e j'.castSucc).consumed (e j'.succ) = none := by
  have hR : ∀ {a b : Fin (k + 1)}, a ≤ b → (e a).Step (e b) := fun hab =>
    chain_rel_le Entry.Step Entry.Step.refl (fun _ _ _ h₁ h₂ => h₁.trans h₂) e h hab
  by_cases h0 : e 0 = e (Fin.last k)
  · left
    have hc : ∀ j, e j = e 0 := fun j => (hR (Fin.zero_le j)).eq_of_eq (hR (Fin.le_last j)) h0
    refine ⟨by rw [h0]; simp, fun j => ?_⟩
    rw [hc j.castSucc, hc j.succ]; simp
  · right
    obtain ⟨A, hA, hl⟩ : ∃ A, e 0 = .live A ∧ e (Fin.last k) = .dead := by
      rcases hR (Fin.zero_le (Fin.last k)) with h' | ⟨⟨A, hA⟩, h'⟩
      · exact absurd h'.symm h0
      · exact ⟨A, hA, h'⟩
    have hP : ∃ m, ∃ hm : m < k + 1, e ⟨m, hm⟩ = .dead := ⟨k, by omega, hl⟩
    classical
    set m := Nat.find hP with hm_def
    obtain ⟨hmk, hmd⟩ := Nat.find_spec hP
    have hmin : ∀ m' (hm' : m' < k + 1), m' < m → e ⟨m', hm'⟩ ≠ .dead := fun m' hm' hlt hd =>
      Nat.find_min hP hlt ⟨hm', hd⟩
    have hm0 : m ≠ 0 := by
      intro h0'
      have : e ⟨0, by omega⟩ = .dead := by
        have := hmd; simp only [← hm_def, h0'] at this; exact this
      rw [show (⟨0, by omega⟩ : Fin (k + 1)) = 0 from rfl, hA] at this
      cases this
    -- every position before `m` is live, every position from `m` on is dead
    have hbefore : ∀ x : Fin (k + 1), x.val < m → e x = .live A := by
      intro x hx
      rcases (show (Entry.live A).Step (e x) from hA ▸ hR (Fin.zero_le x)).of_live with h' | h'
      · exact h'
      · exact absurd h' (hmin x.val x.isLt hx)
    have hafter : ∀ x : Fin (k + 1), m ≤ x.val → e x = .dead := by
      intro x hx
      have hmx : (⟨m, hmk⟩ : Fin (k + 1)) ≤ x := by simpa [Fin.le_def] using hx
      exact (show Entry.dead.Step (e x) from hmd ▸ hR hmx).of_dead
    refine ⟨⟨m - 1, by omega⟩, ?_, fun j' hj' => ?_⟩
    · rw [hbefore _ (by simp; omega), hafter _ (by simp; omega), hA, hl]
    · have hne : j'.val ≠ m - 1 := fun h' => hj' (Fin.ext h')
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [hbefore _ (by simp; omega), hbefore _ (by simp; omega)]; simp
      · rw [hafter _ (by simp; omega)]; simp

/-- Every flow derivation yields a conventional derivation over the consumed variables. -/
theorem Flow.toLin {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    Lin (Γ.consumed Δ) t A := by
  have split2 : ∀ {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n}, (∀ i, (Γ₁ i).Step (Γ₂ i)) → (∀ i, (Γ₂ i).Step (Γ₃ i)) →
      (Γ₁.consumed Γ₃).Split (Γ₁.consumed Γ₂) (Γ₂.consumed Γ₃) := fun h₁ h₂ i =>
    Entry.consumed_split (h₁ i) (h₂ i)
  have splitDag : ∀ {n : ℕ} {Γ Γ₁ Γ₂ Δ : Ctx n}, Γ.Split Γ₁ Γ₂ → Δ.Split Γ₁ Γ₂.dag →
      Γ.consumed Δ = Γ₂.consumed Γ₂.dag := fun hs hs' => by
    funext i
    rcases Ctx.split_dag hs hs' i with ⟨h2, -, h⟩ | ⟨-, h2, h⟩ <;> simp [h, h2]
  induction h with
  | @var n Γ i A hΓ =>
    have : Γ.consumed (Function.update Γ i .dead) = LCtx.single i A := by
      funext j; by_cases hj : j = i
      · subst hj; simp [hΓ, LCtx.single]
      · simp [LCtx.single, hj]
    rw [this]; exact .var i A
  | letIn h₁ h₂ ih₁ ih₂ =>
    rw [Ctx.consumed_cons] at ih₂
    exact .letIn (split2 h₁.step (fun i => by simpa using h₂.step i.succ)) ih₁ (by simpa using ih₂)
  | lam hs h hs' ih =>
    rw [Ctx.consumed_cons] at ih
    rw [splitDag hs hs']
    exact .lam (by simpa using ih)
  | app h₁ h₂ ih₁ ih₂ => exact .app (split2 h₁.step h₂.step) ih₁ ih₂
  | pair h₁ h₂ ih₁ ih₂ => exact .pair (split2 h₁.step h₂.step) ih₁ ih₂
  | letPair h₁ h₂ ih₁ ih₂ =>
    rw [Ctx.consumed_cons, Ctx.consumed_cons] at ih₂
    exact .letPair (split2 h₁.step (fun i => by simpa using h₂.step i.succ.succ)) ih₁
      (by simpa using ih₂)
  | unit =>
    have : ∀ {n : ℕ} (Γ : Ctx n), Γ.consumed Γ = LCtx.empty n := fun Γ => by
      funext i; simp [LCtx.empty]
    rw [this]; exact .unit
  | letUnit h₁ h₂ ih₁ ih₂ => exact .letUnit (split2 h₁.step h₂.step) ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    rw [Ctx.consumed_cons] at ih₂ ih₃
    exact .case (split2 h₁.step (fun i => by simpa using h₂.step i.succ)) ih₁
      (by simpa using ih₂) (by simpa using ih₃)
  | falseE _ ih => exact .falseE ih
  | withPair hs _ _ hs' ih₁ ih₂ =>
    rw [splitDag hs hs']
    exact .withPair ih₁ ih₂
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | trueI _ ih => exact .trueI ih
  | @promote n k Γs ts t As B hts ht ih ihb =>
    refine .promote (Γs := fun j => (Γs j.castSucc).consumed (Γs j.succ)) (fun i => ?_) ih
      (by simpa [Ctx.consumed] using ihb)
    rcases Entry.consumed_chain (fun j => Γs j i) (fun j => (hts j).step i) with
      ⟨h0, hall⟩ | ⟨j, hj, hothers⟩
    · exact Or.inl ⟨h0, hall⟩
    · exact Or.inr ⟨j, hj, hothers⟩
  | discard _ ih => exact .discard ih
  | copy _ ih => exact .copy ih
  | derelict _ ih => exact .derelict ih

@[simp] lemma Entry.ofOption_none : Entry.ofOption none = .absent := rfl
@[simp] lemma Entry.ofOption_some (A : Ty) : Entry.ofOption (some A) = .live A := rfl
@[simp] lemma LCtx.embed_apply {n : ℕ} (Γ : LCtx n) (i : Fin n) :
    Γ.embed i = Entry.ofOption (Γ i) := rfl

lemma LCtx.embed_cons {n : ℕ} (a : Option Ty) (Γ : LCtx n) :
    LCtx.embed (Fin.cons a Γ : LCtx (n + 1)) = Fin.cons (Entry.ofOption a) Γ.embed := by
  funext i; cases i using Fin.cases <;> simp

lemma Ctx.dag_cons {n : ℕ} (a : Entry) (Γ : Ctx n) :
    Ctx.dag (Fin.cons a Γ : Ctx (n + 1)) = Fin.cons a.dag Γ.dag := by
  funext i; cases i using Fin.cases <;> simp

/-- The middle context of a sequential composition: the variables of `Γ₁` are dead,
those of `Γ₂` are still live. -/
def LCtx.mid {n : ℕ} (Γ₁ Γ₂ : LCtx n) : Ctx n := Γ₁.embed.dag.overlay Γ₂.embed

lemma LCtx.Split.flow_left {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) {t : Term n} {A : Ty}
    (h : Flow Γ₁.embed t A Γ₁.embed.dag) : Flow Γ.embed t A (LCtx.mid Γ₁ Γ₂) := by
  have := h.frame Γ₂.embed (fun i => by rcases hs i with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1])
  have e : Γ₁.embed.overlay Γ₂.embed = Γ.embed := by
    funext i; rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, ← h2]
  rwa [e] at this

lemma LCtx.Split.mid_eq {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) :
    Γ₂.embed.overlay Γ₁.embed.dag = LCtx.mid Γ₁ Γ₂ := by
  funext i
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [LCtx.mid, Ctx.overlay_apply,
    Ctx.dag_apply, LCtx.embed_apply, h1] <;> cases Γ₁ i <;> cases Γ₂ i <;> simp_all

lemma LCtx.Split.dag_eq {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) :
    Γ₂.embed.dag.overlay Γ₁.embed.dag = Γ.embed.dag := by
  funext i
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [Ctx.overlay_apply,
    Ctx.dag_apply, LCtx.embed_apply, h1, ← h2] <;> cases Γ₁ i <;> cases Γ₂ i <;> simp_all

lemma LCtx.Split.disj_right {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) (i : Fin n) :
    Γ₂.embed i = .absent ∨ Γ₁.embed.dag i = .absent := by
  rcases hs i with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]

lemma LCtx.Split.flow_right {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) {t : Term n} {A : Ty}
    (h : Flow Γ₂.embed t A Γ₂.embed.dag) : Flow (LCtx.mid Γ₁ Γ₂) t A Γ.embed.dag := by
  have := h.frame Γ₁.embed.dag hs.disj_right
  rwa [hs.mid_eq, hs.dag_eq] at this

lemma LCtx.Split.flow_right₁ {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) {t : Term (n + 1)}
    {A B : Ty} (h : Flow (Fin.cons (.live A) Γ₂.embed) t B (Fin.cons .dead Γ₂.embed.dag)) :
    Flow (Fin.cons (.live A) (LCtx.mid Γ₁ Γ₂)) t B (Fin.cons .dead Γ.embed.dag) := by
  have := h.frame (Fin.cons .absent Γ₁.embed.dag) (fun i => by
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using hs.disj_right i)
  rwa [Ctx.cons_overlay, Ctx.cons_overlay, hs.mid_eq, hs.dag_eq] at this

lemma LCtx.Split.flow_right₂ {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) {t : Term (n + 2)}
    {A B C : Ty}
    (h : Flow (Fin.cons (.live B) (Fin.cons (.live A) Γ₂.embed)) t C
      (Fin.cons .dead (Fin.cons .dead Γ₂.embed.dag))) :
    Flow (Fin.cons (.live B) (Fin.cons (.live A) (LCtx.mid Γ₁ Γ₂))) t C
      (Fin.cons .dead (Fin.cons .dead Γ.embed.dag)) := by
  have := h.frame (Fin.cons .absent (Fin.cons .absent Γ₁.embed.dag)) (fun i => by
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases i using Fin.cases with
      | zero => simp
      | succ i => simpa using hs.disj_right i)
  rwa [Ctx.cons_overlay, Ctx.cons_overlay, Ctx.cons_overlay, Ctx.cons_overlay, hs.mid_eq,
    hs.dag_eq] at this

/-- Canonical description of an `n`-ary context split at a single variable. -/
lemma LCtx.SplitN.cases {n k : ℕ} {Γ : LCtx n} {Γs : Fin k → LCtx n} (hs : Γ.SplitN Γs)
    (i : Fin n) :
    (Γ i = none ∧ ∀ j, Γs j i = none) ∨
      ∃ j A, Γ i = some A ∧ Γs j i = some A ∧ ∀ j', j' ≠ j → Γs j' i = none := by
  rcases hs i with h | ⟨j, hj, hother⟩
  · exact Or.inl h
  · cases hΓ : Γ i with
    | none =>
      refine Or.inl ⟨rfl, fun j' => ?_⟩
      by_cases h' : j' = j
      · subst h'; rw [hj, hΓ]
      · exact hother j' h'
    | some A => exact Or.inr ⟨j, A, rfl, hj.trans hΓ, hother⟩

/-- Every conventional derivation yields a flow derivation whose output context is dead. -/
theorem Lin.toFlow {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) :
    Flow Γ.embed t A Γ.embed.dag := by
  induction h with
  | var i A =>
    have : (LCtx.single i A).embed.dag = Function.update (LCtx.single i A).embed i .dead := by
      funext j; by_cases hj : j = i
      · subst hj; simp [LCtx.single]
      · simp [LCtx.single, hj]
    rw [this]; exact .var (by simp [LCtx.single])
  | letIn hs _ _ ih₁ ih₂ =>
    rw [LCtx.embed_cons, Ctx.dag_cons] at ih₂
    exact .letIn (hs.flow_left ih₁) (hs.flow_right₁ ih₂)
  | lam _ ih =>
    rw [LCtx.embed_cons, Ctx.dag_cons] at ih
    exact .lam (Γ₁ := Ctx.empty _) (fun i => by simp [Ctx.empty]) ih
      (fun i => by simp [Ctx.empty])
  | app hs _ _ ih₁ ih₂ => exact .app (hs.flow_left ih₁) (hs.flow_right ih₂)
  | pair hs _ _ ih₁ ih₂ => exact .pair (hs.flow_left ih₁) (hs.flow_right ih₂)
  | letPair hs _ _ ih₁ ih₂ =>
    rw [LCtx.embed_cons, LCtx.embed_cons, Ctx.dag_cons, Ctx.dag_cons] at ih₂
    exact .letPair (hs.flow_left ih₁) (hs.flow_right₂ ih₂)
  | @unit n =>
    have : (LCtx.empty n).embed.dag = (LCtx.empty n).embed := by funext i; simp [LCtx.empty]
    rw [this]; exact .unit
  | letUnit hs _ _ ih₁ ih₂ => exact .letUnit (hs.flow_left ih₁) (hs.flow_right ih₂)
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case hs _ _ _ ih₁ ih₂ ih₃ =>
    rw [LCtx.embed_cons, Ctx.dag_cons] at ih₂ ih₃
    exact .case (hs.flow_left ih₁) (hs.flow_right₁ ih₂) (hs.flow_right₁ ih₃)
  | falseE _ ih => exact .falseE ih
  | withPair _ _ ih₁ ih₂ =>
    exact .withPair (Γ₁ := Ctx.empty _) (fun i => by simp [Ctx.empty]) ih₁ ih₂
      (fun i => by simp [Ctx.empty])
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | trueI _ ih => exact .trueI ih
  | @promote n k Γ Γs ts t As B hs _ _ ih ihb =>
    classical
    let C : Fin (k + 1) → Ctx n := fun m i =>
      if ∃ j : Fin k, j.val < m.val ∧ Γs j i ≠ none then .dead else Entry.ofOption (Γ i)
    have hb : Flow (fun j => .live (.bang (As j))) t B (fun _ => .dead) := by
      convert ihb using 1
    have h0 : C 0 = Γ.embed := by funext i; simp [C]
    have hlast : C (Fin.last k) = Γ.embed.dag := by
      funext i
      rcases hs.cases i with ⟨hΓ, hall⟩ | ⟨j, A, hΓ, hj, -⟩
      · simp [C, hΓ, hall]
      · have : ∃ j' : Fin k, j'.val < (Fin.last k).val ∧ Γs j' i ≠ none :=
          ⟨j, j.isLt, by simp [hj]⟩
        simp only [C, if_pos this, Ctx.dag_apply, LCtx.embed_apply, hΓ, Entry.ofOption_some,
          Entry.dag_live]
    have hstep : ∀ j : Fin k, Flow (C j.castSucc) (ts j) (.bang (As j)) (C j.succ) := by
      intro j
      let Θ : Ctx n := fun i => if Γs j i = none then C j.castSucc i else .absent
      have := (ih j).frame Θ (fun i => by
        by_cases h : Γs j i = none
        · left; simp [h]
        · right; simp [Θ, h])
      convert this using 1
      · funext i
        by_cases h : Γs j i = none
        · simp [Θ, h]
        · rcases hs.cases i with ⟨-, hall⟩ | ⟨j', A, hΓ, hj', hother⟩
          · exact absurd (hall j) h
          · have hjj : j = j' := by
              by_contra hne; exact h (hother j hne)
            subst hjj
            have : ¬ ∃ j'' : Fin k, j''.val < j.castSucc.val ∧ Γs j'' i ≠ none := by
              rintro ⟨j'', hlt, hne⟩
              exact hne (hother j'' (fun he => by subst he; simp at hlt))
            simp only [C, Θ, Ctx.overlay_apply, LCtx.embed_apply, if_neg this, hj', hΓ,
              Entry.ofOption_some, Entry.overlay_live]
      · funext i
        by_cases h : Γs j i = none
        · simp only [Θ, C, h, if_true, Ctx.overlay_apply, Ctx.dag_apply, LCtx.embed_apply,
            Entry.ofOption_none, Entry.dag_absent, Entry.overlay_absent_left]
          congr 1
          apply propext
          constructor
          · rintro ⟨j'', hlt, hne⟩
            refine ⟨j'', ?_, hne⟩
            simp only [Fin.val_succ] at hlt
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · simpa using hlt
            · exact absurd (by rw [show j'' = j from Fin.ext heq]; exact h) hne
          · rintro ⟨j'', hlt, hne⟩
            exact ⟨j'', by simp at hlt ⊢; omega, hne⟩
        · have : ∃ j'' : Fin k, j''.val < j.succ.val ∧ Γs j'' i ≠ none :=
            ⟨j, by simp, h⟩
          obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 h
          simp only [C, Θ, Ctx.overlay_apply, Ctx.dag_apply, LCtx.embed_apply, if_pos this, hA,
            Entry.ofOption_some, Entry.dag_live, Entry.overlay_dead]
    have := Flow.promote (Γs := C) hstep hb
    rwa [h0, hlast] at this
  | discard _ ih => exact .discard ih
  | copy _ ih => exact .copy ih
  | derelict _ ih => exact .derelict ih

/-! ## The main results of Section 4.6 -/

/-- **Lemma 4.7 (Frame rule).**  Let `x` (here the de Bruijn position `i`) be a variable that
is not in the contexts `Γ₁`, `Γ₂`.  Then
`Γ₁ ⊢ t : A ⊣ Γ₂ ⟺ Γ₁, x : B ⊢ t : A ⊣ Γ₂, x : B ⟺ Γ₁, x† ⊢ t : A ⊣ Γ₂, x†`.

The paper additionally assumes that `x` does not occur free in `t`; this hypothesis turns
out not to be needed. -/
theorem Flow.frame_rule {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t : Term n} {A : Ty} {i : Fin n}
    (h₁ : Γ₁ i = .absent) (h₂ : Γ₂ i = .absent) (B : Ty) :
    (Flow Γ₁ t A Γ₂ ↔
      Flow (Function.update Γ₁ i (.live B)) t A (Function.update Γ₂ i (.live B))) ∧
    (Flow Γ₁ t A Γ₂ ↔
      Flow (Function.update Γ₁ i .dead) t A (Function.update Γ₂ i .dead)) := by
  have key : ∀ e : Entry, e ≠ .absent →
      (Flow Γ₁ t A Γ₂ ↔ Flow (Function.update Γ₁ i e) t A (Function.update Γ₂ i e)) := by
    intro e he
    have ov : ∀ Γ : Ctx n, Γ i = .absent →
        Γ.overlay (Function.update (Ctx.empty n) i e) = Function.update Γ i e := by
      intro Γ hΓ
      funext j; by_cases hj : j = i
      · subst hj; simp [hΓ]
      · simp [Function.update_of_ne hj, Ctx.empty]
    constructor
    · intro h
      have := h.frame (Function.update (Ctx.empty n) i e) (fun j => by
        by_cases hj : j = i
        · subst hj; exact Or.inl h₁
        · right; simp [Function.update_of_ne hj, Ctx.empty])
      rwa [ov Γ₁ h₁, ov Γ₂ h₂] at this
    · intro h
      have := h.strengthen i (by simp)
      simp only [Function.update_idem] at this
      rwa [Function.update_eq_self_iff.2 h₁.symm, Function.update_eq_self_iff.2 h₂.symm] at this
  exact ⟨key _ (by simp), key _ (by simp)⟩

/-- **Theorem 4.6.**  For a conventional `λL` context `Γ` and a term `t`,
`Γ ⊢ t : A ⟺ Γ ⊢ t : A ⊣ Γ†`. -/
theorem lin_iff_flow {n : ℕ} (Γ : LCtx n) (t : Term n) (A : Ty) :
    Lin Γ t A ↔ Flow Γ.embed t A Γ.embed.dag := by
  refine ⟨Lin.toFlow, fun h => ?_⟩
  have e : Γ.embed.consumed Γ.embed.dag = Γ := by
    funext i; cases h : Γ i <;> simp [h]
  simpa [e] using h.toLin

/-- Theorem 4.6 for a context in which all `n` variables are in scope:
`x₁ : A₁, …, xₙ : Aₙ ⊢ t : A ⟺ x₁ : A₁, …, xₙ : Aₙ ⊢ t : A ⊣ x₁†, …, xₙ†`. -/
theorem lin_iff_flow_full {n : ℕ} (Γ : Fin n → Ty) (t : Term n) (A : Ty) :
    Lin (fun i => some (Γ i)) t A ↔ Flow (fun i => .live (Γ i)) t A (fun _ => .dead) := by
  rw [lin_iff_flow]
  have e₁ : LCtx.embed (fun i => some (Γ i)) = fun i => .live (Γ i) := rfl
  have e₂ : Ctx.dag (fun i => Entry.live (Γ i)) = fun _ => .dead := rfl
  rw [e₁, e₂]

/-- Theorem 4.6 for closed terms: `⊢ t : A ⟺ ⊢ t : A ⊣`. -/
theorem lin_iff_flow_closed (t : Term 0) (A : Ty) :
    Lin (LCtx.empty 0) t A ↔ Flow (Ctx.empty 0) t A (Ctx.empty 0) := by
  rw [lin_iff_flow]
  have e₁ : (LCtx.empty 0).embed = Ctx.empty 0 := funext fun i => i.elim0
  have e₂ : (Ctx.empty 0).dag = Ctx.empty 0 := funext fun i => i.elim0
  rw [e₁, e₂]

end FlowTyping
