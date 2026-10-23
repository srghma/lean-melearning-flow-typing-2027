module
public import RequestProject.FlowTyping.Metatheory

/-!
# Flow judgements of `λL` are lenses (Section 4.1)

Every flow judgement `Γ₁ ⊢ t : A ⊣ Γ₂` of `λL` is interpreted by a *closed* `λL` term of the
lens type `(Γ₁°, Γ₂°) → (A, 1)` that is well typed in the conventional type system of Fig. 2
(`FlowTyping.Flow.lens_exists`).

The construction uses renamings of de Bruijn terms (`Term.rename`), which preserve typing
(`Lin.rename`).
-/

@[expose] public section

namespace FlowTyping

/-! ## Renaming -/

/-- Lifting a renaming under a binder. -/
def liftRen {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] lemma liftRen_zero {n m : ℕ} (ρ : Fin n → Fin m) : liftRen ρ 0 = 0 := rfl
@[simp] lemma liftRen_succ {n m : ℕ} (ρ : Fin n → Fin m) (i : Fin n) :
    liftRen ρ i.succ = (ρ i).succ := rfl

lemma liftRen_injective {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) :
    Function.Injective (liftRen ρ) := by
  intro a b h
  cases a using Fin.cases <;> cases b using Fin.cases
  · rfl
  · exact absurd h.symm (Fin.succ_ne_zero _)
  · exact absurd h (Fin.succ_ne_zero _)
  · simp only [liftRen_succ, Fin.succ_inj] at h; rw [hρ h]

/-- Renaming the free variables of a term. -/
def Term.rename : {n m : ℕ} → (Fin n → Fin m) → Term n → Term m
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, ρ, .letIn t₁ t₂ => .letIn (t₁.rename ρ) (t₂.rename (liftRen ρ))
  | _, _, ρ, .lam A t => .lam A (t.rename (liftRen ρ))
  | _, _, ρ, .app t₁ t₂ => .app (t₁.rename ρ) (t₂.rename ρ)
  | _, _, ρ, .pair t₁ t₂ => .pair (t₁.rename ρ) (t₂.rename ρ)
  | _, _, ρ, .letPair t₁ t₂ => .letPair (t₁.rename ρ) (t₂.rename (liftRen (liftRen ρ)))
  | _, _, _, .unit => .unit
  | _, _, ρ, .letUnit t₁ t₂ => .letUnit (t₁.rename ρ) (t₂.rename ρ)
  | _, _, ρ, .inl A B t => .inl A B (t.rename ρ)
  | _, _, ρ, .inr A B t => .inr A B (t.rename ρ)
  | _, _, ρ, .case t t₁ t₂ => .case (t.rename ρ) (t₁.rename (liftRen ρ)) (t₂.rename (liftRen ρ))
  | _, _, ρ, .falseE B t => .falseE B (t.rename ρ)
  | _, _, ρ, .withPair t₁ t₂ => .withPair (t₁.rename ρ) (t₂.rename ρ)
  | _, _, ρ, .fst t => .fst (t.rename ρ)
  | _, _, ρ, .snd t => .snd (t.rename ρ)
  | _, _, ρ, .trueI t => .trueI (t.rename ρ)
  | _, _, ρ, .promote k ts t => .promote k (fun j => (ts j).rename ρ) t
  | _, _, ρ, .discard t => .discard (t.rename ρ)
  | _, _, ρ, .copy t => .copy (t.rename ρ)
  | _, _, ρ, .derelict t => .derelict (t.rename ρ)

open Classical in
/-- Push-forward of a linear context along a renaming. -/
noncomputable def LCtx.push {n m : ℕ} (ρ : Fin n → Fin m) (Γ : LCtx n) : LCtx m :=
  fun j => if h : ∃ i, ρ i = j then Γ h.choose else none

lemma LCtx.push_apply {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (Γ : LCtx n)
    (i : Fin n) : LCtx.push ρ Γ (ρ i) = Γ i := by
  have h : ∃ i', ρ i' = ρ i := ⟨i, rfl⟩
  simp only [LCtx.push, dif_pos h]
  rw [hρ h.choose_spec]

lemma LCtx.push_of_not_mem {n m : ℕ} (ρ : Fin n → Fin m) (Γ : LCtx n) {j : Fin m}
    (hj : ∀ i, ρ i ≠ j) : LCtx.push ρ Γ j = none := by
  simp only [LCtx.push]
  rw [dif_neg (by push_neg; exact hj)]

/-- Two contexts agree if they agree on the image of `ρ` and vanish outside it. -/
lemma LCtx.push_ext {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) {Γ : LCtx n}
    {Γ' : LCtx m} (h₁ : ∀ i, Γ' (ρ i) = Γ i) (h₂ : ∀ j, (∀ i, ρ i ≠ j) → Γ' j = none) :
    LCtx.push ρ Γ = Γ' := by
  funext j
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj; rw [LCtx.push_apply hρ, h₁]
  · push_neg at hj; rw [LCtx.push_of_not_mem _ _ hj, h₂ j hj]

lemma LCtx.push_cons {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ) (a : Option Ty)
    (Γ : LCtx n) :
    LCtx.push (liftRen ρ) (Fin.cons a Γ : LCtx (n + 1)) = Fin.cons a (LCtx.push ρ Γ) := by
  refine LCtx.push_ext (liftRen_injective hρ) (fun i => ?_) (fun j hj => ?_)
  · cases i using Fin.cases with
    | zero => rfl
    | succ i => simp [LCtx.push_apply hρ]
  · cases j using Fin.cases with
    | zero => exact absurd rfl (hj 0)
    | succ j =>
      simp only [Fin.cons_succ]
      exact LCtx.push_of_not_mem _ _ (fun i h => hj i.succ (by simp [h]))

lemma LCtx.Split.push {n m : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Γ Γ₁ Γ₂ : LCtx n} (hs : Γ.Split Γ₁ Γ₂) :
    (LCtx.push ρ Γ).Split (LCtx.push ρ Γ₁) (LCtx.push ρ Γ₂) := fun j => by
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj
    simp only [LCtx.push_apply hρ]; exact hs i
  · push_neg at hj
    simp [LCtx.push_of_not_mem _ _ hj]

lemma LCtx.SplitN.push {n m k : ℕ} {ρ : Fin n → Fin m} (hρ : Function.Injective ρ)
    {Γ : LCtx n} {Γs : Fin k → LCtx n} (hs : Γ.SplitN Γs) :
    (LCtx.push ρ Γ).SplitN (fun j => LCtx.push ρ (Γs j)) := fun j => by
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj
    simp only [LCtx.push_apply hρ]; exact hs i
  · push_neg at hj
    left; simp [LCtx.push_of_not_mem _ _ hj]

/-- Renaming along an injective map preserves conventional typing. -/
theorem Lin.rename {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) :
    ∀ {m : ℕ} (ρ : Fin n → Fin m), Function.Injective ρ →
      Lin (LCtx.push ρ Γ) (t.rename ρ) A := by
  induction h with
  | var i A =>
    intro m ρ hρ
    have : LCtx.push ρ (LCtx.single i A) = LCtx.single (ρ i) A := by
      refine LCtx.push_ext hρ (fun i' => ?_) (fun j hj => ?_)
      · simp [LCtx.single, hρ.eq_iff]
      · simp only [LCtx.single]; rw [if_neg (fun h => hj i h.symm)]
    rw [this]; exact .var _ _
  | letIn hs _ _ ih₁ ih₂ =>
    intro m ρ hρ
    have := ih₂ (liftRen ρ) (liftRen_injective hρ)
    rw [LCtx.push_cons hρ] at this
    exact .letIn (hs.push hρ) (ih₁ ρ hρ) this
  | lam _ ih =>
    intro m ρ hρ
    have := ih (liftRen ρ) (liftRen_injective hρ)
    rw [LCtx.push_cons hρ] at this
    exact .lam this
  | app hs _ _ ih₁ ih₂ => intro m ρ hρ; exact .app (hs.push hρ) (ih₁ ρ hρ) (ih₂ ρ hρ)
  | pair hs _ _ ih₁ ih₂ => intro m ρ hρ; exact .pair (hs.push hρ) (ih₁ ρ hρ) (ih₂ ρ hρ)
  | letPair hs _ _ ih₁ ih₂ =>
    intro m ρ hρ
    have := ih₂ (liftRen (liftRen ρ)) (liftRen_injective (liftRen_injective hρ))
    rw [LCtx.push_cons (liftRen_injective hρ), LCtx.push_cons hρ] at this
    exact .letPair (hs.push hρ) (ih₁ ρ hρ) this
  | @unit n =>
    intro m ρ hρ
    have : LCtx.push ρ (LCtx.empty n) = LCtx.empty m :=
      LCtx.push_ext hρ (fun _ => rfl) (fun _ _ => rfl)
    rw [this]; exact .unit
  | letUnit hs _ _ ih₁ ih₂ => intro m ρ hρ; exact .letUnit (hs.push hρ) (ih₁ ρ hρ) (ih₂ ρ hρ)
  | inl _ ih => intro m ρ hρ; exact .inl (ih ρ hρ)
  | inr _ ih => intro m ρ hρ; exact .inr (ih ρ hρ)
  | case hs _ _ _ ih₁ ih₂ ih₃ =>
    intro m ρ hρ
    have e₂ := ih₂ (liftRen ρ) (liftRen_injective hρ)
    have e₃ := ih₃ (liftRen ρ) (liftRen_injective hρ)
    rw [LCtx.push_cons hρ] at e₂ e₃
    exact .case (hs.push hρ) (ih₁ ρ hρ) e₂ e₃
  | falseE _ ih => intro m ρ hρ; exact .falseE (ih ρ hρ)
  | withPair _ _ ih₁ ih₂ => intro m ρ hρ; exact .withPair (ih₁ ρ hρ) (ih₂ ρ hρ)
  | fst _ ih => intro m ρ hρ; exact .fst (ih ρ hρ)
  | snd _ ih => intro m ρ hρ; exact .snd (ih ρ hρ)
  | trueI _ ih => intro m ρ hρ; exact .trueI (ih ρ hρ)
  | promote hs _ hb ih _ =>
    intro m ρ hρ
    exact .promote (hs.push hρ) (fun j => ih j ρ hρ) hb
  | discard _ ih => intro m ρ hρ; exact .discard (ih ρ hρ)
  | copy _ ih => intro m ρ hρ; exact .copy (ih ρ hρ)
  | derelict _ ih => intro m ρ hρ; exact .derelict (ih ρ hρ)

/-- Weakening a term by a fresh most-recent variable. -/
def Term.shift {n : ℕ} (t : Term n) : Term (n + 1) := t.rename Fin.succ

/-- Weakening a closed term into any scope. -/
def Term.weaken {m : ℕ} (t : Term 0) : Term m := t.rename Fin.elim0

lemma Lin.shift {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) :
    Lin (Fin.cons none Γ) t.shift A := by
  have := h.rename Fin.succ (Fin.succ_injective _)
  convert this using 1
  refine (LCtx.push_ext (Fin.succ_injective _) (fun i => rfl) (fun j hj => ?_)).symm
  cases j using Fin.cases with
  | zero => rfl
  | succ j => exact absurd rfl (hj j)

lemma Lin.weaken {m : ℕ} {t : Term 0} {A : Ty} (h : Lin (LCtx.empty 0) t A) :
    Lin (LCtx.empty m) t.weaken A := by
  have := h.rename (m := m) Fin.elim0 (fun a => a.elim0)
  convert this using 1

/-- Discharge a concrete context-splitting obligation at a single position. -/
local macro "split_tac" : tactic =>
  `(tactic| first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩)

/-! ## Packing and unpacking contexts -/

/-- The live part of a flow context, as a conventional linear context. -/
def Ctx.liveOf {n : ℕ} (Γ : Ctx n) : LCtx n := fun i =>
  match Γ i with
  | .live A => some A
  | _ => none

lemma Ctx.liveOf_succ {n : ℕ} (Γ : Ctx (n + 1)) :
    Γ.liveOf = Fin.cons (Γ.liveOf 0) (Ctx.liveOf (Fin.tail Γ)) := by
  funext i; cases i using Fin.cases <;> rfl

/-- The term `(∗, x₁, …, xₖ)` packing the live variables of a context into a value of type
`Γ°`. -/
def Ctx.pack : {n : ℕ} → Ctx n → Term n
  | 0, _ => .unit
  | _ + 1, Γ =>
    match Γ 0 with
    | .live _ => .pair (Ctx.pack (Fin.tail Γ)).shift (.var 0)
    | _ => (Ctx.pack (Fin.tail Γ)).shift

theorem Ctx.pack_typing : ∀ {n : ℕ} (Γ : Ctx n), Lin Γ.liveOf Γ.pack Γ.toTy
  | 0, Γ => by
    have : Γ.liveOf = LCtx.empty 0 := funext fun i => i.elim0
    rw [this]; exact .unit
  | n + 1, Γ => by
    have ih := (Ctx.pack_typing (Fin.tail Γ)).shift
    rw [Ctx.liveOf_succ]
    cases h : Γ 0 with
    | live A =>
      simp only [Ctx.pack, Ctx.toTy, h, Ctx.liveOf]
      refine .pair (Γ₁ := Fin.cons none (Ctx.liveOf (Fin.tail Γ))) (Γ₂ := LCtx.single 0 A)
        (fun i => ?_) ih (.var 0 A)
      cases i using Fin.cases with
      | zero => left; simp [LCtx.single]
      | succ i => right; simp [LCtx.single, Fin.succ_ne_zero]
    | absent => simpa [Ctx.pack, Ctx.toTy, h, Ctx.liveOf] using ih
    | dead => simpa [Ctx.pack, Ctx.toTy, h, Ctx.liveOf] using ih

/-- Closing an open term over the live variables of `Γ` into a closed function `Γ° ⊸ B`. -/
theorem Ctx.close : ∀ {n : ℕ} (Γ : Ctx n) (b : Term n) (B : Ty), Lin Γ.liveOf b B →
    ∃ c : Term 0, Lin (LCtx.empty 0) c (.lolli Γ.toTy B)
  | 0, Γ, b, B, h => by
    have e : Γ.liveOf = LCtx.empty 0 := funext fun i => i.elim0
    rw [e] at h
    refine ⟨.lam .one (.letUnit (.var 0) b.weaken), .lam ?_⟩
    exact .letUnit (Γ₁ := LCtx.single 0 .one) (Γ₂ := LCtx.empty 1)
      (fun i => by fin_cases i; right; simp [LCtx.single, LCtx.empty]) (.var 0 _) h.weaken
  | n + 1, Γ, b, B, h => by
    rw [Ctx.liveOf_succ] at h
    cases h0 : Γ 0 with
    | live X =>
      simp only [Ctx.liveOf, h0] at h
      obtain ⟨c, hc⟩ := Ctx.close (Fin.tail Γ) (.lam X b) (.lolli X B) (.lam h)
      simp only [Ctx.toTy, h0]
      refine ⟨.lam (.tensor (Ctx.toTy (Fin.tail Γ)) X)
        (.letPair (.var 0) (.app (.app c.weaken (.var 1)) (.var 0))), .lam ?_⟩
      refine .letPair (Γ₁ := LCtx.single 0 (.tensor (Ctx.toTy (Fin.tail Γ)) X))
        (Γ₂ := LCtx.empty 1) (fun i => by fin_cases i; split_tac) (.var 0 _) ?_
      refine .app (Γ₁ := LCtx.single 1 (Ctx.toTy (Fin.tail Γ))) (Γ₂ := LCtx.single 0 X)
        (fun i => by fin_cases i <;> split_tac) ?_ (.var 0 X)
      exact .app (Γ₁ := LCtx.empty 3) (Γ₂ := LCtx.single 1 (Ctx.toTy (Fin.tail Γ)))
        (fun i => by fin_cases i <;> split_tac) hc.weaken (.var 1 _)
    | absent | dead =>
      simp only [Ctx.liveOf, h0] at h
      have h' : Lin (Fin.cons (some .one) (Ctx.liveOf (Fin.tail Γ))) (.letUnit (.var 0) b) B :=
        .letUnit (Γ₁ := LCtx.single 0 .one) (Γ₂ := Fin.cons none (Ctx.liveOf (Fin.tail Γ)))
          (fun i => by
            cases i using Fin.cases with
            | zero => right; simp [LCtx.single]
            | succ i => left; simp [LCtx.single, Fin.succ_ne_zero]) (.var 0 _) h
      obtain ⟨c, hc⟩ := Ctx.close (Fin.tail Γ) (.lam .one (.letUnit (.var 0) b))
        (.lolli .one B) (.lam h')
      simp only [Ctx.toTy, h0]
      refine ⟨.lam (Ctx.toTy (Fin.tail Γ)) (.app (.app c.weaken (.var 0)) .unit), .lam ?_⟩
      refine .app (Γ₁ := Fin.cons (some (Ctx.toTy (Fin.tail Γ))) (LCtx.empty 0))
        (Γ₂ := LCtx.empty 1) (fun i => by fin_cases i; split_tac) ?_ .unit
      exact .app (Γ₁ := LCtx.empty 1) (Γ₂ := LCtx.single 0 (Ctx.toTy (Fin.tail Γ)))
        (fun i => by fin_cases i; split_tac) hc.weaken (.var 0 _)

/-! ## The lens interpretation of flow judgements -/

lemma Ctx.liveOf_split {n : ℕ} {Γ Δ : Ctx n} (h : ∀ i, (Γ i).Step (Δ i)) :
    Γ.liveOf.Split (Γ.consumed Δ) Δ.liveOf := fun i => by
  rcases h i with h' | ⟨⟨A, hA⟩, h'⟩
  · left; refine ⟨?_, ?_⟩
    · simp [h']
    · simp only [Ctx.liveOf, h']
  · right; simp [Ctx.liveOf, hA, h']

/-- **Section 4.1.**  Every flow judgement `Γ₁ ⊢ t : A ⊣ Γ₂` of `λL` is realised by a closed,
conventionally well-typed `λL` lens of type `(Γ₁°, Γ₂°) → (A, 1)`. -/
theorem Flow.lens_exists {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    ∃ l : Term 0, Lin (LCtx.empty 0) l (lensTy Γ.toTy Δ.toTy A .one) := by
  have hres : Lin Δ.liveOf (.lam .one (.letUnit (.var 0) Δ.pack.shift)) (.lolli .one Δ.toTy) := by
    refine .lam (.letUnit (Γ₁ := LCtx.single 0 .one) (Γ₂ := Fin.cons none Δ.liveOf)
      (fun i => ?_) (.var 0 _) Δ.pack_typing.shift)
    cases i using Fin.cases with
    | zero => right; simp [LCtx.single]
    | succ i => left; simp [LCtx.single, Fin.succ_ne_zero]
  exact Ctx.close Γ _ _ (.pair (Ctx.liveOf_split h.step) h.toLin hres)

end FlowTyping
