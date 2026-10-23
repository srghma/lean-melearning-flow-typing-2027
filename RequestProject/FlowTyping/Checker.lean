module
public import RequestProject.FlowTyping.Substitution

/-!
# A verified type checker for `λL`, and closed inhabitants

This file provides proof infrastructure for building closed, conventionally well-typed `λL`
terms (used for the lens translation of Appendix C):

* `Ty.tsubst`, `Term.tsubst`, `Lin.tsubst`: substitution of types for type variables
  preserves typing, so a term checked at type variables `α₀, α₁, …` can be instantiated at
  arbitrary types.
* `check τ t`: a type checker for terms whose variables have the types `τ`; it returns the type
  of `t` together with the set of variables used.  `check_sound` proves it sound for `Lin`.
* `Inh A`: the type `A` has a closed, well-typed inhabitant.  `Inh.of_check` turns a successful
  run of the checker on an open term into an implication between inhabited types.
-/

@[expose] public section

namespace FlowTyping

/-! ## Substituting types for type variables -/

/-- Substitution of types for the type variables of a type. -/
def Ty.tsubst (σ : ℕ → Ty) : Ty → Ty
  | .tvar a => σ a
  | .lolli A B => .lolli (A.tsubst σ) (B.tsubst σ)
  | .tensor A B => .tensor (A.tsubst σ) (B.tsubst σ)
  | .one => .one
  | .plus A B => .plus (A.tsubst σ) (B.tsubst σ)
  | .zero => .zero
  | .with A B => .with (A.tsubst σ) (B.tsubst σ)
  | .top => .top
  | .bang A => .bang (A.tsubst σ)

/-- Substitution of types for the type variables occurring in the annotations of a term. -/
def Term.tsubst (σ : ℕ → Ty) : {n : ℕ} → Term n → Term n
  | _, .var i => .var i
  | _, .letIn t₁ t₂ => .letIn (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .lam A t => .lam (A.tsubst σ) (t.tsubst σ)
  | _, .app t₁ t₂ => .app (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .pair t₁ t₂ => .pair (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .letPair t₁ t₂ => .letPair (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .unit => .unit
  | _, .letUnit t₁ t₂ => .letUnit (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .inl A B t => .inl (A.tsubst σ) (B.tsubst σ) (t.tsubst σ)
  | _, .inr A B t => .inr (A.tsubst σ) (B.tsubst σ) (t.tsubst σ)
  | _, .case t t₁ t₂ => .case (t.tsubst σ) (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .falseE B t => .falseE (B.tsubst σ) (t.tsubst σ)
  | _, .withPair t₁ t₂ => .withPair (t₁.tsubst σ) (t₂.tsubst σ)
  | _, .fst t => .fst (t.tsubst σ)
  | _, .snd t => .snd (t.tsubst σ)
  | _, .trueI t => .trueI (t.tsubst σ)
  | _, .promote k ts t => .promote k (fun j => (ts j).tsubst σ) (t.tsubst σ)
  | _, .discard t => .discard (t.tsubst σ)
  | _, .copy t => .copy (t.tsubst σ)
  | _, .derelict t => .derelict (t.tsubst σ)

/-- Type substitution in a linear context. -/
def LCtx.tsubst {n : ℕ} (σ : ℕ → Ty) (Γ : LCtx n) : LCtx n := fun i => (Γ i).map (Ty.tsubst σ)

lemma LCtx.Split.tsubst {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} (σ : ℕ → Ty) (hs : Γ.Split Γ₁ Γ₂) :
    (Γ.tsubst σ).Split (Γ₁.tsubst σ) (Γ₂.tsubst σ) := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; simp [LCtx.tsubst, h1, h2]
  · right; simp [LCtx.tsubst, h1, h2]

lemma LCtx.SplitN.tsubst {n k : ℕ} {Γ : LCtx n} {Γs : Fin k → LCtx n} (σ : ℕ → Ty)
    (hs : Γ.SplitN Γs) : (Γ.tsubst σ).SplitN (fun j => (Γs j).tsubst σ) := fun i => by
  rcases hs i with ⟨h1, h2⟩ | ⟨j, h1, h2⟩
  · left; simp [LCtx.tsubst, h1, h2]
  · right; exact ⟨j, by simp [LCtx.tsubst, h1], fun j' hj' => by simp [LCtx.tsubst, h2 j' hj']⟩

lemma LCtx.tsubst_cons {n : ℕ} (σ : ℕ → Ty) (A : Ty) (Γ : LCtx n) :
    LCtx.tsubst σ (Fin.cons (some A) Γ : LCtx (n + 1)) = Fin.cons (some (A.tsubst σ)) (Γ.tsubst σ) := by
  funext i; cases i using Fin.cases <;> rfl

/-- Substituting types for type variables preserves typing. -/
theorem Lin.tsubst {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) (σ : ℕ → Ty) :
    Lin (Γ.tsubst σ) (t.tsubst σ) (A.tsubst σ) := by
  induction h with
  | var i A =>
    have : (LCtx.single i A).tsubst σ = LCtx.single i (A.tsubst σ) := by
      funext j; simp only [LCtx.tsubst, LCtx.single]; split_ifs <;> rfl
    rw [this]; exact .var _ _
  | letIn hs _ _ ih₁ ih₂ =>
    rw [LCtx.tsubst_cons] at ih₂; exact .letIn (hs.tsubst σ) ih₁ ih₂
  | lam _ ih => rw [LCtx.tsubst_cons] at ih; exact .lam ih
  | app hs _ _ ih₁ ih₂ => exact .app (hs.tsubst σ) ih₁ ih₂
  | pair hs _ _ ih₁ ih₂ => exact .pair (hs.tsubst σ) ih₁ ih₂
  | letPair hs _ _ ih₁ ih₂ =>
    rw [LCtx.tsubst_cons, LCtx.tsubst_cons] at ih₂; exact .letPair (hs.tsubst σ) ih₁ ih₂
  | @unit n =>
    have : (LCtx.empty n).tsubst σ = LCtx.empty n := rfl
    rw [this]; exact .unit
  | letUnit hs _ _ ih₁ ih₂ => exact .letUnit (hs.tsubst σ) ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case hs _ _ _ ih₁ ih₂ ih₃ =>
    rw [LCtx.tsubst_cons] at ih₂ ih₃; exact .case (hs.tsubst σ) ih₁ ih₂ ih₃
  | falseE _ ih => exact .falseE ih
  | withPair _ _ ih₁ ih₂ => exact .withPair ih₁ ih₂
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | trueI _ ih => exact .trueI ih
  | promote hs _ _ ih ihb =>
    refine .promote (As := fun j => _) (hs.tsubst σ) (fun j => ih j) ?_
    exact ihb
  | discard _ ih => exact .discard ih
  | copy _ ih => exact .copy ih
  | derelict _ ih => exact .derelict ih

/-! ## The checker -/

namespace Check

/-- `uDisj U V`: the usages `U` and `V` are disjoint. -/
def uDisj {n : ℕ} (U V : Fin n → Bool) : Bool := (List.finRange n).all fun i => !(U i && V i)

/-- Equality of usages. -/
def uEq {n : ℕ} (U V : Fin n → Bool) : Bool := (List.finRange n).all fun i => U i == V i

/-- Union of usages. -/
def uUnion {n : ℕ} (U V : Fin n → Bool) : Fin n → Bool := fun i => U i || V i

/-- Pairwise disjointness of a family of usages. -/
def uPairwise {n k : ℕ} (Us : Fin k → Fin n → Bool) : Bool :=
  (List.finRange k).all fun j => (List.finRange k).all fun j' => j == j' || uDisj (Us j) (Us j')

/-- Union of a family of usages. -/
def uBig {n k : ℕ} (Us : Fin k → Fin n → Bool) : Fin n → Bool :=
  fun i => (List.finRange k).any fun j => Us j i

/-- All entries of a family of options are present. -/
def allSome {α : Type} : {k : ℕ} → (Fin k → Option α) → Option (Fin k → α)
  | 0, _ => some Fin.elim0
  | _ + 1, f =>
    match f 0, allSome (Fin.tail f) with
    | some a, some g => some (Fin.cons a g)
    | _, _ => none

lemma allSome_spec {α : Type} : ∀ {k : ℕ} {f : Fin k → Option α} {g : Fin k → α},
    allSome f = some g → ∀ j, f j = some (g j)
  | 0, _, _, _, j => j.elim0
  | k + 1, f, g, h, j => by
    simp only [allSome] at h
    split at h
    · rename_i a g' h0 h1
      simp only [Option.some.injEq] at h; subst h
      cases j using Fin.cases with
      | zero => simpa using h0
      | succ j => simpa using allSome_spec h1 j
    · cases h

lemma uDisj_spec {n : ℕ} {U V : Fin n → Bool} (h : uDisj U V = true) (i : Fin n) :
    ¬ (U i = true ∧ V i = true) := by
  simp only [uDisj, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_false_iff] at h
  rcases h i with h | h <;> simp [h]

lemma uEq_spec {n : ℕ} {U V : Fin n → Bool} (h : uEq U V = true) : U = V := by
  funext i
  simp only [uEq, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i

lemma uPairwise_spec {n k : ℕ} {Us : Fin k → Fin n → Bool} (h : uPairwise Us = true)
    {j j' : Fin k} (hj : j ≠ j') : uDisj (Us j) (Us j') = true := by
  simp only [uPairwise, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h j j' with h | h
  · exact absurd h hj
  · exact h

lemma uBig_spec {n k : ℕ} {Us : Fin k → Fin n → Bool} (i : Fin n) :
    uBig Us i = true ↔ ∃ j, Us j i = true := by
  simp [uBig]

/-- The type of a promotable term must be `!A`. -/
def unbang : Ty → Option Ty
  | .bang A => some A
  | _ => none

lemma unbang_spec {A B : Ty} (h : unbang A = some B) : A = .bang B := by
  cases A <;> simp_all [unbang]

end Check

open Check

/-- The linear context of the variables `i` with `U i`, typed by `τ`. -/
def restrict {n : ℕ} (τ : Fin n → Ty) (U : Fin n → Bool) : LCtx n :=
  fun i => if U i then some (τ i) else none

/-- A type checker for `λL`: `check τ t = some (A, U)` means that `t` has type `A` using
exactly the variables `U` (with types given by `τ`). -/
def check : {n : ℕ} → (Fin n → Ty) → Term n → Option (Ty × (Fin n → Bool))
  | _, τ, .var i => some (τ i, fun j => decide (j = i))
  | _, τ, .letIn t₁ t₂ =>
    match check τ t₁ with
    | some (A, U₁) =>
      match check (Fin.cons A τ) t₂ with
      | some (B, U₂) =>
        if U₂ 0 && uDisj U₁ (Fin.tail U₂) then some (B, uUnion U₁ (Fin.tail U₂)) else none
      | none => none
    | none => none
  | _, τ, .lam A t =>
    match check (Fin.cons A τ) t with
    | some (B, U) => if U 0 then some (.lolli A B, Fin.tail U) else none
    | none => none
  | _, τ, .app t₁ t₂ =>
    match check τ t₁, check τ t₂ with
    | some (.lolli A B, U₁), some (A', U₂) =>
      if A = A' ∧ uDisj U₁ U₂ = true then some (B, uUnion U₁ U₂) else none
    | _, _ => none
  | _, τ, .pair t₁ t₂ =>
    match check τ t₁, check τ t₂ with
    | some (A, U₁), some (B, U₂) =>
      if uDisj U₁ U₂ then some (.tensor A B, uUnion U₁ U₂) else none
    | _, _ => none
  | _, τ, .letPair t₁ t₂ =>
    match check τ t₁ with
    | some (.tensor A B, U₁) =>
      match check (Fin.cons B (Fin.cons A τ)) t₂ with
      | some (C, U₂) =>
        if U₂ 0 && U₂ 1 && uDisj U₁ (Fin.tail (Fin.tail U₂)) then
          some (C, uUnion U₁ (Fin.tail (Fin.tail U₂)))
        else none
      | none => none
    | _ => none
  | _, _, .unit => some (.one, fun _ => false)
  | _, τ, .letUnit t₁ t₂ =>
    match check τ t₁, check τ t₂ with
    | some (.one, U₁), some (A, U₂) =>
      if uDisj U₁ U₂ then some (A, uUnion U₁ U₂) else none
    | _, _ => none
  | _, τ, .inl A B t =>
    match check τ t with
    | some (A', U) => if A' = A then some (.plus A B, U) else none
    | none => none
  | _, τ, .inr A B t =>
    match check τ t with
    | some (B', U) => if B' = B then some (.plus A B, U) else none
    | none => none
  | _, τ, .case t t₁ t₂ =>
    match check τ t with
    | some (.plus A B, U) =>
      match check (Fin.cons A τ) t₁, check (Fin.cons B τ) t₂ with
      | some (C₁, U₁), some (C₂, U₂) =>
        if C₁ = C₂ ∧ U₁ 0 = true ∧ U₂ 0 = true ∧ uEq (Fin.tail U₁) (Fin.tail U₂) = true ∧
            uDisj U (Fin.tail U₁) = true then
          some (C₁, uUnion U (Fin.tail U₁))
        else none
      | _, _ => none
    | _ => none
  | _, τ, .falseE B t =>
    match check τ t with
    | some (.zero, U) => some (B, U)
    | _ => none
  | _, τ, .withPair t₁ t₂ =>
    match check τ t₁, check τ t₂ with
    | some (A, U₁), some (B, U₂) => if uEq U₁ U₂ then some (.with A B, U₁) else none
    | _, _ => none
  | _, τ, .fst t =>
    match check τ t with
    | some (.with A _, U) => some (A, U)
    | _ => none
  | _, τ, .snd t =>
    match check τ t with
    | some (.with _ B, U) => some (B, U)
    | _ => none
  | _, τ, .trueI t =>
    match check τ t with
    | some (_, U) => some (.top, U)
    | none => none
  | _, τ, .promote _ ts t =>
    match allSome (fun j => check τ (ts j)) with
    | some rs =>
      match allSome (fun j => unbang (rs j).1) with
      | some As =>
        if uPairwise (fun j => (rs j).2) then
          match check (fun j => .bang (As j)) t with
          | some (B, U) =>
            if (List.finRange _).all U then some (.bang B, uBig (fun j => (rs j).2)) else none
          | none => none
        else none
      | none => none
    | none => none
  | _, τ, .discard t =>
    match check τ t with
    | some (.bang _, U) => some (.one, U)
    | _ => none
  | _, τ, .copy t =>
    match check τ t with
    | some (.bang A, U) => some (.tensor (.bang A) (.bang A), U)
    | _ => none
  | _, τ, .derelict t =>
    match check τ t with
    | some (.bang A, U) => some (A, U)
    | _ => none

lemma restrict_cons {n : ℕ} (τ : Fin n → Ty) (A : Ty) (U : Fin (n + 1) → Bool) (h : U 0 = true) :
    restrict (Fin.cons A τ) U = Fin.cons (some A) (restrict τ (Fin.tail U)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [restrict, h]
  | succ i => simp [restrict, Fin.tail]

lemma restrict_split {n : ℕ} (τ : Fin n → Ty) {U V : Fin n → Bool} (h : uDisj U V = true) :
    (restrict τ (uUnion U V)).Split (restrict τ U) (restrict τ V) := fun i => by
  have := uDisj_spec h i
  cases hU : U i <;> cases hV : V i <;> simp_all [restrict, uUnion]

lemma restrict_splitN {n k : ℕ} (τ : Fin n → Ty) {Us : Fin k → Fin n → Bool}
    (h : uPairwise Us = true) :
    (restrict τ (uBig Us)).SplitN (fun j => restrict τ (Us j)) := fun i => by
  by_cases hi : uBig Us i = true
  · obtain ⟨j, hj⟩ := (uBig_spec i).1 hi
    right
    refine ⟨j, by simp [restrict, hj, hi], fun j' hj' => ?_⟩
    have := uDisj_spec (uPairwise_spec h hj') i
    simp only [restrict]
    rw [if_neg]; intro h'; exact this ⟨h', hj⟩
  · left
    refine ⟨by simp [restrict, hi], fun j => ?_⟩
    simp only [restrict]
    rw [if_neg]; intro h'; exact hi ((uBig_spec i).2 ⟨j, h'⟩)

/-- **Soundness of the checker.** -/
theorem check_sound {n : ℕ} (t : Term n) :
    ∀ {τ : Fin n → Ty} {A : Ty} {U : Fin n → Bool}, check τ t = some (A, U) →
      Lin (restrict τ U) t A := by
  induction t with
  | var i =>
    intro τ A U h
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : restrict τ (fun j => decide (j = i)) = LCtx.single i (τ i) := by
      funext j; by_cases hj : j = i <;> simp [restrict, LCtx.single, hj]
    rw [this]; exact .var i _
  | letIn t₁ t₂ ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ h₁
    split at h <;> try cases h
    rename_i B U₂ h₂
    split at h <;> try cases h
    rename_i hc
    simp only [Bool.and_eq_true] at hc
    have e₂ := ih₂ h₂
    rw [restrict_cons _ _ _ hc.1] at e₂
    exact .letIn (restrict_split τ hc.2) (ih₁ h₁) e₂
  | lam B t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i C U' h₁
    split at h <;> try cases h
    rename_i hc
    have e := ih h₁
    rw [restrict_cons _ _ _ hc] at e
    exact .lam e
  | app t₁ t₂ ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ B₁ U₁ A₂ U₂ h₁ h₂
    split at h <;> try cases h
    rename_i hc
    obtain ⟨rfl, hd⟩ := hc
    exact .app (restrict_split τ hd) (ih₁ h₁) (ih₂ h₂)
  | pair t₁ t₂ ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ A₂ U₂ h₁ h₂
    split at h <;> try cases h
    rename_i hd
    exact .pair (restrict_split τ hd) (ih₁ h₁) (ih₂ h₂)
  | letPair t₁ t₂ ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ B₁ U₁ h₁
    split at h <;> try cases h
    rename_i C U₂ h₂
    split at h <;> try cases h
    rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hc0, hc1⟩, hd⟩ := hc
    have e₂ := ih₂ h₂
    rw [restrict_cons _ _ _ hc0, restrict_cons _ _ _ (by simpa [Fin.tail] using hc1)] at e₂
    exact .letPair (restrict_split τ hd) (ih₁ h₁) e₂
  | unit =>
    intro τ A U h
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : restrict τ (fun _ => false) = LCtx.empty _ := by funext j; simp [restrict, LCtx.empty]
    rw [this]; exact .unit
  | letUnit t₁ t₂ ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i U₁ A₂ U₂ h₁ h₂
    split at h <;> try cases h
    rename_i hd
    exact .letUnit (restrict_split τ hd) (ih₁ h₁) (ih₂ h₂)
  | inl B C t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A' U' h₁
    split at h <;> try cases h
    rename_i hc; subst hc
    exact .inl (ih h₁)
  | inr B C t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A' U' h₁
    split at h <;> try cases h
    rename_i hc; subst hc
    exact .inr (ih h₁)
  | case t t₁ t₂ ih ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₀ B₀ U₀ h₀
    split at h <;> try cases h
    rename_i C₁ U₁ C₂ U₂ h₁ h₂
    split at h <;> try cases h
    rename_i hc
    obtain ⟨rfl, hc1, hc2, he, hd⟩ := hc
    have e₁ := ih₁ h₁
    have e₂ := ih₂ h₂
    rw [restrict_cons _ _ _ hc1] at e₁
    rw [restrict_cons _ _ _ hc2, ← uEq_spec he] at e₂
    exact .case (restrict_split τ hd) (ih h₀) e₁ e₂
  | falseE B t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i U' h₁
    exact .falseE (ih h₁)
  | withPair t₁ t₂ ih₁ ih₂ =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ A₂ U₂ h₁ h₂
    split at h <;> try cases h
    rename_i he
    have e₂ := ih₂ h₂
    rw [← uEq_spec he] at e₂
    exact .withPair (ih₁ h₁) e₂
  | fst t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ B₁ U₁ h₁
    exact .fst (ih h₁)
  | snd t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ B₁ U₁ h₁
    exact .snd (ih h₁)
  | trueI t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ h₁
    exact .trueI (ih h₁)
  | promote k ts t ihs ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i rs hrs
    split at h <;> try cases h
    rename_i As hAs
    split at h <;> try cases h
    rename_i hp
    split at h <;> try cases h
    rename_i B U' hb
    split at h <;> try cases h
    rename_i hall
    have hrs' := allSome_spec hrs
    have hAs' := allSome_spec hAs
    have hall' : ∀ j, U' j = true := by
      simpa [List.all_eq_true] using hall
    have hbody := ih hb
    have : restrict (fun j => Ty.bang (As j)) U' = fun j => some (Ty.bang (As j)) := by
      funext j; simp [restrict, hall' j]
    rw [this] at hbody
    refine .promote (restrict_splitN τ hp) (fun j => ?_) hbody
    have e := ihs j (hrs' j)
    rwa [unbang_spec (hAs' j)] at e
  | discard t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ h₁
    exact .discard (ih h₁)
  | copy t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ h₁
    exact .copy (ih h₁)
  | derelict t ih =>
    intro τ A U h
    simp only [check] at h
    split at h <;> try cases h
    rename_i A₁ U₁ h₁
    exact .derelict (ih h₁)

/-! ## Closed inhabitants -/

/-- `Inh A`: there is a closed term of type `A`. -/
def Inh (A : Ty) : Prop := ∃ t : Term 0, Lin (LCtx.empty 0) t A

/-- Modus ponens for closed terms. -/
lemma Inh.mp {A B : Ty} (f : Inh (.lolli A B)) (a : Inh A) : Inh B := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨a, ha⟩ := a
  exact ⟨.app f a, .app (fun _ => Or.inl ⟨rfl, rfl⟩) hf ha⟩

/-- `checkAll τ t R`: the checker accepts `t` at type `R`, using all of its variables. -/
def checkAll {n : ℕ} (τ : Fin n → Ty) (t : Term n) (R : Ty) : Bool :=
  match check τ t with
  | some (A, U) => decide (A = R) && (List.finRange n).all U
  | none => false

lemma checkAll_sound {n : ℕ} {τ : Fin n → Ty} {t : Term n} {R : Ty} (h : checkAll τ t R = true) :
    Lin (fun i => some (τ i)) t R := by
  simp only [checkAll] at h
  split at h
  · rename_i A U hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies] at h
    obtain ⟨rfl, hU⟩ := h
    have := check_sound t hc
    have e : restrict τ U = fun i => some (τ i) := by funext i; simp [restrict, hU i]
    rwa [e] at this
  · cases h

/-- A successful run of the checker on a term all of whose (parameter) variables are used,
instantiated along a type substitution `σ`, gives an implication between inhabited types. -/
theorem Inh.of_check {n : ℕ} (τ : Fin n → Ty) (t : Term n) (R : Ty)
    (h : checkAll τ t R = true) (σ : ℕ → Ty)
    (args : ∀ i, Inh ((τ i).tsubst σ)) : Inh (R.tsubst σ) := by
  have ht := (checkAll_sound h).tsubst σ
  choose a ha using args
  refine ⟨(t.tsubst σ).subst a, ht.subst_closed fun i A hi => ?_⟩
  simp only [LCtx.tsubst, Option.map_some, Option.some.injEq] at hi
  subst hi; exact ha i

end FlowTyping
