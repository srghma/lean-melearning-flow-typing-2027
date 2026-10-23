module
public import RequestProject.FlowTyping.LambdaFFrame
public import RequestProject.FlowTyping.Metatheory

/-!
# Examples from the paper

* Section 3: lenses implemented in `λL`.
* Examples 5.2, 5.3, 5.6, 5.7, 5.10, 5.11: typing derivations in `λF`.
-/

@[expose] public section

namespace FlowTyping

lemma Lin.of_eq {n : ℕ} {Γ Γ' : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) (e : Γ = Γ') :
    Lin Γ' t A := e ▸ h

/-! ## Section 3: lenses in `λL` -/

/-- The lens `λ(x, y) : A ⊗ B. (x, λx' : A'. (x', y))` viewing the first component of a pair
(Sections 3.1 and 3.2). -/
def fstLens (A B A' : Ty) : Term 0 :=
  .lam (.tensor A B) (.letPair (.var 0) (.pair (.var 1) (.lam A' (.pair (.var 0) (.var 1)))))

/-- The first-projection lens has the heterogeneous lens type `(A ⊗ B, A' ⊗ B) → (A, A')`
(Section 3.2); in particular (`A' = A`) it is a simple lens `(A ⊗ B) → A` (Section 3.1). -/
theorem fstLens_typing (A B A' : Ty) :
    Lin (LCtx.empty 0) (fstLens A B A') (lensTy (.tensor A B) (.tensor A' B) A A') := by
  have h₄ : Lin (Fin.cons (some A') (LCtx.single 0 B : LCtx 3)) (.pair (.var 0) (.var 1))
      (.tensor A' B) :=
    Lin.pair (Γ₁ := LCtx.single 0 A') (Γ₂ := LCtx.single 1 B)
      (by intro i; fin_cases i <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩) (Lin.var 0 A') (Lin.var 1 B)
  have h₃ : Lin (Fin.cons (some B) (Fin.cons (some A) (LCtx.empty 1)))
      (.pair (.var 1) (.lam A' (.pair (.var 0) (.var 1)))) (.tensor A (.lolli A' (.tensor A' B))) :=
    Lin.pair (Γ₁ := LCtx.single 1 A) (Γ₂ := LCtx.single 0 B)
      (by intro i; fin_cases i <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩) (Lin.var 1 A) (Lin.lam h₄)
  have h₂ : Lin (Fin.cons (some (.tensor A B)) (LCtx.empty 0))
      (.letPair (.var 0) (.pair (.var 1) (.lam A' (.pair (.var 0) (.var 1)))))
      (.tensor A (.lolli A' (.tensor A' B))) :=
    Lin.letPair (Γ₁ := LCtx.single 0 (.tensor A B)) (Γ₂ := LCtx.empty 1)
      (by intro i; fin_cases i; first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩) (Lin.var 0 _) h₃
  exact Lin.lam h₂

/-- The identity lens `λs : S. (s, λx : S. x) : (S, S) → (S, S)`. -/
def idLens (S : Ty) : Term 0 := .lam S (.pair (.var 0) (.lam S (.var 0)))

theorem idLens_typing (S : Ty) : Lin (LCtx.empty 0) (idLens S) (lensTy S S S S) := by
  have h₂ : Lin (LCtx.empty 1) (.lam S (.var 0)) (.lolli S S) :=
    Lin.lam ((Lin.var 0 S).of_eq (by funext i; fin_cases i <;> rfl))
  have h₁ : Lin (Fin.cons (some S) (LCtx.empty 0)) (.pair (.var 0) (.lam S (.var 0)))
      (.tensor S (.lolli S S)) :=
    Lin.pair (Γ₁ := LCtx.single 0 S) (Γ₂ := LCtx.empty 1)
      (by intro i; fin_cases i; first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩) (Lin.var 0 S) h₂
  exact Lin.lam h₁

namespace LambdaF

lemma LinTy.of_eq {n : ℕ} {Γ Γ' Δ Δ' : FCtx n} {t : LinTm n} {A : PTy} (h : LinTy Γ t A Δ)
    (e₁ : Γ = Γ') (e₂ : Δ = Δ') : LinTy Γ' t A Δ' := e₁ ▸ e₂ ▸ h

lemma LensTy.of_eq {n : ℕ} {Γ Γ' Δ Δ' : FCtx n} {u : LensTm n} {A B : PTy}
    (h : LensTy Γ u A B Δ) (e₁ : Γ = Γ') (e₂ : Δ = Δ') : LensTy Γ' u A B Δ' := e₁ ▸ e₂ ▸ h

/-! ## Example 5.2: assignment to a variable -/

/-- Derived rule: `Γ₁ ⊢ t : A ⊣ Γ₂, x : B` implies `Γ₁ ⊢ (x ≔ t) : B ⊣ Γ₂, x : A`. -/
theorem assign_var_live {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t : LinTm n} {A B : PTy} {i : Fin n}
    (ht : LinTy Γ₁ t A Γ₂) (hi : Γ₂ i = .live B) :
    LinTy Γ₁ (.assign (.var i) t) B (Function.update Γ₂ i (.live A)) :=
  .assign ht (.varLive hi)

/-- Derived rule: `Γ₁ ⊢ t : A ⊣ Γ₂, x†` implies `Γ₁ ⊢ (x ≔ t) : 1 ⊣ Γ₂, x : A`. -/
theorem assign_var_dead {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t : LinTm n} {A : PTy} {i : Fin n}
    (ht : LinTy Γ₁ t A Γ₂) (hi : Γ₂ i = .dead) :
    LinTy Γ₁ (.assign (.var i) t) .one (Function.update Γ₂ i (.live A)) :=
  .assign ht (.varDead hi)

/-- `x : A, y : B ⊢ (y ≔ x) : B ⊣ x†, y : A` (here `x = var 0`, `y = var 1`). -/
theorem example_5_2_a (A B : PTy) :
    LinTy ![.live A, .live B] (.assign (.var 1) (.var 0)) B ![.dead, .live A] := by
  refine (assign_var_live (.var (i := 0) (A := A) rfl) ?_).of_eq rfl ?_
  · rfl
  · funext i; fin_cases i <;> rfl

/-- `x : A, y : B ⊢ (x ≔ (y ≔ x)) : 1 ⊣ x : B, y : A`: this term swaps `x` and `y`. -/
theorem example_5_2_b (A B : PTy) :
    LinTy ![.live A, .live B] (.assign (.var 0) (.assign (.var 1) (.var 0))) .one
      ![.live B, .live A] := by
  refine (assign_var_dead (example_5_2_a A B) rfl).of_eq rfl ?_
  funext i; fin_cases i <;> rfl

/-! ## Example 5.3: tuples of lenses -/

/-- `x : A, y : B ⊢ ((x, y) ≔ (y, x)) : 1 ⊗ 1 ⊣ x : B, y : A`. -/
theorem example_5_3 (A B : PTy) :
    LinTy ![.live A, .live B] (.assign (.pair (.var 0) (.var 1)) (.pair (.var 1) (.var 0)))
      (.tensor .one .one) ![.live B, .live A] := by
  have h₁ : LinTy ![.live A, .live B] (.pair (.var 1) (.var 0)) (.tensor B A) ![.dead, .dead] :=
    (LinTy.pair (.var (i := 1) (A := B) rfl) (.var (i := 0) (A := A) rfl)).of_eq rfl
      (by funext i; fin_cases i <;> rfl)
  have h₂ : LensTy ![.dead, .dead] (.pair (.var 0) (.var 1)) (.tensor .one .one)
      (.tensor B A) ![.live B, .live A] := by
    refine LensTy.pair (Γ₁ := ![.dead, .absent]) (Γ₃ := ![.absent, .dead])
      (Γ₂ := ![.live B, .absent]) (Γ₄ := ![.absent, .live A]) ?_
      ((LensTy.varDead (i := 0) (A' := B) rfl).of_eq rfl ?_)
      ((LensTy.varDead (i := 1) (A' := A) rfl).of_eq rfl ?_) ?_
    all_goals first
      | (intro i; fin_cases i <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩)
      | (funext i; fin_cases i <;> rfl)
  exact .assign h₁ h₂

/-! ## Example 5.6: identity flow functions -/

/-- The identity flow function `λx : A. x : A ⊸ A`. -/
theorem example_5_6_plain (A : PTy) :
    LinTy (fun _ => .absent : FCtx 0) (.lam (.plain A) (.lin (.var 0)))
      (.lolli (.plain A) (.plain A)) (fun _ => .absent) := by
  refine .lam (Γ₁ := fun _ => .absent) (Γ₂ := fun _ => .absent) (fun i => i.elim0)
    (.lin ((LinTy.var (i := 0) (A := A) rfl).of_eq rfl ?_)) (fun i => i.elim0)
  funext i; fin_cases i; rfl

/-- The identity flow function `λx : A/A'. ~x : A/A' ⊸ A/A'`. -/
theorem example_5_6_slash (A A' : PTy) :
    LinTy (fun _ => .absent : FCtx 0) (.lam (.slash A A') (.lens (.var 0)))
      (.lolli (.slash A A') (.slash A A')) (fun _ => .absent) := by
  refine .lamSlash (Γ₁ := fun _ => .absent) (Γ₂ := fun _ => .absent) (fun i => i.elim0)
    (.lens ((LensTy.varLive (i := 0) (A := A) (A' := A') rfl).of_eq rfl ?_)) (fun i => i.elim0)
  funext i; fin_cases i; rfl

/-! ## Example 5.7: `use` and `take` -/

/-- `use ≔ λa : A. lens x ← a in x : A ⊸ A/1`. -/
def use (A : PTy) : LinTm 0 := .lam (.plain A) (.lens (.lens (.var 0) (.var 0)))

theorem use_typing (A : PTy) :
    LinTy (fun _ => .absent) (use A) (.lolli (.plain A) (.slash A .one)) (fun _ => .absent) := by
  refine .lam (Γ₁ := fun _ => .absent) (Γ₂ := fun _ => .absent) (fun i => i.elim0)
    (.lens (.lens (Γ₂ := ![.dead]) ((LinTy.var (i := 0) (A := A) rfl).of_eq rfl ?_)
      ((LinTy.var (i := 0) (A := .one) rfl).of_eq rfl ?_))) (fun i => i.elim0)
  all_goals (funext i; fin_cases i <;> rfl)

/-- `take ≔ λa : A/1. (a ≔ ∗) : A/1 ⊸ A`. -/
def take (A : PTy) : LinTm 0 := .lam (.slash A .one) (.lin (.assign (.var 0) .unit))

theorem take_typing (A : PTy) :
    LinTy (fun _ => .absent) (take A) (.lolli (.slash A .one) (.plain A)) (fun _ => .absent) := by
  refine .lamSlash (Γ₁ := fun _ => .absent) (Γ₂ := fun _ => .absent) (fun i => i.elim0)
    (.lin (.assign .unit ((LensTy.varLive (i := 0) (A := A) (A' := .one) rfl).of_eq rfl ?_)))
    (fun i => i.elim0)
  funext i; fin_cases i; rfl

/-! ## Example 5.10: the first projection lens, internally -/

/-- `fst ≔ λz : (A ⊗ B)/(A' ⊗ B). let (x, y) = ~z in ~x : (A ⊗ B)/(A' ⊗ B) ⊸ A/A'`. -/
def fstF (A B A' : PTy) : LinTm 0 :=
  .lam (.slash (.tensor A B) (.tensor A' B)) (.lens (.letPair (.lens (.var 0)) (.var 1)))

theorem fstF_typing (A B A' : PTy) :
    LinTy (fun _ => .absent) (fstF A B A')
      (.lolli (.slash (.tensor A B) (.tensor A' B)) (.slash A A')) (fun _ => .absent) := by
  refine .lamSlash (Γ₁ := fun _ => .absent) (Γ₂ := fun _ => .absent) (fun i => i.elim0)
    (.lens (.letPairLens (Γ₁ := ![.live (.tensor A B)]) (Γ₃ := ![.absent])
      (Γ₂ := ![.live (.tensor A' B)]) (Γ₄ := ![.absent]) ?_
      ((LensTy.varLive (i := 0) (A' := .tensor A' B) rfl).of_eq rfl ?_)
      ((LensTy.varLive (i := 1) (A' := A') rfl).of_eq rfl ?_) ?_)) (fun i => i.elim0)
  all_goals first
    | (intro i; fin_cases i; first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩)
    | (funext i; fin_cases i <;> rfl)

/-! ## Example 5.11: inspecting a sum without consuming it -/

/-- `isInl ≔ λz : (A ⊕ B)/(A ⊕ B). case ~z of inl(x) → inl(∗) | inr(y) → inr(∗)`. -/
def isInl (A B : PTy) : LinTm 0 :=
  .lam (.slash (.plus A B) (.plus A B))
    (.lin (.case (.lens (.var 0)) (.inl .one .one .unit) (.inr .one .one .unit)))

theorem isInl_typing (A B : PTy) :
    LinTy (fun _ => .absent) (isInl A B)
      (.lolli (.slash (.plus A B) (.plus A B)) (.plain (.plus .one .one))) (fun _ => .absent) := by
  refine .lamSlash (Γ₁ := fun _ => .absent) (Γ₂ := fun _ => .absent) (fun i => i.elim0)
    (.lin (.caseLens (Γ₁ := ![.live (.plus A B)]) (Γ₃ := ![.absent])
      (Γ₂ := ![.live (.plus A B)]) (Γ₄ := ![.absent]) ?_
      ((LensTy.varLive (i := 0) (A' := .plus A B) rfl).of_eq rfl ?_)
      ((LinTy.inl .unit).of_eq rfl ?_) ((LinTy.inr .unit).of_eq rfl ?_) ?_)) (fun i => i.elim0)
  all_goals first
    | (intro i; fin_cases i; first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩)
    | (funext i; fin_cases i <;> rfl)

end LambdaF

end FlowTyping
