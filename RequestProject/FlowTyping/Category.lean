module
public import RequestProject.FlowTyping.Congruence
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of `λL` types and terms (Proposition D.10)

The objects are `λL` types; a morphism `A → B` is an equivalence class of closed terms
`⊢ t : A ⊸ B` under `⊨ - ≈ - : A ⊸ B` (here `LR.T (A ⊸ B)`). The identity is the class of
`λx : A. x` and the composite of `[t₂] : A → B` and `[t₁] : B → C` is the class of
`λx : A. t₁ (t₂ x)`.

* `LR.T.app`: closed compatibility of application (an instance of Theorem D.8).
* `LR.T.of_eval_imp`: replacing a term by one that evaluates to everything the first one does.
* `LR.LCat` with `instCategoryLCat`: **Proposition D.10**, `C` is a category.
-/

@[expose] public section

namespace FlowTyping

namespace LR

/-- If `t'` is well typed and evaluates to every value `t` evaluates to, then `t'` can
replace `t` on the left of `T⟦A⟧`. -/
theorem T.of_eval_imp {A : Ty} {t t' s : Term 0} (hW : W A t')
    (himp : ∀ v, Eval t v → Eval t' v) (h : T A t s) : T A t' s := by
  obtain ⟨-, hs, v₁, v₂, e₁, e₂, hv⟩ := h
  exact ⟨hW, hs, v₁, v₂, himp v₁ e₁, e₂, hv⟩

/-- The same, on the right of `T⟦A⟧`. -/
theorem T.of_eval_imp_right {A : Ty} {t s s' : Term 0} (hW : W A s')
    (himp : ∀ v, Eval s v → Eval s' v) (h : T A t s) : T A t s' :=
  (T.of_eval_imp hW himp h.symm).symm

/-- Closed compatibility of application. -/
theorem T.app {A B : Ty} {t₁ t₂ a₁ a₂ : Term 0} (h₁ : T (.lolli A B) t₁ t₂) (h₂ : T A a₁ a₂) :
    T B (.app t₁ a₁) (.app t₂ a₂) := by
  obtain ⟨w₁, w₂, v₁, v₂, e₁, e₂, -, -, s₁, s₂, rfl, rfl, hs'⟩ := h₁
  obtain ⟨x₁, x₂, b₁, b₂, f₁, f₂, hb⟩ := h₂
  obtain ⟨-, -, c₁, c₂, g₁, g₂, hc⟩ := hs' b₁ b₂ hb
  exact ⟨.app split_empty w₁ x₁, .app split_empty w₂ x₂, c₁, c₂, .app e₁ f₁ g₁,
    .app e₂ f₂ g₂, hc⟩

/-- The identity term `λx : A. x`. -/
def idTm (A : Ty) : Term 0 := .lam A (.var 0)

/-- The composite `λx : A. g (f x)` of `f : A ⊸ B` and `g : B ⊸ C`. -/
def compTm (A : Ty) (f g : Term 0) : Term 0 :=
  .lam A (.app g.weaken (.app f.weaken (.var 0)))

lemma single_zero_eq (A : Ty) : (LCtx.single 0 A : LCtx 1) = Fin.cons (some A) (LCtx.empty 0) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact i.elim0

lemma W_id (A : Ty) : W (.lolli A A) (idTm A) := by
  refine Lin.lam ?_
  rw [← single_zero_eq]
  exact Lin.var 0 A

lemma W_comp {A B C : Ty} {f g : Term 0} (hf : W (.lolli A B) f) (hg : W (.lolli B C) g) :
    W (.lolli A C) (compTm A f g) := by
  refine Lin.lam (Lin.app (Γ₁ := LCtx.empty 1) (Γ₂ := Fin.cons (some A) (LCtx.empty 0)) ?_
    hg.weaken (Lin.app (Γ₁ := LCtx.empty 1) (Γ₂ := Fin.cons (some A) (LCtx.empty 0)) ?_
      hf.weaken ?_))
  · intro i; exact Or.inl ⟨rfl, rfl⟩
  · intro i; exact Or.inl ⟨rfl, rfl⟩
  · rw [← single_zero_eq]; exact Lin.var 0 A

lemma idTm_body (w : Term 0) : (Term.var 0 : Term 1).subst (fun _ => w) = w := rfl

lemma compTm_body (f g w : Term 0) :
    (Term.app g.weaken (.app f.weaken (.var 0)) : Term 1).subst (fun _ => w) =
      .app g (.app f w) := by
  simp only [Term.subst, Term.subst_weaken]

lemma W_app {A B : Ty} {f a : Term 0} (hf : W (.lolli A B) f) (ha : W A a) : W B (.app f a) :=
  .app split_empty hf ha

/-- Composition respects `≈`. -/
theorem comp_congr {A B C : Ty} {f f' g g' : Term 0} (hf : T (.lolli A B) f f')
    (hg : T (.lolli B C) g g') : T (.lolli A C) (compTm A f g) (compTm A f' g') := by
  have h₁ := W_comp hf.wellTyped.1 hg.wellTyped.1
  have h₂ := W_comp hf.wellTyped.2 hg.wellTyped.2
  refine ⟨h₁, h₂, _, _, .lam _ _, .lam _ _, h₁, h₂, _, _, rfl, rfl, fun w₁ w₂ hw => ?_⟩
  rw [compTm_body, compTm_body]
  exact T.app hg (T.app hf (V.toT hw))

/-- Left identity: `λx. f (id x) ≈ f`. -/
theorem id_comp_rel {A B : Ty} {f : Term 0} (hf : W (.lolli A B) f) :
    T (.lolli A B) (compTm A (idTm A) f) f := by
  have hc := W_comp (W_id A) hf
  obtain ⟨-, -, v, v', e, e', hv⟩ := T.refl hf
  have hv' := hv
  obtain ⟨-, hv'W, s, s', rfl, rfl, hs⟩ := hv'
  refine ⟨hc, hf, _, _, .lam _ _, e', hc, hv'W, _, _, rfl, rfl, fun w₁ w₂ hw => ?_⟩
  rw [compTm_body]
  have hw₁ := (V.wellTyped A hw).1
  refine T.of_eval_imp (W_app hf (W_app (W_id A) hw₁)) (fun r hr => ?_) (hs w₁ w₂ hw)
  have hval := (V.isValue A hw).1
  exact .app e (.app (.lam _ _) hval.eval_self hval.eval_self) hr

/-- Right identity: `λx. id (f x) ≈ f`. -/
theorem comp_id_rel {A B : Ty} {f : Term 0} (hf : W (.lolli A B) f) :
    T (.lolli A B) (compTm A f (idTm B)) f := by
  have hc := W_comp hf (W_id B)
  obtain ⟨-, -, v, v', e, e', hv⟩ := T.refl hf
  have hv' := hv
  obtain ⟨-, hv'W, s, s', rfl, rfl, hs⟩ := hv'
  refine ⟨hc, hf, _, _, .lam _ _, e', hc, hv'W, _, _, rfl, rfl, fun w₁ w₂ hw => ?_⟩
  rw [compTm_body]
  have hw₁ := (V.wellTyped A hw).1
  refine T.of_eval_imp (W_app (W_id B) (W_app hf hw₁)) (fun r hr => ?_) (hs w₁ w₂ hw)
  have hval := (V.isValue A hw).1
  exact .app (.lam _ _) (.app e hval.eval_self hr) (Eval.isValue hr).eval_self

/-- Associativity: `λx. h ((λy. g (f y)) x) ≈ λx. (λy. h (g y)) (f x)`. -/
theorem assoc_rel {A B C D : Ty} {f g h : Term 0} (hf : W (.lolli A B) f)
    (hg : W (.lolli B C) g) (hh : W (.lolli C D) h) :
    T (.lolli A D) (compTm A (compTm A f g) h) (compTm A f (compTm B g h)) := by
  have hfg := W_comp hf hg
  have hgh := W_comp hg hh
  have h₁ := W_comp hfg hh
  have h₂ := W_comp hf hgh
  refine ⟨h₁, h₂, _, _, .lam _ _, .lam _ _, h₁, h₂, _, _, rfl, rfl, fun w₁ w₂ hw => ?_⟩
  rw [compTm_body, compTm_body]
  have hw₁ := (V.wellTyped A hw).1
  have hw₂ := (V.wellTyped A hw).2
  have base : T D (.app h (.app g (.app f w₁))) (.app h (.app g (.app f w₂))) :=
    T.app (T.refl hh) (T.app (T.refl hg) (T.app (T.refl hf) (V.toT hw)))
  refine T.of_eval_imp_right (W_app hgh (W_app hf hw₂)) (fun r hr => ?_)
    (T.of_eval_imp (W_app hh (W_app hfg hw₁)) (fun r hr => ?_) base)
  · cases hr with
    | app eh emid ebody =>
      cases emid with
      | app eg ef egbody =>
        refine .app (.lam _ _) ef ?_
        rw [compTm_body]
        exact .app eh (.app eg (Eval.isValue ef).eval_self egbody) ebody
  · cases hr with
    | app eh emid ebody =>
      refine .app eh (.app (.lam _ _) (V.isValue A hw).1.eval_self ?_) ebody
      rw [compTm_body]
      exact emid

/-- The setoid `⊨ - ≈ - : A ⊸ B` on closed terms of type `A ⊸ B`. -/
def homSetoid (A B : Ty) : Setoid {t : Term 0 // W (.lolli A B) t} where
  r t u := T (.lolli A B) t.1 u.1
  iseqv := ⟨fun t => T.refl t.2, T.symm, T.trans⟩

/-- The objects of the category `C`: the types of `λL`. -/
def LCat : Type := Ty

/-- **Proposition D.10.** `C` is a category: morphisms `A → B` are closed terms of type
`A ⊸ B` up to `⊨ - ≈ - : A ⊸ B`. -/
instance instCategoryLCat : CategoryTheory.Category LCat where
  Hom A B := Quotient (homSetoid A B)
  id A := Quotient.mk _ ⟨idTm A, W_id A⟩
  comp {A _ _} f g := Quotient.map₂ (fun f g => ⟨compTm A f.1 g.1, W_comp f.2 g.2⟩)
    (fun _ _ hf _ _ hg => comp_congr hf hg) f g
  id_comp f := by
    induction f using Quotient.inductionOn with
    | h f => exact Quotient.sound (id_comp_rel f.2)
  comp_id f := by
    induction f using Quotient.inductionOn with
    | h f => exact Quotient.sound (comp_id_rel f.2)
  assoc f g h := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    induction h using Quotient.inductionOn with | h h =>
    exact Quotient.sound (assoc_rel f.2 g.2 h.2)

end LR

end FlowTyping
