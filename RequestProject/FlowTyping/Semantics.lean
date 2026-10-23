module
public import RequestProject.FlowTyping.Substitution

/-!
# Big-step semantics of `λL` (Appendix D.1)

* `Term.bang t` is `!t`, the abbreviation of `promote for in t` (a promotion with no
  promoted terms).
* `IsValue v`: the values
  `v ::= λx : A. t | (v₁, v₂) | ∗ | inl(v) | inr(v) | t₁ & t₂ | true(v) | promote for in t`.
* `Eval t v`: the big-step judgement `t ⇓ v` for closed terms `t : Term 0`.
* `Eval.deterministic`: Proposition D.1.
* `IsValue.eval_self`, `Eval.isValue`: Proposition D.2 (values are closed terms — automatic
  since they live in `Term 0` — and they evaluate to themselves; moreover only values are
  results of evaluation).

The appendix lists the rules for `inl` and `case … inl …` and leaves the symmetric rules
for `inr` implicit; we include them.  Substitution `t[v/x]` is `Term.subst`.
-/

@[expose] public section

namespace FlowTyping

/-- `!t`, abbreviating the value `promote for in t`. -/
def Term.bang (t : Term 0) : Term 0 := .promote 0 Fin.elim0 t

lemma Term.promote_zero_eq_bang (ts : Fin 0 → Term 0) (t : Term 0) :
    Term.promote 0 ts t = t.bang := by
  have : ts = Fin.elim0 := funext fun i => i.elim0
  rw [this]; rfl

lemma Term.bang_inj {a b : Term 0} (h : a.bang = b.bang) : a = b := by
  simp only [Term.bang, Term.promote.injEq, true_and, heq_eq_eq] at h
  exact h

/-- Values of `λL` (Appendix D.1). -/
inductive IsValue : Term 0 → Prop
  | lam (A : Ty) (t : Term 1) : IsValue (.lam A t)
  | pair {v₁ v₂ : Term 0} : IsValue v₁ → IsValue v₂ → IsValue (.pair v₁ v₂)
  | unit : IsValue .unit
  | inl (A B : Ty) {v : Term 0} : IsValue v → IsValue (.inl A B v)
  | inr (A B : Ty) {v : Term 0} : IsValue v → IsValue (.inr A B v)
  | withPair (t₁ t₂ : Term 0) : IsValue (.withPair t₁ t₂)
  | trueI {v : Term 0} : IsValue v → IsValue (.trueI v)
  | bang (t : Term 0) : IsValue t.bang

/-- The big-step semantics `t ⇓ v` of closed `λL` terms (Appendix D.1). -/
inductive Eval : Term 0 → Term 0 → Prop
  | letIn {t₁ : Term 0} {t₂ : Term 1} {v₁ v₂ : Term 0} :
      Eval t₁ v₁ → Eval (t₂.subst fun _ => v₁) v₂ → Eval (.letIn t₁ t₂) v₂
  | lam (A : Ty) (t : Term 1) : Eval (.lam A t) (.lam A t)
  | app {t₁ t₂ : Term 0} {A : Ty} {t : Term 1} {v₁ v₂ : Term 0} :
      Eval t₁ (.lam A t) → Eval t₂ v₁ → Eval (t.subst fun _ => v₁) v₂ → Eval (.app t₁ t₂) v₂
  | pair {t₁ t₂ v₁ v₂ : Term 0} : Eval t₁ v₁ → Eval t₂ v₂ → Eval (.pair t₁ t₂) (.pair v₁ v₂)
  | letPair {t₁ : Term 0} {t₂ : Term 2} {v₁ v₂ v : Term 0} :
      Eval t₁ (.pair v₁ v₂) → Eval (t₂.subst ![v₂, v₁]) v → Eval (.letPair t₁ t₂) v
  | unit : Eval .unit .unit
  | letUnit {t₁ t₂ v : Term 0} : Eval t₁ .unit → Eval t₂ v → Eval (.letUnit t₁ t₂) v
  | inl (A B : Ty) {t v : Term 0} : Eval t v → Eval (.inl A B t) (.inl A B v)
  | inr (A B : Ty) {t v : Term 0} : Eval t v → Eval (.inr A B t) (.inr A B v)
  | caseInl {t : Term 0} {t₁ t₂ : Term 1} {A B : Ty} {v₁ v₂ : Term 0} :
      Eval t (.inl A B v₁) → Eval (t₁.subst fun _ => v₁) v₂ → Eval (.case t t₁ t₂) v₂
  | caseInr {t : Term 0} {t₁ t₂ : Term 1} {A B : Ty} {v₁ v₂ : Term 0} :
      Eval t (.inr A B v₁) → Eval (t₂.subst fun _ => v₁) v₂ → Eval (.case t t₁ t₂) v₂
  | withPair (t₁ t₂ : Term 0) : Eval (.withPair t₁ t₂) (.withPair t₁ t₂)
  | fst {t t₁ t₂ v : Term 0} : Eval t (.withPair t₁ t₂) → Eval t₁ v → Eval (.fst t) v
  | snd {t t₁ t₂ v : Term 0} : Eval t (.withPair t₁ t₂) → Eval t₂ v → Eval (.snd t) v
  | trueI {t v : Term 0} : Eval t v → Eval (.trueI t) (.trueI v)
  | promote {k : ℕ} {ts : Fin k → Term 0} {t : Term k} (ts' : Fin k → Term 0) :
      (∀ j, Eval (ts j) (ts' j).bang) →
      Eval (.promote k ts t) (t.subst fun j => (ts' j).bang).bang
  | discard {t t' : Term 0} : Eval t t'.bang → Eval (.discard t) .unit
  | copy {t t' : Term 0} : Eval t t'.bang → Eval (.copy t) (.pair t'.bang t'.bang)
  | derelict {t t' v : Term 0} : Eval t t'.bang → Eval t' v → Eval (.derelict t) v

/-- **Proposition D.1 (determinism).** If `t ⇓ v₁` and `t ⇓ v₂` then `v₁ = v₂`. -/
theorem Eval.deterministic {t v₁ : Term 0} (h₁ : Eval t v₁) :
    ∀ {v₂ : Term 0}, Eval t v₂ → v₁ = v₂ := by
  induction h₁ with
  | letIn _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | letIn h₁ h₂ => cases ih₁ h₁; exact ih₂ h₂
  | lam => intro v h; cases h; rfl
  | app _ _ _ ih₁ ih₂ ih₃ =>
    intro v h; cases h with
    | app h₁ h₂ h₃ =>
      cases ih₁ h₁; cases ih₂ h₂; exact ih₃ h₃
  | pair _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | pair h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]
  | letPair _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | letPair h₁ h₂ => cases ih₁ h₁; exact ih₂ h₂
  | unit => intro v h; cases h; rfl
  | letUnit _ _ _ ih₂ =>
    intro v h; cases h with
    | letUnit _ h₂ => exact ih₂ h₂
  | inl _ _ _ ih => intro v h; cases h with | inl _ _ h => rw [ih h]
  | inr _ _ _ ih => intro v h; cases h with | inr _ _ h => rw [ih h]
  | caseInl _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | caseInl h₁ h₂ => cases ih₁ h₁; exact ih₂ h₂
    | caseInr h₁ _ => cases ih₁ h₁
  | caseInr _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | caseInl h₁ _ => cases ih₁ h₁
    | caseInr h₁ h₂ => cases ih₁ h₁; exact ih₂ h₂
  | withPair => intro v h; cases h; rfl
  | fst _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | fst h₁ h₂ => cases ih₁ h₁; exact ih₂ h₂
  | snd _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | snd h₁ h₂ => cases ih₁ h₁; exact ih₂ h₂
  | trueI _ ih => intro v h; cases h with | trueI h => rw [ih h]
  | promote ts' _ ih =>
    intro v h; cases h with
    | promote ts'' h' =>
      have : ts' = ts'' := funext fun j => Term.bang_inj (ih j (h' j))
      rw [this]
  | discard => intro v h; cases h; rfl
  | copy _ ih =>
    intro v h; cases h with
    | copy h => rw [Term.bang_inj (ih h)]
  | derelict _ _ ih₁ ih₂ =>
    intro v h; cases h with
    | derelict h₁ h₂ => cases Term.bang_inj (ih₁ h₁); exact ih₂ h₂

/-- `!t ⇓ !t`. -/
lemma Eval.bang (t : Term 0) : Eval t.bang t.bang := by
  have := Eval.promote (ts := Fin.elim0) (t := t) Fin.elim0 (fun j => j.elim0)
  rwa [Term.subst_closed] at this

/-- **Proposition D.2.** Values evaluate to themselves. -/
theorem IsValue.eval_self {v : Term 0} (h : IsValue v) : Eval v v := by
  induction h with
  | lam A t => exact .lam A t
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | unit => exact .unit
  | inl A B _ ih => exact .inl A B ih
  | inr A B _ ih => exact .inr A B ih
  | withPair t₁ t₂ => exact .withPair t₁ t₂
  | trueI _ ih => exact .trueI ih
  | bang t => exact .bang t

/-- The result of an evaluation is a value. -/
theorem Eval.isValue {t v : Term 0} (h : Eval t v) : IsValue v := by
  induction h with
  | lam A t => exact .lam A t
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | unit => exact .unit
  | inl A B _ ih => exact .inl A B ih
  | inr A B _ ih => exact .inr A B ih
  | withPair t₁ t₂ => exact .withPair t₁ t₂
  | trueI _ ih => exact .trueI ih
  | promote => exact .bang _
  | discard => exact .unit
  | copy => exact .pair (.bang _) (.bang _)
  | _ => assumption

end FlowTyping
