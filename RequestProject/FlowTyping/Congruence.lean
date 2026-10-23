module
public import RequestProject.FlowTyping.Fundamental

/-!
# `Γ ⊨ - ≈ - : A` is a congruence (Theorem D.8)

`LR.Cong Γ t₁ t₂ A` is the closure of `Γ ⊨ t₁ ≈ t₂ : A` (on well-typed terms) under all the
typing rules of `λL`: each constructor mirrors a rule of `Lin`, with two terms instead of
one. The theorem `LR.Cong.sem` says that this closure adds nothing, i.e. the logical relation
is preserved by every term constructor. Together with `LR.sem_refl`, `LR.Sem.symm` and
`LR.Sem.trans` this is Theorem D.8.
-/

@[expose] public section

namespace FlowTyping

namespace LR

/-- The congruence closure of `Γ ⊨ - ≈ - : A` under the typing rules of `λL`. -/
inductive Cong : {n : ℕ} → LCtx n → Term n → Term n → Ty → Prop
  | rel {n : ℕ} {Γ : LCtx n} {t₁ t₂ : Term n} {A : Ty} :
      Lin Γ t₁ A → Lin Γ t₂ A → Sem Γ t₁ t₂ A → Cong Γ t₁ t₂ A
  | letIn {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' A B} :
      Γ.Split Γ₁ Γ₂ → Cong Γ₁ t₁ t₁' A → Cong (Fin.cons (some A) Γ₂) t₂ t₂' B →
      Cong Γ (.letIn t₁ t₂) (.letIn t₁' t₂') B
  | lam {n : ℕ} {Γ : LCtx n} {t t' A B} :
      Cong (Fin.cons (some A) Γ) t t' B → Cong Γ (.lam A t) (.lam A t') (.lolli A B)
  | app {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' A B} :
      Γ.Split Γ₁ Γ₂ → Cong Γ₁ t₁ t₁' (.lolli A B) → Cong Γ₂ t₂ t₂' A →
      Cong Γ (.app t₁ t₂) (.app t₁' t₂') B
  | pair {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' A B} :
      Γ.Split Γ₁ Γ₂ → Cong Γ₁ t₁ t₁' A → Cong Γ₂ t₂ t₂' B →
      Cong Γ (.pair t₁ t₂) (.pair t₁' t₂') (.tensor A B)
  | letPair {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' A B C} :
      Γ.Split Γ₁ Γ₂ → Cong Γ₁ t₁ t₁' (.tensor A B) →
      Cong (Fin.cons (some B) (Fin.cons (some A) Γ₂)) t₂ t₂' C →
      Cong Γ (.letPair t₁ t₂) (.letPair t₁' t₂') C
  | letUnit {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' A} :
      Γ.Split Γ₁ Γ₂ → Cong Γ₁ t₁ t₁' .one → Cong Γ₂ t₂ t₂' A →
      Cong Γ (.letUnit t₁ t₂) (.letUnit t₁' t₂') A
  | inl {n : ℕ} {Γ : LCtx n} {t t' A B} :
      Cong Γ t t' A → Cong Γ (.inl A B t) (.inl A B t') (.plus A B)
  | inr {n : ℕ} {Γ : LCtx n} {t t' A B} :
      Cong Γ t t' B → Cong Γ (.inr A B t) (.inr A B t') (.plus A B)
  | case {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' t₃ t₃' A B C} :
      Γ.Split Γ₁ Γ₂ → Cong Γ₁ t₁ t₁' (.plus A B) → Cong (Fin.cons (some A) Γ₂) t₂ t₂' C →
      Cong (Fin.cons (some B) Γ₂) t₃ t₃' C → Cong Γ (.case t₁ t₂ t₃) (.case t₁' t₂' t₃') C
  | falseE {n : ℕ} {Γ : LCtx n} {t t' B} :
      Cong Γ t t' .zero → Cong Γ (.falseE B t) (.falseE B t') B
  | withPair {n : ℕ} {Γ : LCtx n} {t₁ t₁' t₂ t₂' A B} :
      Cong Γ t₁ t₁' A → Cong Γ t₂ t₂' B →
      Cong Γ (.withPair t₁ t₂) (.withPair t₁' t₂') (.with A B)
  | fst {n : ℕ} {Γ : LCtx n} {t t' A B} : Cong Γ t t' (.with A B) → Cong Γ (.fst t) (.fst t') A
  | snd {n : ℕ} {Γ : LCtx n} {t t' A B} : Cong Γ t t' (.with A B) → Cong Γ (.snd t) (.snd t') B
  | trueI {n : ℕ} {Γ : LCtx n} {t t' A} : Cong Γ t t' A → Cong Γ (.trueI t) (.trueI t') .top
  | promote {n k : ℕ} {Γ : LCtx n} {Γs : Fin k → LCtx n} {ts ts' : Fin k → Term n}
      {t t' : Term k} {As : Fin k → Ty} {B : Ty} :
      Γ.SplitN Γs → (∀ j, Cong (Γs j) (ts j) (ts' j) (.bang (As j))) →
      Cong (fun j => some (.bang (As j))) t t' B →
      Cong Γ (.promote k ts t) (.promote k ts' t') (.bang B)
  | discard {n : ℕ} {Γ : LCtx n} {t t' A} :
      Cong Γ t t' (.bang A) → Cong Γ (.discard t) (.discard t') .one
  | copy {n : ℕ} {Γ : LCtx n} {t t' A} :
      Cong Γ t t' (.bang A) → Cong Γ (.copy t) (.copy t') (.tensor (.bang A) (.bang A))
  | derelict {n : ℕ} {Γ : LCtx n} {t t' A} :
      Cong Γ t t' (.bang A) → Cong Γ (.derelict t) (.derelict t') A

/-- Both sides of a congruence are well typed. -/
theorem Cong.wellTyped {n : ℕ} {Γ : LCtx n} {t₁ t₂ : Term n} {A : Ty} (h : Cong Γ t₁ t₂ A) :
    Lin Γ t₁ A ∧ Lin Γ t₂ A := by
  induction h with
  | rel h₁ h₂ _ => exact ⟨h₁, h₂⟩
  | letIn hs _ _ ih₁ ih₂ => exact ⟨.letIn hs ih₁.1 ih₂.1, .letIn hs ih₁.2 ih₂.2⟩
  | lam _ ih => exact ⟨.lam ih.1, .lam ih.2⟩
  | app hs _ _ ih₁ ih₂ => exact ⟨.app hs ih₁.1 ih₂.1, .app hs ih₁.2 ih₂.2⟩
  | pair hs _ _ ih₁ ih₂ => exact ⟨.pair hs ih₁.1 ih₂.1, .pair hs ih₁.2 ih₂.2⟩
  | letPair hs _ _ ih₁ ih₂ => exact ⟨.letPair hs ih₁.1 ih₂.1, .letPair hs ih₁.2 ih₂.2⟩
  | letUnit hs _ _ ih₁ ih₂ => exact ⟨.letUnit hs ih₁.1 ih₂.1, .letUnit hs ih₁.2 ih₂.2⟩
  | inl _ ih => exact ⟨.inl ih.1, .inl ih.2⟩
  | inr _ ih => exact ⟨.inr ih.1, .inr ih.2⟩
  | case hs _ _ _ ih₁ ih₂ ih₃ =>
    exact ⟨.case hs ih₁.1 ih₂.1 ih₃.1, .case hs ih₁.2 ih₂.2 ih₃.2⟩
  | falseE _ ih => exact ⟨.falseE ih.1, .falseE ih.2⟩
  | withPair _ _ ih₁ ih₂ => exact ⟨.withPair ih₁.1 ih₂.1, .withPair ih₁.2 ih₂.2⟩
  | fst _ ih => exact ⟨.fst ih.1, .fst ih.2⟩
  | snd _ ih => exact ⟨.snd ih.1, .snd ih.2⟩
  | trueI _ ih => exact ⟨.trueI ih.1, .trueI ih.2⟩
  | promote hs _ _ ihs ihb =>
    exact ⟨.promote hs (fun j => (ihs j).1) ihb.1, .promote hs (fun j => (ihs j).2) ihb.2⟩
  | discard _ ih => exact ⟨.discard ih.1, .discard ih.2⟩
  | copy _ ih => exact ⟨.copy ih.1, .copy ih.2⟩
  | derelict _ ih => exact ⟨.derelict ih.1, .derelict ih.2⟩

lemma wellTyped_subst₂ {n : ℕ} {Γ : LCtx n} {t₁ t₂ : Term n} {A : Ty}
    (h : Lin Γ t₁ A ∧ Lin Γ t₂ A) {γ₁ γ₂ : Fin n → Term 0} (hγ : C Γ γ₁ γ₂) :
    W A (t₁.subst γ₁) ∧ W A (t₂.subst γ₂) :=
  ⟨(wellTyped_subst h.1 hγ).1, (wellTyped_subst h.2 hγ).2⟩

/-- **Theorem D.8 (congruence).** The logical relation is closed under every typing rule. -/
theorem Cong.sem {n : ℕ} {Γ : LCtx n} {t₁ t₂ : Term n} {A : Ty} (h : Cong Γ t₁ t₂ A) :
    Sem Γ t₁ t₂ A := by
  induction h with
  | rel _ _ h => exact h
  | letIn hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.letIn hs h₁ h₂).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, hv⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ _ _ ((hγ.right hs).cons hv)
    refine ⟨hW.1, hW.2, w₁, w₂, .letIn e₁ ?_, .letIn e₂ ?_, hw⟩ <;>
      rwa [Term.subst_liftSub_cons]
  | lam h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.lam h).wellTyped hγ
    refine ⟨hW.1, hW.2, _, _, .lam _ _, .lam _ _, hW.1, hW.2, _, _, rfl, rfl,
      fun w₁ w₂ hw => ?_⟩
    rw [Term.subst_liftSub_cons, Term.subst_liftSub_cons]
    exact ih _ _ (hγ.cons hw)
  | app hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.app hs h₁ h₂).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, -, -, s₁, s₂, rfl, rfl, hs'⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, a₁, a₂, f₁, f₂, ha⟩ := ih₂ γ₁ γ₂ (hγ.right hs)
    obtain ⟨-, -, b₁, b₂, g₁, g₂, hb⟩ := hs' a₁ a₂ ha
    exact ⟨hW.1, hW.2, b₁, b₂, .app e₁ f₁ g₁, .app e₂ f₂ g₂, hb⟩
  | pair hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.pair hs h₁ h₂).wellTyped hγ
    obtain ⟨-, -, a₁, a₂, e₁, e₂, ha⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, b₁, b₂, f₁, f₂, hb⟩ := ih₂ γ₁ γ₂ (hγ.right hs)
    exact ⟨hW.1, hW.2, _, _, .pair e₁ f₁, .pair e₂ f₂, a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩
  | letPair hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.letPair hs h₁ h₂).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, b₁, a₂, b₂, rfl, rfl, ha, hb⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ _ _ (((hγ.right hs).cons ha).cons hb)
    refine ⟨hW.1, hW.2, w₁, w₂, .letPair e₁ ?_, .letPair e₂ ?_, hw⟩ <;>
      rwa [Term.subst_liftSub₂_cons]
  | letUnit hs h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.letUnit hs h₁ h₂).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, rfl, rfl⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ γ₁ γ₂ (hγ.right hs)
    exact ⟨hW.1, hW.2, w₁, w₂, .letUnit e₁ f₁, .letUnit e₂ f₂, hw⟩
  | @inl _ _ _ _ _ B h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.inl (B := B) h).wellTyped hγ
    obtain ⟨-, -, a₁, a₂, e₁, e₂, ha⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .inl _ _ e₁, .inl _ _ e₂, Or.inl ⟨a₁, a₂, rfl, rfl, ha⟩⟩
  | @inr _ _ _ _ A _ h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.inr (A := A) h).wellTyped hγ
    obtain ⟨-, -, a₁, a₂, e₁, e₂, ha⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .inr _ _ e₁, .inr _ _ e₂, Or.inr ⟨a₁, a₂, rfl, rfl, ha⟩⟩
  | case hs h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.case hs h₁ h₂ h₃).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, hv⟩ := ih₁ γ₁ γ₂ (hγ.left hs)
    rcases hv with ⟨a₁, a₂, rfl, rfl, ha⟩ | ⟨a₁, a₂, rfl, rfl, ha⟩
    · obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₂ _ _ ((hγ.right hs).cons ha)
      refine ⟨hW.1, hW.2, w₁, w₂, .caseInl e₁ ?_, .caseInl e₂ ?_, hw⟩ <;>
        rwa [Term.subst_liftSub_cons]
    · obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ih₃ _ _ ((hγ.right hs).cons ha)
      refine ⟨hW.1, hW.2, w₁, w₂, .caseInr e₁ ?_, .caseInr e₂ ?_, hw⟩ <;>
        rwa [Term.subst_liftSub_cons]
  | falseE h ih =>
    intro γ₁ γ₂ hγ
    obtain ⟨-, -, v₁, v₂, -, -, hv⟩ := ih γ₁ γ₂ hγ
    exact hv.elim
  | withPair h₁ h₂ ih₁ ih₂ =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.withPair h₁ h₂).wellTyped hγ
    exact ⟨hW.1, hW.2, _, _, .withPair _ _, .withPair _ _, _, _, _, _, rfl, rfl,
      ih₁ γ₁ γ₂ hγ, ih₂ γ₁ γ₂ hγ⟩
  | fst h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.fst h).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, b₁, a₂, b₂, rfl, rfl, ha, -⟩ := ih γ₁ γ₂ hγ
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ha
    exact ⟨hW.1, hW.2, w₁, w₂, .fst e₁ f₁, .fst e₂ f₂, hw⟩
  | snd h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.snd h).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, b₁, a₂, b₂, rfl, rfl, -, hb⟩ := ih γ₁ γ₂ hγ
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := hb
    exact ⟨hW.1, hW.2, w₁, w₂, .snd e₁ f₁, .snd e₂ f₂, hw⟩
  | trueI h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.trueI h).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, hv⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .trueI e₁, .trueI e₂, .trueI (V.wellTyped _ hv).1,
      .trueI (V.wellTyped _ hv).2, v₁, v₂, (V.isValue _ hv).1, (V.isValue _ hv).2, rfl, rfl⟩
  | @promote n k Γ Γs ts ts' t t' As B hs hts hb ihs ihb =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.promote hs hts hb).wellTyped hγ
    have key : ∀ j, ∃ a₁ a₂ : Term 0, Eval ((ts j).subst γ₁) a₁.bang ∧
        Eval ((ts' j).subst γ₂) a₂.bang ∧ TT (V (As j)) (As j) a₁ a₂ := by
      intro j
      obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, ha⟩ := ihs j γ₁ γ₂ (hγ.splitN hs j)
      exact ⟨a₁, a₂, e₁, e₂, ha⟩
    choose a₁ a₂ e₁ e₂ ha using key
    have hC : C (fun j => some (Ty.bang (As j))) (fun j => (a₁ j).bang) (fun j => (a₂ j).bang) :=
      fun j A hj => by
        simp only [Option.some.injEq] at hj; subst hj
        exact ⟨a₁ j, a₂ j, rfl, rfl, ha j⟩
    exact ⟨hW.1, hW.2, _, _, .promote a₁ e₁, .promote a₂ e₂, _, _, rfl, rfl, ihb _ _ hC⟩
  | discard h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.discard h).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, -⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .discard e₁, .discard e₂, rfl, rfl⟩
  | copy h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.copy h).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, ha⟩ := ih γ₁ γ₂ hγ
    exact ⟨hW.1, hW.2, _, _, .copy e₁, .copy e₂, _, _, _, _, rfl, rfl,
      ⟨a₁, a₂, rfl, rfl, ha⟩, ⟨a₁, a₂, rfl, rfl, ha⟩⟩
  | derelict h ih =>
    intro γ₁ γ₂ hγ
    have hW := wellTyped_subst₂ (Cong.derelict h).wellTyped hγ
    obtain ⟨-, -, v₁, v₂, e₁, e₂, a₁, a₂, rfl, rfl, ha⟩ := ih γ₁ γ₂ hγ
    obtain ⟨-, -, w₁, w₂, f₁, f₂, hw⟩ := ha
    exact ⟨hW.1, hW.2, w₁, w₂, .derelict e₁ f₁, .derelict e₂ f₂, hw⟩

/-- A well-typed term is in the congruence closure (with itself). -/
theorem Cong.refl {n : ℕ} {Γ : LCtx n} {t : Term n} {A : Ty} (h : Lin Γ t A) : Cong Γ t t A :=
  .rel h h (fundamental h)

/-- Compatibility with application, the instance of Theorem D.8 used for composition. -/
theorem Sem.app {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₁' t₂ t₂' : Term n} {A B : Ty}
    (hs : Γ.Split Γ₁ Γ₂) (h₁ : Lin Γ₁ t₁ (.lolli A B)) (h₁' : Lin Γ₁ t₁' (.lolli A B))
    (e₁ : Sem Γ₁ t₁ t₁' (.lolli A B)) (h₂ : Lin Γ₂ t₂ A) (h₂' : Lin Γ₂ t₂' A)
    (e₂ : Sem Γ₂ t₂ t₂' A) : Sem Γ (.app t₁ t₂) (.app t₁' t₂') B :=
  (Cong.app hs (.rel h₁ h₁' e₁) (.rel h₂ h₂' e₂)).sem

/-- Compatibility with `λ`-abstraction. -/
theorem Sem.lam {n : ℕ} {Γ : LCtx n} {t t' : Term (n + 1)} {A B : Ty}
    (h : Lin (Fin.cons (some A) Γ) t B) (h' : Lin (Fin.cons (some A) Γ) t' B)
    (e : Sem (Fin.cons (some A) Γ) t t' B) : Sem Γ (.lam A t) (.lam A t') (.lolli A B) :=
  (Cong.lam (.rel h h' e)).sem

end LR

end FlowTyping
