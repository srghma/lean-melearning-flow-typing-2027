module
public import RequestProject.FlowTyping.Syntax

/-!
# Conventional and flow typing for `λL`

* `Lin Γ t A` is the conventional linear typing judgement `Γ ⊢ t : A` of Fig. 2.
* `Flow Γ₁ t A Γ₂` is the flow typing judgement `Γ₁ ⊢ t : A ⊣ Γ₂` of Fig. 3.

The exchange rules (`Exch`, `ExchL`, `ExchR`) are not needed: contexts are functions from
de Bruijn positions, so they are already "up to permutation".
-/

@[expose] public section

namespace FlowTyping

/-- The conventional typing rules for `λL` (Fig. 2): `Lin Γ t A` is `Γ ⊢ t : A`. -/
inductive Lin : {n : ℕ} → LCtx n → Term n → Ty → Prop
  | var {n : ℕ} (i : Fin n) (A : Ty) : Lin (LCtx.single i A) (.var i) A
  | letIn {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₂ A B} :
      Γ.Split Γ₁ Γ₂ → Lin Γ₁ t₁ A → Lin (Fin.cons (some A) Γ₂) t₂ B → Lin Γ (.letIn t₁ t₂) B
  | lam {n : ℕ} {Γ : LCtx n} {t A B} :
      Lin (Fin.cons (some A) Γ) t B → Lin Γ (.lam A t) (.lolli A B)
  | app {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₂ A B} :
      Γ.Split Γ₁ Γ₂ → Lin Γ₁ t₁ (.lolli A B) → Lin Γ₂ t₂ A → Lin Γ (.app t₁ t₂) B
  | pair {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₂ A B} :
      Γ.Split Γ₁ Γ₂ → Lin Γ₁ t₁ A → Lin Γ₂ t₂ B → Lin Γ (.pair t₁ t₂) (.tensor A B)
  | letPair {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₂ A B C} :
      Γ.Split Γ₁ Γ₂ → Lin Γ₁ t₁ (.tensor A B) →
      Lin (Fin.cons (some B) (Fin.cons (some A) Γ₂)) t₂ C → Lin Γ (.letPair t₁ t₂) C
  | unit {n : ℕ} : Lin (LCtx.empty n) .unit .one
  | letUnit {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₂ A} :
      Γ.Split Γ₁ Γ₂ → Lin Γ₁ t₁ .one → Lin Γ₂ t₂ A → Lin Γ (.letUnit t₁ t₂) A
  | inl {n : ℕ} {Γ : LCtx n} {t A B} : Lin Γ t A → Lin Γ (.inl A B t) (.plus A B)
  | inr {n : ℕ} {Γ : LCtx n} {t A B} : Lin Γ t B → Lin Γ (.inr A B t) (.plus A B)
  | case {n : ℕ} {Γ Γ₁ Γ₂ : LCtx n} {t₁ t₂ t₃ A B C} :
      Γ.Split Γ₁ Γ₂ → Lin Γ₁ t₁ (.plus A B) → Lin (Fin.cons (some A) Γ₂) t₂ C →
      Lin (Fin.cons (some B) Γ₂) t₃ C → Lin Γ (.case t₁ t₂ t₃) C
  | falseE {n : ℕ} {Γ : LCtx n} {t B} : Lin Γ t .zero → Lin Γ (.falseE B t) B
  | withPair {n : ℕ} {Γ : LCtx n} {t₁ t₂ A B} :
      Lin Γ t₁ A → Lin Γ t₂ B → Lin Γ (.withPair t₁ t₂) (.with A B)
  | fst {n : ℕ} {Γ : LCtx n} {t A B} : Lin Γ t (.with A B) → Lin Γ (.fst t) A
  | snd {n : ℕ} {Γ : LCtx n} {t A B} : Lin Γ t (.with A B) → Lin Γ (.snd t) B
  | trueI {n : ℕ} {Γ : LCtx n} {t A} : Lin Γ t A → Lin Γ (.trueI t) .top
  | promote {n k : ℕ} {Γ : LCtx n} {Γs : Fin k → LCtx n} {ts : Fin k → Term n} {t : Term k}
      {As : Fin k → Ty} {B : Ty} :
      Γ.SplitN Γs → (∀ j, Lin (Γs j) (ts j) (.bang (As j))) →
      Lin (fun j => some (.bang (As j))) t B → Lin Γ (.promote k ts t) (.bang B)
  | discard {n : ℕ} {Γ : LCtx n} {t A} : Lin Γ t (.bang A) → Lin Γ (.discard t) .one
  | copy {n : ℕ} {Γ : LCtx n} {t A} :
      Lin Γ t (.bang A) → Lin Γ (.copy t) (.tensor (.bang A) (.bang A))
  | derelict {n : ℕ} {Γ : LCtx n} {t A} : Lin Γ t (.bang A) → Lin Γ (.derelict t) A

/-- The flow typing rules for `λL` (Fig. 3): `Flow Γ₁ t A Γ₂` is `Γ₁ ⊢ t : A ⊣ Γ₂`.

In the rules `⊸-I` and `&-I` the input context is split as `Γ₁, Γ₂` and the output context
is `Γ₁, Γ₂†`; this is expressed with two `Ctx.Split` hypotheses. -/
inductive Flow : {n : ℕ} → Ctx n → Term n → Ty → Ctx n → Prop
  | var {n : ℕ} {Γ : Ctx n} {i : Fin n} {A : Ty} :
      Γ i = .live A → Flow Γ (.var i) A (Function.update Γ i .dead)
  | letIn {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} {t₁ t₂ A B} :
      Flow Γ₁ t₁ A Γ₂ → Flow (Fin.cons (.live A) Γ₂) t₂ B (Fin.cons .dead Γ₃) →
      Flow Γ₁ (.letIn t₁ t₂) B Γ₃
  | lam {n : ℕ} {Γ Γ₁ Γ₂ Δ : Ctx n} {t A B} :
      Γ.Split Γ₁ Γ₂ → Flow (Fin.cons (.live A) Γ₂) t B (Fin.cons .dead Γ₂.dag) →
      Δ.Split Γ₁ Γ₂.dag → Flow Γ (.lam A t) (.lolli A B) Δ
  | app {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} {t₁ t₂ A B} :
      Flow Γ₁ t₁ (.lolli A B) Γ₂ → Flow Γ₂ t₂ A Γ₃ → Flow Γ₁ (.app t₁ t₂) B Γ₃
  | pair {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} {t₁ t₂ A B} :
      Flow Γ₁ t₁ A Γ₂ → Flow Γ₂ t₂ B Γ₃ → Flow Γ₁ (.pair t₁ t₂) (.tensor A B) Γ₃
  | letPair {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} {t₁ t₂ A B C} :
      Flow Γ₁ t₁ (.tensor A B) Γ₂ →
      Flow (Fin.cons (.live B) (Fin.cons (.live A) Γ₂)) t₂ C
        (Fin.cons .dead (Fin.cons .dead Γ₃)) →
      Flow Γ₁ (.letPair t₁ t₂) C Γ₃
  | unit {n : ℕ} {Γ : Ctx n} : Flow Γ .unit .one Γ
  | letUnit {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} {t₁ t₂ A} :
      Flow Γ₁ t₁ .one Γ₂ → Flow Γ₂ t₂ A Γ₃ → Flow Γ₁ (.letUnit t₁ t₂) A Γ₃
  | inl {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A B} : Flow Γ₁ t A Γ₂ → Flow Γ₁ (.inl A B t) (.plus A B) Γ₂
  | inr {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A B} : Flow Γ₁ t B Γ₂ → Flow Γ₁ (.inr A B t) (.plus A B) Γ₂
  | case {n : ℕ} {Γ₁ Γ₂ Γ₃ : Ctx n} {t₁ t₂ t₃ A B C} :
      Flow Γ₁ t₁ (.plus A B) Γ₂ →
      Flow (Fin.cons (.live A) Γ₂) t₂ C (Fin.cons .dead Γ₃) →
      Flow (Fin.cons (.live B) Γ₂) t₃ C (Fin.cons .dead Γ₃) →
      Flow Γ₁ (.case t₁ t₂ t₃) C Γ₃
  | falseE {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t B} : Flow Γ₁ t .zero Γ₂ → Flow Γ₁ (.falseE B t) B Γ₂
  | withPair {n : ℕ} {Γ Γ₁ Γ₂ Δ : Ctx n} {t₁ t₂ A B} :
      Γ.Split Γ₁ Γ₂ → Flow Γ₂ t₁ A Γ₂.dag → Flow Γ₂ t₂ B Γ₂.dag →
      Δ.Split Γ₁ Γ₂.dag → Flow Γ (.withPair t₁ t₂) (.with A B) Δ
  | fst {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A B} : Flow Γ₁ t (.with A B) Γ₂ → Flow Γ₁ (.fst t) A Γ₂
  | snd {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A B} : Flow Γ₁ t (.with A B) Γ₂ → Flow Γ₁ (.snd t) B Γ₂
  | trueI {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A} : Flow Γ₁ t A Γ₂ → Flow Γ₁ (.trueI t) .top Γ₂
  | promote {n k : ℕ} {Γs : Fin (k + 1) → Ctx n} {ts : Fin k → Term n} {t : Term k}
      {As : Fin k → Ty} {B : Ty} :
      (∀ j : Fin k, Flow (Γs j.castSucc) (ts j) (.bang (As j)) (Γs j.succ)) →
      Flow (fun j => .live (.bang (As j))) t B (fun _ => .dead) →
      Flow (Γs 0) (.promote k ts t) (.bang B) (Γs (Fin.last k))
  | discard {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A} : Flow Γ₁ t (.bang A) Γ₂ → Flow Γ₁ (.discard t) .one Γ₂
  | copy {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A} :
      Flow Γ₁ t (.bang A) Γ₂ → Flow Γ₁ (.copy t) (.tensor (.bang A) (.bang A)) Γ₂
  | derelict {n : ℕ} {Γ₁ Γ₂ : Ctx n} {t A} : Flow Γ₁ t (.bang A) Γ₂ → Flow Γ₁ (.derelict t) A Γ₂

end FlowTyping
