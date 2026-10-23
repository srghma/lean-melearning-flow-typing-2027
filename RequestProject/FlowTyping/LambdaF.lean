module
public import RequestProject.FlowTyping.Syntax

/-!
# The flow typing calculus `λF` (Section 5)

Syntax (Fig. 4) and typing rules (Section 5) of the flow typing calculus `λF`, again with
de Bruijn indices: `LinTm n`, `LensTm n` and `Tm n` are the linear terms `t`, lens terms `u`
and terms `s ::= t | ~u` with `n` variables in scope.

Binding conventions are as for `λL` (see `RequestProject.FlowTyping.Syntax`); in addition
`lens t₁ t₂` is `lens x ← t₁ in t₂`, binding `x = var 0` in `t₂`.

The paper gives the typing rules of `λF` throughout Section 5 (the complete listing is in an
appendix that is not part of the article).  We include every rule stated in Section 5, and
complete the system as described there: the rules for the remaining linear-term formers are
copied from Fig. 3, the pattern-matching rules with a linear scrutinee are copied from Fig. 3
with a body `s : T` that may be a linear or a lens term, and the flow elimination rule `~1-E`
for `1` is the nullary instance of `~⊗-E`.
-/

@[expose] public section

namespace FlowTyping

namespace LambdaF

mutual
/-- Plain types of `λF`:
`A, B ::= α | T ⊸ T' | A ⊗ B | 1 | A ⊕ B | 0 | A & B | ⊤ | !A`. -/
inductive PTy where
  | tvar : ℕ → PTy
  | lolli : FTy → FTy → PTy
  | tensor : PTy → PTy → PTy
  | one : PTy
  | plus : PTy → PTy → PTy
  | zero : PTy
  | with : PTy → PTy → PTy
  | top : PTy
  | bang : PTy → PTy

/-- Types of `λF`: `T ::= A | A/B`. -/
inductive FTy where
  | plain : PTy → FTy
  | slash : PTy → PTy → FTy
end

mutual
/-- Linear terms `t` of `λF` (Fig. 4). -/
inductive LinTm : ℕ → Type where
  /-- `x` -/
  | var {n : ℕ} : Fin n → LinTm n
  /-- `u ≔ t` -/
  | assign {n : ℕ} : LensTm n → LinTm n → LinTm n
  /-- `unlens u in t` -/
  | unlens {n : ℕ} : LensTm n → LinTm n → LinTm n
  /-- `let x = s in t` -/
  | letIn {n : ℕ} : Tm n → LinTm (n + 1) → LinTm n
  /-- `λx : T. s` -/
  | lam {n : ℕ} : FTy → Tm (n + 1) → LinTm n
  /-- `t s` -/
  | app {n : ℕ} : LinTm n → Tm n → LinTm n
  /-- `(t₁, t₂)` -/
  | pair {n : ℕ} : LinTm n → LinTm n → LinTm n
  /-- `let (x, y) = s in t` -/
  | letPair {n : ℕ} : Tm n → LinTm (n + 2) → LinTm n
  /-- `∗` -/
  | unit {n : ℕ} : LinTm n
  /-- `let ∗ = s in t` -/
  | letUnit {n : ℕ} : Tm n → LinTm n → LinTm n
  /-- `inl_{A ⊕ B}(t)` -/
  | inl {n : ℕ} : PTy → PTy → LinTm n → LinTm n
  /-- `inr_{A ⊕ B}(t)` -/
  | inr {n : ℕ} : PTy → PTy → LinTm n → LinTm n
  /-- `case s of inl(x) → t₁ | inr(y) → t₂` -/
  | case {n : ℕ} : Tm n → LinTm (n + 1) → LinTm (n + 1) → LinTm n
  /-- `false_A(s)` -/
  | falseE {n : ℕ} : PTy → Tm n → LinTm n
  /-- `t₁ & t₂` -/
  | withPair {n : ℕ} : LinTm n → LinTm n → LinTm n
  /-- `fst(t)` -/
  | fst {n : ℕ} : LinTm n → LinTm n
  /-- `snd(t)` -/
  | snd {n : ℕ} : LinTm n → LinTm n
  /-- `true(t)` -/
  | trueI {n : ℕ} : LinTm n → LinTm n
  /-- `promote t₁, …, tₖ for x₁, …, xₖ in t` -/
  | promote {n : ℕ} (k : ℕ) : (Fin k → LinTm n) → LinTm k → LinTm n
  /-- `discard t` -/
  | discard {n : ℕ} : LinTm n → LinTm n
  /-- `copy t` -/
  | copy {n : ℕ} : LinTm n → LinTm n
  /-- `derelict t` -/
  | derelict {n : ℕ} : LinTm n → LinTm n

/-- Lens terms `u` of `λF` (Fig. 4). -/
inductive LensTm : ℕ → Type where
  /-- `x` -/
  | var {n : ℕ} : Fin n → LensTm n
  /-- `lens x ← t₁ in t₂` -/
  | lens {n : ℕ} : LinTm n → LinTm (n + 1) → LensTm n
  /-- `let x = s in u` -/
  | letIn {n : ℕ} : Tm n → LensTm (n + 1) → LensTm n
  /-- `t s` -/
  | app {n : ℕ} : LinTm n → Tm n → LensTm n
  /-- `(u₁, u₂)` -/
  | pair {n : ℕ} : LensTm n → LensTm n → LensTm n
  /-- `let (x, y) = s in u` -/
  | letPair {n : ℕ} : Tm n → LensTm (n + 2) → LensTm n
  /-- `∗` -/
  | unit {n : ℕ} : LensTm n
  /-- `let ∗ = s in u` -/
  | letUnit {n : ℕ} : Tm n → LensTm n → LensTm n
  /-- `case s of inl(x) → u₁ | inr(y) → u₂` -/
  | case {n : ℕ} : Tm n → LensTm (n + 1) → LensTm (n + 1) → LensTm n
  /-- `false_A(s)` -/
  | falseE {n : ℕ} : PTy → Tm n → LensTm n

/-- Terms `s ::= t | ~u` of `λF`. -/
inductive Tm : ℕ → Type where
  /-- a linear term `t` -/
  | lin {n : ℕ} : LinTm n → Tm n
  /-- a tagged lens term `~u` -/
  | lens {n : ℕ} : LensTm n → Tm n
end

/-! ## Contexts of `λF` -/

/-- An entry of a `λF` context: absent, dead (`x†`) or live (`x : A`). -/
inductive FEntry where
  | absent : FEntry
  | dead : FEntry
  | live : PTy → FEntry

/-- `λF` contexts (Definition 5.1) for terms with `n` free variables. -/
abbrev FCtx (n : ℕ) := Fin n → FEntry

/-- `(-)†` on a single entry. -/
def FEntry.dag : FEntry → FEntry
  | .absent => .absent
  | _ => .dead

/-- `(-)†` on contexts. -/
def FCtx.dag {n : ℕ} (Γ : FCtx n) : FCtx n := fun i => (Γ i).dag

/-- `FCtx.Split Γ Γ₁ Γ₂` means that `Γ` is the disjoint comma `Γ₁, Γ₂`. -/
def FCtx.Split {n : ℕ} (Γ Γ₁ Γ₂ : FCtx n) : Prop :=
  ∀ i, (Γ₁ i = .absent ∧ Γ₂ i = Γ i) ∨ (Γ₂ i = .absent ∧ Γ₁ i = Γ i)

/-- The type `A ⊸ B` between plain types. -/
abbrev PTy.lolliP (A B : PTy) : PTy := .lolli (.plain A) (.plain B)

/-! ## Typing rules of `λF` -/

mutual
/-- `LinTy Γ₁ t A Γ₂` is the judgement `Γ₁ ⊢ t : A ⊣ Γ₂` for a linear term `t`. -/
inductive LinTy : {n : ℕ} → FCtx n → LinTm n → PTy → FCtx n → Prop
  /-- `Var` (Fig. 3) -/
  | var {n : ℕ} {Γ : FCtx n} {i : Fin n} {A : PTy} :
      Γ i = .live A → LinTy Γ (.var i) A (Function.update Γ i .dead)
  /-- `Assign` -/
  | assign {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t u A B} :
      LinTy Γ₁ t B Γ₂ → LensTy Γ₂ u A B Γ₃ → LinTy Γ₁ (.assign u t) A Γ₃
  /-- `Unlens` -/
  | unlens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Δ : FCtx n} {u t A B C} :
      Γ.Split Γ₁ Γ₂ → LensTy Γ₂ u A B Γ₃ → LinTy Γ₃ t C Γ₃.dag → Δ.Split Γ₁ Γ₂.dag →
      LinTy Γ (.unlens u t) (.tensor A (.lolliP B C)) Δ
  /-- `Let` with a linear scrutinee -/
  | letIn {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t₁ t₂ A B} :
      LinTy Γ₁ t₁ A Γ₂ → LinTy (Fin.cons (.live A) Γ₂) t₂ B (Fin.cons .dead Γ₃) →
      LinTy Γ₁ (.letIn (.lin t₁) t₂) B Γ₃
  /-- `~Let`: let with a lens scrutinee -/
  | letInLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u t A A' B} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u A A' Γ₂ →
      LinTy (Fin.cons (.live A) Γ₃) t B (Fin.cons (.live A') Γ₄) → Δ.Split Γ₂ Γ₄ →
      LinTy Γ (.letIn (.lens u) t) B Δ
  /-- `⊸-I`, case `A ⊸ T` -/
  | lam {n : ℕ} {Γ Γ₁ Γ₂ Δ : FCtx n} {s A T} :
      Γ.Split Γ₁ Γ₂ → TmTy (Fin.cons (.live A) Γ₂) s T (Fin.cons .dead Γ₂.dag) →
      Δ.Split Γ₁ Γ₂.dag → LinTy Γ (.lam (.plain A) s) (.lolli (.plain A) T) Δ
  /-- `/⊸-I`, case `A/A' ⊸ T` -/
  | lamSlash {n : ℕ} {Γ Γ₁ Γ₂ Δ : FCtx n} {s A A' T} :
      Γ.Split Γ₁ Γ₂ → TmTy (Fin.cons (.live A) Γ₂) s T (Fin.cons (.live A') Γ₂.dag) →
      Δ.Split Γ₁ Γ₂.dag → LinTy Γ (.lam (.slash A A') s) (.lolli (.slash A A') T) Δ
  /-- `⊸-E` with a plain result type -/
  | app {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t s T B} :
      LinTy Γ₁ t (.lolli T (.plain B)) Γ₂ → TmTy Γ₂ s T Γ₃ → LinTy Γ₁ (.app t s) B Γ₃
  /-- `⊗-I` -/
  | pair {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t₁ t₂ A B} :
      LinTy Γ₁ t₁ A Γ₂ → LinTy Γ₂ t₂ B Γ₃ → LinTy Γ₁ (.pair t₁ t₂) (.tensor A B) Γ₃
  /-- `⊗-E` with a linear scrutinee -/
  | letPair {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t₁ t₂ A B C} :
      LinTy Γ₁ t₁ (.tensor A B) Γ₂ →
      LinTy (Fin.cons (.live B) (Fin.cons (.live A) Γ₂)) t₂ C
        (Fin.cons .dead (Fin.cons .dead Γ₃)) →
      LinTy Γ₁ (.letPair (.lin t₁) t₂) C Γ₃
  /-- `~⊗-E` with a lens scrutinee -/
  | letPairLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u t A A' B B' C} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u (.tensor A B) (.tensor A' B') Γ₂ →
      LinTy (Fin.cons (.live B) (Fin.cons (.live A) Γ₃)) t C
        (Fin.cons (.live B') (Fin.cons (.live A') Γ₄)) → Δ.Split Γ₂ Γ₄ →
      LinTy Γ (.letPair (.lens u) t) C Δ
  /-- `1-I` -/
  | unit {n : ℕ} {Γ : FCtx n} : LinTy Γ .unit .one Γ
  /-- `1-E` with a linear scrutinee -/
  | letUnit {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t₁ t₂ A} :
      LinTy Γ₁ t₁ .one Γ₂ → LinTy Γ₂ t₂ A Γ₃ → LinTy Γ₁ (.letUnit (.lin t₁) t₂) A Γ₃
  /-- `~1-E` with a lens scrutinee -/
  | letUnitLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u t A} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u .one .one Γ₂ → LinTy Γ₃ t A Γ₄ → Δ.Split Γ₂ Γ₄ →
      LinTy Γ (.letUnit (.lens u) t) A Δ
  /-- `⊕-IL` -/
  | inl {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A B} :
      LinTy Γ₁ t A Γ₂ → LinTy Γ₁ (.inl A B t) (.plus A B) Γ₂
  /-- `⊕-IR` -/
  | inr {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A B} :
      LinTy Γ₁ t B Γ₂ → LinTy Γ₁ (.inr A B t) (.plus A B) Γ₂
  /-- `⊕-E` with a linear scrutinee -/
  | case {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t t₁ t₂ A B C} :
      LinTy Γ₁ t (.plus A B) Γ₂ →
      LinTy (Fin.cons (.live A) Γ₂) t₁ C (Fin.cons .dead Γ₃) →
      LinTy (Fin.cons (.live B) Γ₂) t₂ C (Fin.cons .dead Γ₃) →
      LinTy Γ₁ (.case (.lin t) t₁ t₂) C Γ₃
  /-- `~⊕-E` with a lens scrutinee -/
  | caseLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u t₁ t₂ A A' B B' C} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u (.plus A B) (.plus A' B') Γ₂ →
      LinTy (Fin.cons (.live A) Γ₃) t₁ C (Fin.cons (.live A') Γ₄) →
      LinTy (Fin.cons (.live B) Γ₃) t₂ C (Fin.cons (.live B') Γ₄) → Δ.Split Γ₂ Γ₄ →
      LinTy Γ (.case (.lens u) t₁ t₂) C Δ
  /-- `0-E` with a linear scrutinee -/
  | falseE {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t B} :
      LinTy Γ₁ t .zero Γ₂ → LinTy Γ₁ (.falseE B (.lin t)) B Γ₂
  /-- `&-I` -/
  | withPair {n : ℕ} {Γ Γ₁ Γ₂ Δ : FCtx n} {t₁ t₂ A B} :
      Γ.Split Γ₁ Γ₂ → LinTy Γ₂ t₁ A Γ₂.dag → LinTy Γ₂ t₂ B Γ₂.dag → Δ.Split Γ₁ Γ₂.dag →
      LinTy Γ (.withPair t₁ t₂) (.with A B) Δ
  /-- `&-EL` -/
  | fst {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A B} : LinTy Γ₁ t (.with A B) Γ₂ → LinTy Γ₁ (.fst t) A Γ₂
  /-- `&-ER` -/
  | snd {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A B} : LinTy Γ₁ t (.with A B) Γ₂ → LinTy Γ₁ (.snd t) B Γ₂
  /-- `⊤-I` -/
  | trueI {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A} : LinTy Γ₁ t A Γ₂ → LinTy Γ₁ (.trueI t) .top Γ₂
  /-- `Prom` -/
  | promote {n k : ℕ} {Γs : Fin (k + 1) → FCtx n} {ts : Fin k → LinTm n} {t : LinTm k}
      {As : Fin k → PTy} {B : PTy} :
      (∀ j : Fin k, LinTy (Γs j.castSucc) (ts j) (.bang (As j)) (Γs j.succ)) →
      LinTy (fun j => .live (.bang (As j))) t B (fun _ => .dead) →
      LinTy (Γs 0) (.promote k ts t) (.bang B) (Γs (Fin.last k))
  /-- `Disc` -/
  | discard {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A} :
      LinTy Γ₁ t (.bang A) Γ₂ → LinTy Γ₁ (.discard t) .one Γ₂
  /-- `Copy` -/
  | copy {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A} :
      LinTy Γ₁ t (.bang A) Γ₂ → LinTy Γ₁ (.copy t) (.tensor (.bang A) (.bang A)) Γ₂
  /-- `Der` -/
  | derelict {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A} :
      LinTy Γ₁ t (.bang A) Γ₂ → LinTy Γ₁ (.derelict t) A Γ₂

/-- `LensTy Γ₁ u A B Γ₂` is the judgement `Γ₁ ⊢ u : A/B ⊣ Γ₂` for a lens term `u`. -/
inductive LensTy : {n : ℕ} → FCtx n → LensTm n → PTy → PTy → FCtx n → Prop
  /-- `FVar-Live` -/
  | varLive {n : ℕ} {Γ : FCtx n} {i : Fin n} {A A' : PTy} :
      Γ i = .live A → LensTy Γ (.var i) A A' (Function.update Γ i (.live A'))
  /-- `FVar-Dead` -/
  | varDead {n : ℕ} {Γ : FCtx n} {i : Fin n} {A' : PTy} :
      Γ i = .dead → LensTy Γ (.var i) .one A' (Function.update Γ i (.live A'))
  /-- `Lens` (lens literals) -/
  | lens {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t₁ t₂ A A'} :
      LinTy Γ₁ t₁ A Γ₂ → LinTy (Fin.cons (.live A') Γ₂) t₂ .one (Fin.cons .dead Γ₃) →
      LensTy Γ₁ (.lens t₁ t₂) A A' Γ₃
  /-- `Let` with a linear scrutinee and a lens body -/
  | letIn {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t u A B B'} :
      LinTy Γ₁ t A Γ₂ → LensTy (Fin.cons (.live A) Γ₂) u B B' (Fin.cons .dead Γ₃) →
      LensTy Γ₁ (.letIn (.lin t) u) B B' Γ₃
  /-- `~Let` with a lens scrutinee and a lens body -/
  | letInLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u₁ u₂ A A' B B'} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u₁ A A' Γ₂ →
      LensTy (Fin.cons (.live A) Γ₃) u₂ B B' (Fin.cons (.live A') Γ₄) → Δ.Split Γ₂ Γ₄ →
      LensTy Γ (.letIn (.lens u₁) u₂) B B' Δ
  /-- `⊸-E` with a flow result type -/
  | app {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t s T B B'} :
      LinTy Γ₁ t (.lolli T (.slash B B')) Γ₂ → TmTy Γ₂ s T Γ₃ → LensTy Γ₁ (.app t s) B B' Γ₃
  /-- `~⊗-I` -/
  | pair {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u₁ u₂ A A' B B'} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u₁ A A' Γ₂ → LensTy Γ₃ u₂ B B' Γ₄ → Δ.Split Γ₂ Γ₄ →
      LensTy Γ (.pair u₁ u₂) (.tensor A B) (.tensor A' B') Δ
  /-- `~1-I` -/
  | unit {n : ℕ} {Γ : FCtx n} : LensTy Γ .unit .one .one Γ
  /-- `⊗-E` with a linear scrutinee and a lens body -/
  | letPair {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t u A B C C'} :
      LinTy Γ₁ t (.tensor A B) Γ₂ →
      LensTy (Fin.cons (.live B) (Fin.cons (.live A) Γ₂)) u C C'
        (Fin.cons .dead (Fin.cons .dead Γ₃)) →
      LensTy Γ₁ (.letPair (.lin t) u) C C' Γ₃
  /-- `~⊗-E` with a lens scrutinee and a lens body -/
  | letPairLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u₁ u₂ A A' B B' C C'} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u₁ (.tensor A B) (.tensor A' B') Γ₂ →
      LensTy (Fin.cons (.live B) (Fin.cons (.live A) Γ₃)) u₂ C C'
        (Fin.cons (.live B') (Fin.cons (.live A') Γ₄)) → Δ.Split Γ₂ Γ₄ →
      LensTy Γ (.letPair (.lens u₁) u₂) C C' Δ
  /-- `1-E` with a linear scrutinee and a lens body -/
  | letUnit {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t u C C'} :
      LinTy Γ₁ t .one Γ₂ → LensTy Γ₂ u C C' Γ₃ → LensTy Γ₁ (.letUnit (.lin t) u) C C' Γ₃
  /-- `~1-E` with a lens scrutinee and a lens body -/
  | letUnitLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u₁ u₂ C C'} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u₁ .one .one Γ₂ → LensTy Γ₃ u₂ C C' Γ₄ → Δ.Split Γ₂ Γ₄ →
      LensTy Γ (.letUnit (.lens u₁) u₂) C C' Δ
  /-- `⊕-E` with a linear scrutinee and lens branches -/
  | case {n : ℕ} {Γ₁ Γ₂ Γ₃ : FCtx n} {t u₁ u₂ A B C C'} :
      LinTy Γ₁ t (.plus A B) Γ₂ →
      LensTy (Fin.cons (.live A) Γ₂) u₁ C C' (Fin.cons .dead Γ₃) →
      LensTy (Fin.cons (.live B) Γ₂) u₂ C C' (Fin.cons .dead Γ₃) →
      LensTy Γ₁ (.case (.lin t) u₁ u₂) C C' Γ₃
  /-- `~⊕-E` with a lens scrutinee and lens branches -/
  | caseLens {n : ℕ} {Γ Γ₁ Γ₂ Γ₃ Γ₄ Δ : FCtx n} {u u₁ u₂ A A' B B' C C'} :
      Γ.Split Γ₁ Γ₃ → LensTy Γ₁ u (.plus A B) (.plus A' B') Γ₂ →
      LensTy (Fin.cons (.live A) Γ₃) u₁ C C' (Fin.cons (.live A') Γ₄) →
      LensTy (Fin.cons (.live B) Γ₃) u₂ C C' (Fin.cons (.live B') Γ₄) → Δ.Split Γ₂ Γ₄ →
      LensTy Γ (.case (.lens u) u₁ u₂) C C' Δ
  /-- `0-E` with a linear scrutinee, producing a lens term -/
  | falseE {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t C C'} :
      LinTy Γ₁ t .zero Γ₂ → LensTy Γ₁ (.falseE C (.lin t)) C C' Γ₂

/-- `TmTy Γ₁ s T Γ₂` is the abbreviated judgement `Γ₁ ⊢ s : T ⊣ Γ₂` for `s ::= t | ~u`,
where `(Γ₁ ⊢ ~u : A/A' ⊣ Γ₂) ≔ (Γ₁ ⊢ u : A/A' ⊣ Γ₂)`. -/
inductive TmTy : {n : ℕ} → FCtx n → Tm n → FTy → FCtx n → Prop
  | lin {n : ℕ} {Γ₁ Γ₂ : FCtx n} {t A} : LinTy Γ₁ t A Γ₂ → TmTy Γ₁ (.lin t) (.plain A) Γ₂
  | lens {n : ℕ} {Γ₁ Γ₂ : FCtx n} {u A A'} :
      LensTy Γ₁ u A A' Γ₂ → TmTy Γ₁ (.lens u) (.slash A A') Γ₂
end

end LambdaF

end FlowTyping
