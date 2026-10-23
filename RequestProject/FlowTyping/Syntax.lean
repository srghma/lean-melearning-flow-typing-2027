module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Basic

/-!
# Flow typing: syntax of the linear lambda calculus `λL`

Formalisation of Section 2 (Fig. 1) and Sections 3–4 (lenses, flow contexts) of
*Flow Typing: A New Lens on Linearity* (Wilshaw & Hutton).

Terms use de Bruijn indices: `Term n` is the type of terms with (at most) `n` free variables,
so `Term 0` is the type of closed terms.  Binders extend the scope; by convention the most
recently bound variable is `var 0`.

* `letIn t₁ t₂` is `let x = t₁ in t₂`, where `x` is `var 0` in `t₂`.
* `lam A t` is `λx : A. t`.
* `letPair t₁ t₂` is `let (x, y) = t₁ in t₂`, where in `t₂` we have `y = var 0`, `x = var 1`.
* `case t t₁ t₂` is `case t of inl(x) → t₁ | inr(y) → t₂`, both branches bind `var 0`.
* `promote k ts t` is `promote t₁, …, tₖ for x₁, …, xₖ in t`; the body `t : Term k` is closed
  except for the `k` promoted variables, `var j` in `t` being bound to `ts j`.
-/

@[expose] public section

namespace FlowTyping

/-- Types of `λL` (Fig. 1):
`A, B ::= α | A ⊸ B | A ⊗ B | 1 | A ⊕ B | 0 | A & B | ⊤ | !A`. -/
inductive Ty where
  | tvar : ℕ → Ty
  | lolli : Ty → Ty → Ty
  | tensor : Ty → Ty → Ty
  | one : Ty
  | plus : Ty → Ty → Ty
  | zero : Ty
  | with : Ty → Ty → Ty
  | top : Ty
  | bang : Ty → Ty
  deriving DecidableEq, Repr

/-- Terms of `λL` (Fig. 1), with de Bruijn indices.  `Term n` has `n` variables in scope. -/
inductive Term : ℕ → Type where
  /-- a variable `x` -/
  | var {n : ℕ} : Fin n → Term n
  /-- `let x = t₁ in t₂` -/
  | letIn {n : ℕ} : Term n → Term (n + 1) → Term n
  /-- `λx : A. t` -/
  | lam {n : ℕ} : Ty → Term (n + 1) → Term n
  /-- `t₁ t₂` -/
  | app {n : ℕ} : Term n → Term n → Term n
  /-- `(t₁, t₂)` -/
  | pair {n : ℕ} : Term n → Term n → Term n
  /-- `let (x, y) = t₁ in t₂` (in `t₂`: `x = var 1`, `y = var 0`) -/
  | letPair {n : ℕ} : Term n → Term (n + 2) → Term n
  /-- `∗` -/
  | unit {n : ℕ} : Term n
  /-- `let ∗ = t₁ in t₂` -/
  | letUnit {n : ℕ} : Term n → Term n → Term n
  /-- `inl_{A ⊕ B}(t)` -/
  | inl {n : ℕ} : Ty → Ty → Term n → Term n
  /-- `inr_{A ⊕ B}(t)` -/
  | inr {n : ℕ} : Ty → Ty → Term n → Term n
  /-- `case t of inl(x) → t₁ | inr(y) → t₂` -/
  | case {n : ℕ} : Term n → Term (n + 1) → Term (n + 1) → Term n
  /-- `false_B(t)` -/
  | falseE {n : ℕ} : Ty → Term n → Term n
  /-- `t₁ & t₂` -/
  | withPair {n : ℕ} : Term n → Term n → Term n
  /-- `fst(t)` -/
  | fst {n : ℕ} : Term n → Term n
  /-- `snd(t)` -/
  | snd {n : ℕ} : Term n → Term n
  /-- `true(t)` -/
  | trueI {n : ℕ} : Term n → Term n
  /-- `promote t₁, …, tₖ for x₁, …, xₖ in t` -/
  | promote {n : ℕ} (k : ℕ) : (Fin k → Term n) → Term k → Term n
  /-- `discard t` -/
  | discard {n : ℕ} : Term n → Term n
  /-- `copy t` -/
  | copy {n : ℕ} : Term n → Term n
  /-- `derelict t` -/
  | derelict {n : ℕ} : Term n → Term n

/-- The type of (heterogeneous) lenses `(S, S') → (A, A')`, Definition 3.2:
it abbreviates the `λL` type `S ⊸ (A ⊗ (A' ⊸ S'))`. -/
def lensTy (S S' A A' : Ty) : Ty := .lolli S (.tensor A (.lolli A' S'))

/-- Simple lenses `S → A` are the lenses `(S, S) → (A, A)`. -/
def simpleLensTy (S A : Ty) : Ty := lensTy S S A A

/-! ## Contexts

A context for `Term n` assigns to each of the `n` de Bruijn positions an `Entry`:
the variable is either `live` with a type (`x : A`), `dead` (`x†`, Definition 4.2), or
`absent`, meaning that the variable is not part of this context at all (this is what
happens to the variables of the other half after a context split `Γ₁, Γ₂`).

Conventional `λL` contexts (Section 2) only contain live variables: they are
`LCtx n = Fin n → Option Ty`, where `none` means the variable is not in the context.
Since contexts are indexed by position, the exchange rules are built in. -/

/-- An entry of a flow typing context. -/
inductive Entry where
  /-- the variable does not belong to the context -/
  | absent : Entry
  /-- the variable is dead, `x†` -/
  | dead : Entry
  /-- the variable is live with the given type, `x : A` -/
  | live : Ty → Entry
  deriving DecidableEq, Repr

/-- Flow typing contexts for terms with `n` free variables. -/
abbrev Ctx (n : ℕ) := Fin n → Entry

/-- Conventional linear contexts for terms with `n` free variables. -/
abbrev LCtx (n : ℕ) := Fin n → Option Ty

/-- The operation `(-)†` on a single entry. -/
def Entry.dag : Entry → Entry
  | .absent => .absent
  | _ => .dead

/-- The operation `(-)†` on contexts (Section 4.4): every variable becomes dead. -/
def Ctx.dag {n : ℕ} (Γ : Ctx n) : Ctx n := fun i => (Γ i).dag

/-- The empty part of a context: no variable belongs to it. -/
def Ctx.empty (n : ℕ) : Ctx n := fun _ => .absent

/-- `Ctx.Split Γ Γ₁ Γ₂` means that `Γ` is the (disjoint) comma `Γ₁, Γ₂`: every variable
of `Γ` (live or dead) belongs to exactly one of `Γ₁`, `Γ₂`. -/
def Ctx.Split {n : ℕ} (Γ Γ₁ Γ₂ : Ctx n) : Prop :=
  ∀ i, (Γ₁ i = .absent ∧ Γ₂ i = Γ i) ∨ (Γ₂ i = .absent ∧ Γ₁ i = Γ i)

/-- Embedding of conventional linear contexts into flow contexts. -/
def Entry.ofOption : Option Ty → Entry
  | none => .absent
  | some A => .live A

/-- Embedding of conventional linear contexts into flow contexts. -/
def LCtx.embed {n : ℕ} (Γ : LCtx n) : Ctx n := fun i => Entry.ofOption (Γ i)

/-- `LCtx.Split Γ Γ₁ Γ₂` means that `Γ` is the disjoint comma `Γ₁, Γ₂`. -/
def LCtx.Split {n : ℕ} (Γ Γ₁ Γ₂ : LCtx n) : Prop :=
  ∀ i, (Γ₁ i = none ∧ Γ₂ i = Γ i) ∨ (Γ₂ i = none ∧ Γ₁ i = Γ i)

/-- `LCtx.SplitN Γ Γs` means that `Γ` is the disjoint comma `Γs 0, …, Γs (k-1)`. -/
def LCtx.SplitN {n k : ℕ} (Γ : LCtx n) (Γs : Fin k → LCtx n) : Prop :=
  ∀ i, (Γ i = none ∧ ∀ j, Γs j i = none) ∨ ∃ j, Γs j i = Γ i ∧ ∀ j', j' ≠ j → Γs j' i = none

/-- The empty linear context. -/
def LCtx.empty (n : ℕ) : LCtx n := fun _ => none

/-- The linear context containing only the variable `i : A`. -/
def LCtx.single {n : ℕ} (i : Fin n) (A : Ty) : LCtx n := fun j => if j = i then some A else none

/-- The `λL` type `Γ°` encoding a context (Section 4.3):
`(∅)° = 1`, `(Γ, x : A)° = Γ° ⊗ A`, `(Γ, x†)° = Γ°`.  Absent variables are skipped too.
Variable `0` is the most recent one, hence the right-most component. -/
def Ctx.toTy : {n : ℕ} → Ctx n → Ty
  | 0, _ => .one
  | _ + 1, Γ =>
    match Γ 0 with
    | .live A => .tensor (Ctx.toTy (Fin.tail Γ)) A
    | _ => Ctx.toTy (Fin.tail Γ)

end FlowTyping
