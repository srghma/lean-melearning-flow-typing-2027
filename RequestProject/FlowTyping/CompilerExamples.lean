module
public import RequestProject.FlowTyping.Examples

/-!
# Programs from the reference compiler's `examples.fl`, written in `λF`

The flow typing compiler (`flow-typing-compiler`, written in Rust) accepts a surface language
with type annotations such as `swap :: (a,b)/(c,d) -> (b,a)/(d,c)`.  Here we write the
structural examples of `examples.fl` (those that use no base types, recursion or library
functions) as closed `λF` terms of our de Bruijn grammar and check them against the typing
rules of Appendix A, at the types declared in `examples.fl`.  Type variables `a, b, …` of
`examples.fl` become arbitrary plain types `A B …`; the surface notation `~a` is `a/a`.

A function definition `f p₁ … pₖ = e` becomes nested `λ`s; a flow pattern `~(x, y)` becomes
`λz : (A ⊗ B)/(A' ⊗ B'). let (x, y) = ~z in …`, and the sequencing `e₁; e₂` becomes
`let ∗ = e₁ in e₂`.

We also prove that two kinds of term are rejected by the rules of the paper (and hence by
our formalisation):
* `LensTy.not_pair_same_var`: the lens tuple `~(x, x)` never typechecks (`~⊗-I` splits the context);
* `LinTy.not_lamSlash_capture_lens`: a flow function `λy : A/A'. ~x` that leaves the variable
  `x` it captured live never typechecks (`~⊸-I` requires captured variables to end dead).
-/

@[expose] public section

namespace FlowTyping

namespace LambdaF

/-- Closes a goal `FCtx.Split Γ Γ₁ Γ₂` between concrete contexts. -/
local macro "split_ctx" : tactic => `(tactic| (intro i; fin_cases i <;> simp))

/-- Closes a goal `Γ = Γ'` between concrete contexts. -/
local macro "ctx_eq" : tactic => `(tactic| (funext i; fin_cases i <;> rfl))

/-- The empty `λF` context for closed terms. -/
abbrev FCtx.nil : FCtx 0 := fun _ => .absent

/-! ## `swap ~(x, y) = ~(y, x)` -/

/-- `swap :: (a,b)/(c,d) -> (b,a)/(d,c)`:
`λz : (A ⊗ B)/(C ⊗ D). let (x, y) = ~z in ~(y, x)`. -/
def swapF (A B C D : PTy) : LinTm 0 :=
  .lam (.slash (.tensor A B) (.tensor C D))
    (.lens (.letPair (.lens (.var 0)) (.pair (.var 0) (.var 1))))

theorem swapF_typing (A B C D : PTy) :
    LinTy FCtx.nil (swapF A B C D)
      (.lolli (.slash (.tensor A B) (.tensor C D)) (.slash (.tensor B A) (.tensor D C)))
      FCtx.nil := by
  have hpair : LensTy ![.live B, .live A, .absent] (.pair (.var 0) (.var 1))
      (.tensor B A) (.tensor D C) ![.live D, .live C, .absent] := by
    refine LensTy.pair (Γ₁ := ![.live B, .absent, .absent]) (Γ₃ := ![.absent, .live A, .absent])
      (Γ₂ := ![.live D, .absent, .absent]) (Γ₄ := ![.absent, .live C, .absent]) ?_
      ((LensTy.varLive (i := 0) (A' := D) rfl).of_eq rfl ?_)
      ((LensTy.varLive (i := 1) (A' := C) rfl).of_eq rfl ?_) ?_
    all_goals first
      | split_ctx
      | ctx_eq
  refine .lamSlash (Γ₁ := FCtx.nil) (Γ₂ := FCtx.nil) (fun i => i.elim0)
    (.lens (.letPairLens (Γ₁ := ![.live (.tensor A B)]) (Γ₃ := ![.absent])
      (Γ₂ := ![.live (.tensor C D)]) (Γ₄ := ![.absent]) ?_
      ((LensTy.varLive (i := 0) (A' := .tensor C D) rfl).of_eq rfl ?_)
      (hpair.of_eq ?_ ?_) ?_)) (fun i => i.elim0)
  all_goals first
    | split_ctx
    | ctx_eq

/-! ## `swapPair ~(x, y) = y := x := y` -/

/-- `swapPair :: (a, b)/(b, a) -> ()`:
`λz : (A ⊗ B)/(B ⊗ A). let (x, y) = ~z in (y ≔ (x ≔ y))`. -/
def swapPairF (A B : PTy) : LinTm 0 :=
  .lam (.slash (.tensor A B) (.tensor B A))
    (.lin (.letPair (.lens (.var 0)) (.assign (.var 0) (.assign (.var 1) (.var 0)))))

theorem swapPairF_typing (A B : PTy) :
    LinTy FCtx.nil (swapPairF A B)
      (.lolli (.slash (.tensor A B) (.tensor B A)) (.plain .one)) FCtx.nil := by
  have hinner : LinTy ![.live B, .live A, .absent] (.assign (.var 1) (.var 0)) A
      ![.dead, .live B, .absent] :=
    (LinTy.assign (LinTy.var (i := 0) (A := B) rfl) (LensTy.varLive (i := 1) (A' := B) rfl)).of_eq
      rfl (by ctx_eq)
  have hbody : LinTy ![.live B, .live A, .absent] (.assign (.var 0) (.assign (.var 1) (.var 0)))
      .one ![.live A, .live B, .absent] :=
    (LinTy.assign hinner (LensTy.varDead (i := 0) (A' := A) rfl)).of_eq rfl
      (by ctx_eq)
  refine .lamSlash (Γ₁ := FCtx.nil) (Γ₂ := FCtx.nil) (fun i => i.elim0)
    (.lin (.letPairLens (Γ₁ := ![.live (.tensor A B)]) (Γ₃ := ![.absent])
      (Γ₂ := ![.live (.tensor B A)]) (Γ₄ := ![.absent]) ?_
      ((LensTy.varLive (i := 0) (A' := .tensor B A) rfl).of_eq rfl ?_)
      (hbody.of_eq ?_ ?_) ?_)) (fun i => i.elim0)
  all_goals first
    | split_ctx
    | ctx_eq

/-! ## `united ~x = ~()` -/

/-- `united :: ~a -> ~()`: `λx : A/A. ~∗`. -/
def unitedF (A : PTy) : LinTm 0 := .lam (.slash A A) (.lens .unit)

theorem unitedF_typing (A : PTy) :
    LinTy FCtx.nil (unitedF A) (.lolli (.slash A A) (.slash .one .one)) FCtx.nil := by
  refine .lamSlash (Γ₁ := FCtx.nil) (Γ₂ := FCtx.nil) (fun i => i.elim0)
    (.lens (LensTy.unit.of_eq rfl ?_)) (fun i => i.elim0)
  ctx_eq

/-! ## `map f ~x = x := f x` -/

/-- `map :: (a -> b) -> a/b -> ()`: `λf : A ⊸ B. λx : A/B. (x ≔ f x)`. -/
def mapF (A B : PTy) : LinTm 0 :=
  .lam (.plain (.lolliP A B))
    (.lin (.lam (.slash A B) (.lin (.assign (.var 0) (.app (.var 1) (.lin (.var 0)))))))

theorem mapF_typing (A B : PTy) :
    LinTy FCtx.nil (mapF A B)
      (.lolli (.plain (.lolliP A B)) (.plain (.lolli (.slash A B) (.plain .one)))) FCtx.nil := by
  have happ : LinTy ![.live A, .live (.lolliP A B)] (.app (.var 1) (.lin (.var 0))) B
      ![.dead, .dead] :=
    (LinTy.app (LinTy.var (i := 1) rfl) (.lin (LinTy.var (i := 0) (A := A) rfl))).of_eq rfl
      (by ctx_eq)
  have hbody : LinTy ![.live A, .live (.lolliP A B)] (.assign (.var 0) (.app (.var 1) (.lin (.var 0))))
      .one ![.live B, .dead] :=
    (LinTy.assign happ (LensTy.varDead (i := 0) (A' := B) rfl)).of_eq rfl
      (by ctx_eq)
  have hinner : LinTy ![.live (.lolliP A B)]
      (.lam (.slash A B) (.lin (.assign (.var 0) (.app (.var 1) (.lin (.var 0))))))
      (.lolli (.slash A B) (.plain .one)) ![.dead] := by
    refine .lamSlash (Γ₁ := ![.absent]) (Γ₂ := ![.live (.lolliP A B)]) ?_
      (.lin (hbody.of_eq ?_ ?_)) ?_
    all_goals first
      | split_ctx
      | ctx_eq
  refine .lam (Γ₁ := FCtx.nil) (Γ₂ := FCtx.nil) (fun i => i.elim0)
    (.lin (hinner.of_eq ?_ ?_)) (fun i => i.elim0)
  all_goals ctx_eq

/-! ## `unmap f x = f ~x; x` -/

/-- `unmap :: (a/b -> ()) -> a -> b`: `λf : A/B ⊸ 1. λx : A. let ∗ = f ~x in x`. -/
def unmapF (A B : PTy) : LinTm 0 :=
  .lam (.plain (.lolli (.slash A B) (.plain .one)))
    (.lin (.lam (.plain A) (.lin (.letUnit (.lin (.app (.var 1) (.lens (.var 0)))) (.var 0)))))

theorem unmapF_typing (A B : PTy) :
    LinTy FCtx.nil (unmapF A B)
      (.lolli (.plain (.lolli (.slash A B) (.plain .one))) (.plain (.lolliP A B))) FCtx.nil := by
  have happ : LinTy ![.live A, .live (.lolli (.slash A B) (.plain .one))]
      (.app (.var 1) (.lens (.var 0))) .one ![.live B, .dead] :=
    (LinTy.app (LinTy.var (i := 1) rfl) (.lens (LensTy.varLive (i := 0) (A' := B) rfl))).of_eq
      rfl (by ctx_eq)
  have hbody : LinTy ![.live A, .live (.lolli (.slash A B) (.plain .one))]
      (.letUnit (.lin (.app (.var 1) (.lens (.var 0)))) (.var 0)) B ![.dead, .dead] :=
    (LinTy.letUnit happ (LinTy.var (i := 0) rfl)).of_eq rfl (by ctx_eq)
  have hinner : LinTy ![.live (.lolli (.slash A B) (.plain .one))]
      (.lam (.plain A) (.lin (.letUnit (.lin (.app (.var 1) (.lens (.var 0)))) (.var 0))))
      (.lolliP A B) ![.dead] := by
    refine .lam (Γ₁ := ![.absent]) (Γ₂ := ![.live (.lolli (.slash A B) (.plain .one))]) ?_
      (.lin (hbody.of_eq ?_ ?_)) ?_
    all_goals first
      | split_ctx
      | ctx_eq
  refine .lam (Γ₁ := FCtx.nil) (Γ₂ := FCtx.nil) (fun i => i.elim0)
    (.lin (hinner.of_eq ?_ ?_)) (fun i => i.elim0)
  all_goals ctx_eq

/-! ## `fcomp g f ~x = ~(g ~(f ~x))` -/

/-- `fcomp :: (b/b' -> c/c') -> (a/a' -> b/b') -> a/a' -> c/c'`:
`λg. λf. λx : A/A'. ~(g ~(f ~x))`. -/
def fcompF (A A' B B' C C' : PTy) : LinTm 0 :=
  .lam (.plain (.lolli (.slash B B') (.slash C C')))
    (.lin (.lam (.plain (.lolli (.slash A A') (.slash B B')))
      (.lin (.lam (.slash A A')
        (.lens (.app (.var 2) (.lens (.app (.var 1) (.lens (.var 0))))))))))

theorem fcompF_typing (A A' B B' C C' : PTy) :
    LinTy FCtx.nil (fcompF A A' B B' C C')
      (.lolli (.plain (.lolli (.slash B B') (.slash C C')))
        (.plain (.lolli (.plain (.lolli (.slash A A') (.slash B B')))
          (.plain (.lolli (.slash A A') (.slash C C')))))) FCtx.nil := by
  set G : PTy := .lolli (.slash B B') (.slash C C')
  set F : PTy := .lolli (.slash A A') (.slash B B')
  have hbody : LensTy ![.live A, .live F, .live G]
      (.app (.var 2) (.lens (.app (.var 1) (.lens (.var 0))))) C C' ![.live A', .dead, .dead] := by
    refine LensTy.app (Γ₂ := ![.live A, .live F, .dead])
      ((LinTy.var (i := 2) (A := G) rfl).of_eq rfl ?_) (.lens ?_)
    · ctx_eq
    · refine LensTy.app (Γ₂ := ![.live A, .dead, .dead])
        ((LinTy.var (i := 1) (A := F) rfl).of_eq rfl ?_)
        (.lens ((LensTy.varLive (i := 0) (A' := A') rfl).of_eq rfl ?_))
      all_goals ctx_eq
  have h3 : LinTy ![.live F, .live G]
      (.lam (.slash A A') (.lens (.app (.var 2) (.lens (.app (.var 1) (.lens (.var 0)))))))
      (.lolli (.slash A A') (.slash C C')) ![.dead, .dead] := by
    refine .lamSlash (Γ₁ := ![.absent, .absent]) (Γ₂ := ![.live F, .live G]) ?_
      (.lens (hbody.of_eq ?_ ?_)) ?_
    all_goals first
      | split_ctx
      | ctx_eq
  have h2 : LinTy ![.live G]
      (.lam (.plain F) (.lin (.lam (.slash A A')
        (.lens (.app (.var 2) (.lens (.app (.var 1) (.lens (.var 0)))))))))
      (.lolli (.plain F) (.plain (.lolli (.slash A A') (.slash C C')))) ![.dead] := by
    refine .lam (Γ₁ := ![.absent]) (Γ₂ := ![.live G]) ?_ (.lin (h3.of_eq ?_ ?_)) ?_
    all_goals first
      | split_ctx
      | ctx_eq
  refine .lam (Γ₁ := FCtx.nil) (Γ₂ := FCtx.nil) (fun i => i.elim0)
    (.lin (h2.of_eq ?_ ?_)) (fun i => i.elim0)
  all_goals ctx_eq

/-! ## Terms rejected by the paper's rules -/

/-- The lens tuple `~(x, x)` never typechecks: the rule `~⊗-I` splits the input context
between the two components, so `x` cannot be used by both. -/
theorem LensTy.not_pair_same_var {n : ℕ} {Γ Δ : FCtx n} {i : Fin n} {A B : PTy} :
    ¬ LensTy Γ (.pair (.var i) (.var i)) A B Δ := by
  intro h
  cases h with
  | pair hs h₁ h₂ _ =>
    cases h₁ with
    | varLive e₁ =>
      cases h₂ with
      | varLive e₂ => rcases hs i with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
      | varDead e₂ => rcases hs i with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
    | varDead e₁ =>
      cases h₂ with
      | varLive e₂ => rcases hs i with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all
      | varDead e₂ => rcases hs i with ⟨h, _⟩ | ⟨h, _⟩ <;> simp_all

/-- A flow function `λy : A/A'. ~x` whose body is a lens on a variable `x` that it captured
never typechecks: the rule `~⊸-I` requires every captured variable to be dead at the end of
the body, but a lens on a variable leaves it live. -/
theorem LinTy.not_lamSlash_capture_lens {n : ℕ} {Γ Δ : FCtx n} {j : Fin n} {A A' : PTy}
    {T : PTy} : ¬ LinTy Γ (.lam (.slash A A') (.lens (.var j.succ))) T Δ := by
  intro h
  cases h with
  | @lamSlash _ _ _ Γ₂ _ _ _ _ _ _ hb _ =>
    cases hb with
    | lens hl =>
      generalize hO : (Fin.cons (.live A') Γ₂.dag : FCtx (n + 1)) = O at hl
      cases hl with
      | varLive _ =>
        have := congrFun hO j.succ
        simp only [Fin.cons_succ, Function.update_self, FCtx.dag] at this
        cases hj : Γ₂ j <;> simp [hj, FEntry.dag] at this
      | varDead _ =>
        have := congrFun hO j.succ
        simp only [Fin.cons_succ, Function.update_self, FCtx.dag] at this
        cases hj : Γ₂ j <;> simp [hj, FEntry.dag] at this

end LambdaF

end FlowTyping
