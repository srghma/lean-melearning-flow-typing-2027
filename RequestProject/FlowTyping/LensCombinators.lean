module
public import RequestProject.FlowTyping.Checker

/-!
# Closed `λL` combinators for the lens translation (Appendix C)

Each lemma states that a type built from inhabited types is inhabited by a closed, well-typed
`λL` term.  The terms are those of the translation rules of Appendix C (written with
de Bruijn indices); their typing is established by the verified checker `check`, at type
variables, and then instantiated.  Notation: `lensTy S S' A A'` is `(S, S') → (A, A')`.
-/

@[expose] public section

namespace FlowTyping

namespace Comb

open Term

local notation "α" i => Ty.tvar i

/-- Instantiation of type variables by a list of types. -/
def tl (l : List Ty) (i : ℕ) : Ty := l.getD i .one

/-- Sequential composition `f ≫ g` (Appendix C). -/
theorem seq {S S' S'' A B B' : Ty}
    (f : Inh (lensTy S S' A Ty.one))
    (g : Inh (lensTy (Ty.tensor S' A) S'' B B')) :
    Inh (lensTy S S'' B B') :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 3) Ty.one, lensTy (Ty.tensor (α 1) (α 3)) (α 2) (α 4) (α 5)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (app (var 4) (pair (app (var 0) unit) (var 1)))))
    (lensTy (α 0) (α 2) (α 4) (α 5)) (by decide) (tl [S, S', S'', A, B, B'])
    (fun i => by fin_cases i <;> assumption)

/-- Post-composition of the forward part with a function (`c_left h ◦̂ f`). -/
theorem mapOut {S S' A A' B : Ty}
    (f : Inh (lensTy S S' A A'))
    (h : Inh (Ty.lolli A B)) :
    Inh (lensTy S S' B A') :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 2) (α 3), Ty.lolli (α 2) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (app (var 4) (var 1)) (var 0))))
    (lensTy (α 0) (α 1) (α 4) (α 3)) (by decide) (tl [S, S', A, A', B])
    (fun i => by fin_cases i <;> assumption)

/-- Composition of functions. -/
theorem comp {A B C : Ty}
    (f : Inh (Ty.lolli A B))
    (g : Inh (Ty.lolli B C)) :
    Inh (Ty.lolli A C) :=
  Inh.of_check ![Ty.lolli (α 0) (α 1), Ty.lolli (α 1) (α 2)]
    (lam (α 0) (app (var 2) (app (var 1) (var 0))))
    (Ty.lolli (α 0) (α 2)) (by decide) (tl [A, B, C])
    (fun i => by fin_cases i <;> assumption)

/-- Post-composition of the backward part with a function. -/
theorem postRes {S S' S'' A A' : Ty}
    (f : Inh (lensTy S S' A A'))
    (μ : Inh (Ty.lolli S' S'')) :
    Inh (lensTy S S'' A A') :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 3) (α 4), Ty.lolli (α 1) (α 2)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (var 1) (lam (α 4) (app (var 5) (app (var 1) (var 0)))))))
    (lensTy (α 0) (α 2) (α 3) (α 4)) (by decide) (tl [S, S', S'', A, A'])
    (fun i => by fin_cases i <;> assumption)

/-- A lens out of a splitting `S ⊸ R ⊗ A`. -/
theorem ofSplit {S R A : Ty}
    (ρ : Inh (Ty.lolli S (Ty.tensor R A))) :
    Inh (lensTy S R A Ty.one) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2))]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (var 0) (lam Ty.one (letUnit (var 0) (var 2))))))
    (lensTy (α 0) (α 1) (α 2) Ty.one) (by decide) (tl [S, R, A])
    (fun i => by fin_cases i; assumption)

/-- Translation of `FVar-Live`. -/
theorem varLive {S R A A' S' : Ty}
    (ρ : Inh (Ty.lolli S (Ty.tensor R A)))
    (μ : Inh (Ty.lolli (Ty.tensor R A') S')) :
    Inh (lensTy S S' A A') :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 1) (α 3)) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (var 0) (lam (α 3) (app (var 5) (pair (var 2) (var 0)))))))
    (lensTy (α 0) (α 4) (α 2) (α 3)) (by decide) (tl [S, R, A, A', S'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `FVar-Dead`. -/
theorem varDead {S A' S' : Ty}
    (μ : Inh (Ty.lolli (Ty.tensor S A') S')) :
    Inh (lensTy S S' Ty.one A') :=
  Inh.of_check ![Ty.lolli (Ty.tensor (α 0) (α 1)) (α 2)]
    (lam (α 0) (pair unit (lam (α 1) (app (var 2) (pair (var 1) (var 0))))))
    (lensTy (α 0) (α 2) Ty.one (α 1)) (by decide) (tl [S, A', S'])
    (fun i => by fin_cases i; assumption)

/-- Translation of `Assign`. -/
theorem assign {S S' S'' A B : Ty}
    (f : Inh (lensTy S S' B Ty.one))
    (g : Inh (lensTy S' S'' A B)) :
    Inh (lensTy S S'' A Ty.one) :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 4) Ty.one, lensTy (α 1) (α 2) (α 3) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (pair (var 1) (lam Ty.one (letUnit (var 0) (app (var 1) (var 4))))))))
    (lensTy (α 0) (α 2) (α 3) Ty.one) (by decide) (tl [S, S', S'', A, B])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `Unlens`. -/
theorem unlens {S S₁ S₂ D S₃ A B C : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₂)))
    (μ : Inh (Ty.lolli (Ty.tensor S₁ Ty.one) D))
    (f : Inh (lensTy S₂ S₃ A B))
    (g : Inh (lensTy S₃ Ty.one C Ty.one)) :
    Inh (lensTy S D (Ty.tensor A (Ty.lolli B C)) Ty.one) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 1) Ty.one) (α 3), lensTy (α 2) (α 4) (α 5) (α 6), lensTy (α 4) Ty.one (α 7) Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 5) (var 0)) (pair (pair (var 1) (lam (α 6) (letPair (app (var 9) (app (var 1) (var 0))) (letUnit (app (var 0) unit) (var 1))))) (lam Ty.one (letUnit (var 0) (app (var 7) (pair (var 4) unit))))))))
    (lensTy (α 0) (α 3) (Ty.tensor (α 5) (Ty.lolli (α 6) (α 7))) Ty.one) (by decide) (tl [S, S₁, S₂, D, S₃, A, B, C])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~Let`. -/
theorem letLens {S S₁ S₃ S₂ S₄ D A A' B B' : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₃)))
    (μ : Inh (Ty.lolli (Ty.tensor S₂ S₄) D))
    (u : Inh (lensTy S₁ S₂ A A'))
    (t : Inh (lensTy (Ty.tensor S₃ A) (Ty.tensor S₄ A') B B')) :
    Inh (lensTy S D B B') :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 3) (α 4)) (α 5), lensTy (α 1) (α 3) (α 6) (α 7), lensTy (Ty.tensor (α 2) (α 6)) (Ty.tensor (α 4) (α 7)) (α 8) (α 9)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 5) (var 1)) (letPair (app (var 8) (pair (var 2) (var 1))) (pair (var 1) (lam (α 9) (letPair (app (var 1) (var 0)) (app (var 11) (pair (app (var 5) (var 0)) (var 1))))))))))
    (lensTy (α 0) (α 5) (α 8) (α 9)) (by decide) (tl [S, S₁, S₃, S₂, S₄, D, A, A', B, B'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of the `⊸-I` rules, given the curried body. -/
theorem lamGen {S S₁ S₂ D F : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₂)))
    (μ : Inh (Ty.lolli (Ty.tensor S₁ Ty.one) D))
    (h : Inh (Ty.lolli S₂ F)) :
    Inh (lensTy S D F Ty.one) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 1) Ty.one) (α 3), Ty.lolli (α 2) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (app (var 5) (var 0)) (lam Ty.one (letUnit (var 0) (app (var 5) (pair (var 2) unit)))))))
    (lensTy (α 0) (α 3) (α 4) Ty.one) (by decide) (tl [S, S₁, S₂, D, F])
    (fun i => by fin_cases i <;> assumption)

/-- Body of `⊸-I` with a plain result. -/
theorem curryPP {G A B : Ty}
    (f : Inh (lensTy (Ty.tensor G A) Ty.one B Ty.one)) :
    Inh (Ty.lolli G (Ty.lolli A B)) :=
  Inh.of_check ![lensTy (Ty.tensor (α 0) (α 1)) Ty.one (α 2) Ty.one]
    (lam (α 0) (lam (α 1) (letPair (app (var 2) (pair (var 1) (var 0))) (letUnit (app (var 0) unit) (var 1)))))
    (Ty.lolli (α 0) (Ty.lolli (α 1) (α 2))) (by decide) (tl [G, A, B])
    (fun i => by fin_cases i; assumption)

/-- Body of `⊸-I` with a flow result. -/
theorem curryPS {G A B B' : Ty}
    (f : Inh (lensTy (Ty.tensor G A) Ty.one B B')) :
    Inh (Ty.lolli G (Ty.lolli A (Ty.tensor B (Ty.lolli B' Ty.one)))) :=
  Inh.of_check ![lensTy (Ty.tensor (α 0) (α 1)) Ty.one (α 2) (α 3)]
    (lam (α 0) (lam (α 1) (app (var 2) (pair (var 1) (var 0)))))
    (Ty.lolli (α 0) (Ty.lolli (α 1) (Ty.tensor (α 2) (Ty.lolli (α 3) Ty.one)))) (by decide) (tl [G, A, B, B'])
    (fun i => by fin_cases i; assumption)

/-- Body of `~⊸-I` with a plain result. -/
theorem currySP {G A A' B : Ty}
    (f : Inh (lensTy (Ty.tensor G A) (Ty.tensor Ty.one A') B Ty.one)) :
    Inh (Ty.lolli G (Ty.lolli A (Ty.tensor B A'))) :=
  Inh.of_check ![lensTy (Ty.tensor (α 0) (α 1)) (Ty.tensor Ty.one (α 2)) (α 3) Ty.one]
    (lam (α 0) (lam (α 1) (letPair (app (var 2) (pair (var 1) (var 0))) (letPair (app (var 0) unit) (letUnit (var 1) (pair (var 3) (var 0)))))))
    (Ty.lolli (α 0) (Ty.lolli (α 1) (Ty.tensor (α 3) (α 2)))) (by decide) (tl [G, A, A', B])
    (fun i => by fin_cases i; assumption)

/-- Body of `~⊸-I` with a flow result. -/
theorem currySS {G A A' B B' : Ty}
    (f : Inh (lensTy (Ty.tensor G A) (Ty.tensor Ty.one A') B B')) :
    Inh (Ty.lolli G (Ty.lolli A (Ty.tensor B (Ty.lolli B' A')))) :=
  Inh.of_check ![lensTy (Ty.tensor (α 0) (α 1)) (Ty.tensor Ty.one (α 2)) (α 3) (α 4)]
    (lam (α 0) (lam (α 1) (letPair (app (var 2) (pair (var 1) (var 0))) (pair (var 1) (lam (α 4) (letPair (app (var 1) (var 0)) (letUnit (var 1) (var 0))))))))
    (Ty.lolli (α 0) (Ty.lolli (α 1) (Ty.tensor (α 3) (Ty.lolli (α 4) (α 2))))) (by decide) (tl [G, A, A', B, B'])
    (fun i => by fin_cases i; assumption)

/-- Translation of `⊸-E` (plain argument, plain result). -/
theorem appPP {S S' S'' A B : Ty}
    (f : Inh (lensTy S S' (Ty.lolli A B) Ty.one))
    (g : Inh (lensTy S' S'' A Ty.one)) :
    Inh (lensTy S S'' B Ty.one) :=
  Inh.of_check ![lensTy (α 0) (α 1) (Ty.lolli (α 3) (α 4)) Ty.one, lensTy (α 1) (α 2) (α 3) Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (pair (app (var 3) (var 1)) (var 0)))))
    (lensTy (α 0) (α 2) (α 4) Ty.one) (by decide) (tl [S, S', S'', A, B])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~⊸-E` (flow argument, plain result). -/
theorem appSP {S S' S'' A A' B : Ty}
    (f : Inh (lensTy S S' (Ty.lolli A (Ty.tensor B A')) Ty.one))
    (g : Inh (lensTy S' S'' A A')) :
    Inh (lensTy S S'' B Ty.one) :=
  Inh.of_check ![lensTy (α 0) (α 1) (Ty.lolli (α 3) (Ty.tensor (α 5) (α 4))) Ty.one, lensTy (α 1) (α 2) (α 3) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (letPair (app (var 3) (var 1)) (pair (var 1) (lam Ty.one (letUnit (var 0) (app (var 3) (var 1)))))))))
    (lensTy (α 0) (α 2) (α 5) Ty.one) (by decide) (tl [S, S', S'', A, A', B])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `⊸~-E` (plain argument, flow result). -/
theorem appPS {S S' S'' A B B' : Ty}
    (f : Inh (lensTy S S' (Ty.lolli A (Ty.tensor B (Ty.lolli B' Ty.one))) Ty.one))
    (g : Inh (lensTy S' S'' A Ty.one)) :
    Inh (lensTy S S'' B B') :=
  Inh.of_check ![lensTy (α 0) (α 1) (Ty.lolli (α 3) (Ty.tensor (α 4) (Ty.lolli (α 5) Ty.one))) Ty.one, lensTy (α 1) (α 2) (α 3) Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (letPair (app (var 3) (var 1)) (pair (var 1) (lam (α 5) (letUnit (app (var 1) (var 0)) (app (var 3) unit))))))))
    (lensTy (α 0) (α 2) (α 4) (α 5)) (by decide) (tl [S, S', S'', A, B, B'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~⊸~-E` (flow argument, flow result). -/
theorem appSS {S S' S'' A A' B B' : Ty}
    (f : Inh (lensTy S S' (Ty.lolli A (Ty.tensor B (Ty.lolli B' A'))) Ty.one))
    (g : Inh (lensTy S' S'' A A')) :
    Inh (lensTy S S'' B B') :=
  Inh.of_check ![lensTy (α 0) (α 1) (Ty.lolli (α 3) (Ty.tensor (α 5) (Ty.lolli (α 6) (α 4)))) Ty.one, lensTy (α 1) (α 2) (α 3) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (letPair (app (var 3) (var 1)) (pair (var 1) (lam (α 6) (app (var 3) (app (var 1) (var 0)))))))))
    (lensTy (α 0) (α 2) (α 5) (α 6)) (by decide) (tl [S, S', S'', A, A', B, B'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `⊗-I`. -/
theorem pairLin {S S' S'' A B : Ty}
    (f : Inh (lensTy S S' A Ty.one))
    (g : Inh (lensTy S' S'' B Ty.one)) :
    Inh (lensTy S S'' (Ty.tensor A B) Ty.one) :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 3) Ty.one, lensTy (α 1) (α 2) (α 4) Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (pair (pair (var 3) (var 1)) (var 0)))))
    (lensTy (α 0) (α 2) (Ty.tensor (α 3) (α 4)) Ty.one) (by decide) (tl [S, S', S'', A, B])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~⊗-I`. -/
theorem pairLens {S S₁ S₃ S₂ S₄ D A A' B B' : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₃)))
    (μ : Inh (Ty.lolli (Ty.tensor S₂ S₄) D))
    (u₁ : Inh (lensTy S₁ S₂ A A'))
    (u₂ : Inh (lensTy S₃ S₄ B B')) :
    Inh (lensTy S D (Ty.tensor A B) (Ty.tensor A' B')) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 3) (α 4)) (α 5), lensTy (α 1) (α 3) (α 6) (α 7), lensTy (α 2) (α 4) (α 8) (α 9)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 5) (var 1)) (letPair (app (var 8) (var 2)) (pair (pair (var 3) (var 1)) (lam (Ty.tensor (α 7) (α 9)) (letPair (var 0) (app (var 11) (pair (app (var 5) (var 1)) (app (var 3) (var 0)))))))))))
    (lensTy (α 0) (α 5) (Ty.tensor (α 6) (α 8)) (Ty.tensor (α 7) (α 9))) (by decide) (tl [S, S₁, S₃, S₂, S₄, D, A, A', B, B'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `⊗-E` with a linear scrutinee. -/
theorem letPairLin {S S' S'' A B C C' : Ty}
    (f : Inh (lensTy S S' (Ty.tensor A B) Ty.one))
    (g : Inh (lensTy (Ty.tensor (Ty.tensor S' A) B) S'' C C')) :
    Inh (lensTy S S'' C C') :=
  Inh.of_check ![lensTy (α 0) (α 1) (Ty.tensor (α 3) (α 4)) Ty.one, lensTy (Ty.tensor (Ty.tensor (α 1) (α 3)) (α 4)) (α 2) (α 5) (α 6)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (var 1) (app (var 6) (pair (pair (app (var 2) unit) (var 1)) (var 0))))))
    (lensTy (α 0) (α 2) (α 5) (α 6)) (by decide) (tl [S, S', S'', A, B, C, C'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~⊗-E`. -/
theorem letPairLens {S S₁ S₃ S₂ S₄ D A B A' B' C C' : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₃)))
    (μ : Inh (Ty.lolli (Ty.tensor S₂ S₄) D))
    (u : Inh (lensTy S₁ S₂ (Ty.tensor A B) (Ty.tensor A' B')))
    (t : Inh (lensTy (Ty.tensor (Ty.tensor S₃ A) B) (Ty.tensor (Ty.tensor S₄ A') B') C C')) :
    Inh (lensTy S D C C') :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 3) (α 4)) (α 5), lensTy (α 1) (α 3) (Ty.tensor (α 6) (α 7)) (Ty.tensor (α 8) (α 9)), lensTy (Ty.tensor (Ty.tensor (α 2) (α 6)) (α 7)) (Ty.tensor (Ty.tensor (α 4) (α 8)) (α 9)) (α 10) (α 11)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 5) (var 1)) (letPair (var 1) (letPair (app (var 10) (pair (pair (var 4) (var 1)) (var 0))) (pair (var 1) (lam (α 11) (letPair (app (var 1) (var 0)) (letPair (var 1) (app (var 15) (pair (app (var 9) (pair (var 0) (var 2))) (var 1))))))))))))
    (lensTy (α 0) (α 5) (α 10) (α 11)) (by decide) (tl [S, S₁, S₃, S₂, S₄, D, A, B, A', B', C, C'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `1-I` and `~1-I`. -/
theorem unitLens {S : Ty} :
    Inh (lensTy S S Ty.one Ty.one) :=
  Inh.of_check (n := 0) ![]
    (lam (α 0) (pair unit (lam Ty.one (letUnit (var 0) (var 1)))))
    (lensTy (α 0) (α 0) Ty.one Ty.one) (by decide) (tl [S])
    (fun i => by exact i.elim0)

/-- Translation of `1-E` with a linear scrutinee. -/
theorem letUnitLin {S S' S'' X X' : Ty}
    (f : Inh (lensTy S S' Ty.one Ty.one))
    (g : Inh (lensTy S' S'' X X')) :
    Inh (lensTy S S'' X X') :=
  Inh.of_check ![lensTy (α 0) (α 1) Ty.one Ty.one, lensTy (α 1) (α 2) (α 3) (α 4)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letUnit (var 1) (app (var 4) (app (var 0) unit)))))
    (lensTy (α 0) (α 2) (α 3) (α 4)) (by decide) (tl [S, S', S'', X, X'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~1-E`. -/
theorem letUnitLens {S S₁ S₃ S₂ S₄ D X X' : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₃)))
    (μ : Inh (Ty.lolli (Ty.tensor S₂ S₄) D))
    (u : Inh (lensTy S₁ S₂ Ty.one Ty.one))
    (t : Inh (lensTy S₃ S₄ X X')) :
    Inh (lensTy S D X X') :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 3) (α 4)) (α 5), lensTy (α 1) (α 3) Ty.one Ty.one, lensTy (α 2) (α 4) (α 6) (α 7)]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 5) (var 1)) (letUnit (var 1) (letPair (app (var 8) (var 2)) (pair (var 1) (lam (α 7) (app (var 9) (pair (app (var 3) unit) (app (var 1) (var 0)))))))))))
    (lensTy (α 0) (α 5) (α 6) (α 7)) (by decide) (tl [S, S₁, S₃, S₂, S₄, D, X, X'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `⊕-E` with a linear scrutinee (the two branches packed with `&`). -/
theorem caseLin {S S' S'' A B C C' : Ty}
    (f : Inh (lensTy S S' (Ty.plus A B) Ty.one))
    (g : Inh (Ty.with (lensTy (Ty.tensor S' A) S'' C C') (lensTy (Ty.tensor S' B) S'' C C'))) :
    Inh (lensTy S S'' C C') :=
  Inh.of_check ![lensTy (α 0) (α 1) (Ty.plus (α 3) (α 4)) Ty.one, Ty.with (lensTy (Ty.tensor (α 1) (α 3)) (α 2) (α 5) (α 6)) (lensTy (Ty.tensor (α 1) (α 4)) (α 2) (α 5) (α 6))]
    (lam (α 0) (letPair (app (var 1) (var 0)) (case (var 1) (app (fst (var 5)) (pair (app (var 1) unit) (var 0))) (app (snd (var 5)) (pair (app (var 1) unit) (var 0))))))
    (lensTy (α 0) (α 2) (α 5) (α 6)) (by decide) (tl [S, S', S'', A, B, C, C'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `~⊕-E` (the two branches packed with `&`). -/
theorem caseLens {S S₁ S₃ S₂ S₄ D A B A' B' C C' : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₃)))
    (μ : Inh (Ty.lolli (Ty.tensor S₂ S₄) D))
    (u : Inh (lensTy S₁ S₂ (Ty.plus A B) (Ty.plus A' B')))
    (t : Inh (Ty.with (lensTy (Ty.tensor S₃ A) (Ty.tensor S₄ A') C C') (lensTy (Ty.tensor S₃ B) (Ty.tensor S₄ B') C C'))) :
    Inh (lensTy S D C C') :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 3) (α 4)) (α 5), lensTy (α 1) (α 3) (Ty.plus (α 6) (α 7)) (Ty.plus (α 8) (α 9)), Ty.with (lensTy (Ty.tensor (α 2) (α 6)) (Ty.tensor (α 4) (α 8)) (α 10) (α 11)) (lensTy (Ty.tensor (α 2) (α 7)) (Ty.tensor (α 4) (α 9)) (α 10) (α 11))]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 5) (var 1)) (case (var 1) (letPair (app (fst (var 9)) (pair (var 3) (var 0))) (pair (var 1) (lam (α 11) (letPair (app (var 1) (var 0)) (app (var 12) (pair (app (var 6) (inl (α 8) (α 9) (var 0))) (var 1))))))) (letPair (app (snd (var 9)) (pair (var 3) (var 0))) (pair (var 1) (lam (α 11) (letPair (app (var 1) (var 0)) (app (var 12) (pair (app (var 6) (inr (α 8) (α 9) (var 0))) (var 1)))))))))))
    (lensTy (α 0) (α 5) (α 10) (α 11)) (by decide) (tl [S, S₁, S₃, S₂, S₄, D, A, B, A', B', C, C'])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `0-E` with a linear scrutinee. -/
theorem falseLin {S S' X X' : Ty}
    (f : Inh (lensTy S S' Ty.zero Ty.one)) :
    Inh (lensTy S S' X X') :=
  Inh.of_check ![lensTy (α 0) (α 1) Ty.zero Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (falseE (Ty.tensor (α 2) (Ty.lolli (α 3) Ty.one)) (var 1)) (pair (var 1) (lam (α 3) (app (var 3) (app (var 1) (var 0))))))))
    (lensTy (α 0) (α 1) (α 2) (α 3)) (by decide) (tl [S, S', X, X'])
    (fun i => by fin_cases i; assumption)

/-- Translation of `~0-E`. -/
theorem falseLens {S S' X X' : Ty}
    (f : Inh (lensTy S S' Ty.zero Ty.zero)) :
    Inh (lensTy S S' X X') :=
  Inh.of_check ![lensTy (α 0) (α 1) Ty.zero Ty.zero]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (falseE (Ty.tensor (α 2) (Ty.lolli (α 3) Ty.zero)) (var 1)) (pair (var 1) (lam (α 3) (app (var 3) (app (var 1) (var 0))))))))
    (lensTy (α 0) (α 1) (α 2) (α 3)) (by decide) (tl [S, S', X, X'])
    (fun i => by fin_cases i; assumption)

/-- Translation of `&-I` (the two components packed with `&`). -/
theorem withLens {S S₁ S₂ D A B : Ty}
    (σ : Inh (Ty.lolli S (Ty.tensor S₁ S₂)))
    (μ : Inh (Ty.lolli (Ty.tensor S₁ Ty.one) D))
    (fg : Inh (Ty.with (Ty.lolli S₂ A) (Ty.lolli S₂ B))) :
    Inh (lensTy S D (Ty.with A B) Ty.one) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2)), Ty.lolli (Ty.tensor (α 1) Ty.one) (α 3), Ty.with (Ty.lolli (α 2) (α 4)) (Ty.lolli (α 2) (α 5))]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (withPair (app (fst (var 5)) (var 0)) (app (snd (var 5)) (var 0))) (lam Ty.one (letUnit (var 0) (app (var 5) (pair (var 2) unit)))))))
    (lensTy (α 0) (α 3) (Ty.with (α 4) (α 5)) Ty.one) (by decide) (tl [S, S₁, S₂, D, A, B])
    (fun i => by fin_cases i <;> assumption)

/-- Translation of `Lens` (lens literals). -/
theorem lensLit {S S' S'' A A' : Ty}
    (f : Inh (lensTy S S' A Ty.one))
    (g : Inh (lensTy (Ty.tensor S' A') S'' Ty.one Ty.one)) :
    Inh (lensTy S S'' A A') :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 3) Ty.one, lensTy (Ty.tensor (α 1) (α 4)) (α 2) Ty.one Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (pair (var 1) (lam (α 4) (letPair (app (var 5) (pair (app (var 1) unit) (var 0))) (letUnit (var 1) (app (var 0) unit)))))))
    (lensTy (α 0) (α 2) (α 3) (α 4)) (by decide) (tl [S, S', S'', A, A'])
    (fun i => by fin_cases i <;> assumption)

/-- One step of the translation of `Prom`. -/
theorem chain {S S₁ S₂ X D : Ty}
    (f : Inh (lensTy S S₁ X Ty.one))
    (h : Inh (lensTy S₁ S₂ D Ty.one)) :
    Inh (lensTy S S₂ (Ty.tensor D X) Ty.one) :=
  Inh.of_check ![lensTy (α 0) (α 1) (α 3) Ty.one, lensTy (α 1) (α 2) (α 4) Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (app (var 4) (app (var 0) unit)) (pair (pair (var 1) (var 3)) (var 0)))))
    (lensTy (α 0) (α 2) (Ty.tensor (α 4) (α 3)) Ty.one) (by decide) (tl [S, S₁, S₂, X, D])
    (fun i => by fin_cases i <;> assumption)

/-- A lens with trivial output state is a function. -/
theorem lensDone {S B : Ty}
    (g : Inh (lensTy S Ty.one B Ty.one)) :
    Inh (Ty.lolli S B) :=
  Inh.of_check ![lensTy (α 0) Ty.one (α 1) Ty.one]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letUnit (app (var 0) unit) (var 1))))
    (Ty.lolli (α 0) (α 1)) (by decide) (tl [S, B])
    (fun i => by fin_cases i; assumption)

/-- Context splitting: adding a component on the left part. -/
theorem tensorL {X Y Z A : Ty}
    (ρ : Inh (Ty.lolli X (Ty.tensor Y Z))) :
    Inh (Ty.lolli (Ty.tensor X A) (Ty.tensor (Ty.tensor Y A) Z)) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2))]
    (lam (Ty.tensor (α 0) (α 3)) (letPair (var 0) (letPair (app (var 3) (var 1)) (pair (pair (var 1) (var 2)) (var 0)))))
    (Ty.lolli (Ty.tensor (α 0) (α 3)) (Ty.tensor (Ty.tensor (α 1) (α 3)) (α 2))) (by decide) (tl [X, Y, Z, A])
    (fun i => by fin_cases i; assumption)

/-- Context splitting: adding a component on the right part. -/
theorem tensorR {X Y Z A : Ty}
    (ρ : Inh (Ty.lolli X (Ty.tensor Y Z))) :
    Inh (Ty.lolli (Ty.tensor X A) (Ty.tensor Y (Ty.tensor Z A))) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (α 2))]
    (lam (Ty.tensor (α 0) (α 3)) (letPair (var 0) (letPair (app (var 3) (var 1)) (pair (var 1) (pair (var 0) (var 2))))))
    (Ty.lolli (Ty.tensor (α 0) (α 3)) (Ty.tensor (α 1) (Ty.tensor (α 2) (α 3)))) (by decide) (tl [X, Y, Z, A])
    (fun i => by fin_cases i; assumption)

/-- Context merging: adding a component from the left part. -/
theorem mergeL {X Y Z A : Ty}
    (μ : Inh (Ty.lolli (Ty.tensor Y Z) X)) :
    Inh (Ty.lolli (Ty.tensor (Ty.tensor Y A) Z) (Ty.tensor X A)) :=
  Inh.of_check ![Ty.lolli (Ty.tensor (α 1) (α 2)) (α 0)]
    (lam (Ty.tensor (Ty.tensor (α 1) (α 3)) (α 2)) (letPair (var 0) (letPair (var 1) (pair (app (var 5) (pair (var 1) (var 2))) (var 0)))))
    (Ty.lolli (Ty.tensor (Ty.tensor (α 1) (α 3)) (α 2)) (Ty.tensor (α 0) (α 3))) (by decide) (tl [X, Y, Z, A])
    (fun i => by fin_cases i; assumption)

/-- Context merging: adding a component from the right part. -/
theorem mergeR {X Y Z A : Ty}
    (μ : Inh (Ty.lolli (Ty.tensor Y Z) X)) :
    Inh (Ty.lolli (Ty.tensor Y (Ty.tensor Z A)) (Ty.tensor X A)) :=
  Inh.of_check ![Ty.lolli (Ty.tensor (α 1) (α 2)) (α 0)]
    (lam (Ty.tensor (α 1) (Ty.tensor (α 2) (α 3))) (letPair (var 0) (letPair (var 0) (pair (app (var 5) (pair (var 3) (var 1))) (var 0)))))
    (Ty.lolli (Ty.tensor (α 1) (Ty.tensor (α 2) (α 3))) (Ty.tensor (α 0) (α 3))) (by decide) (tl [X, Y, Z, A])
    (fun i => by fin_cases i; assumption)

/-- Splitting off a single variable. -/
theorem unitSplit {X R A : Ty}
    (ρ : Inh (Ty.lolli X (Ty.tensor R (Ty.tensor Ty.one A)))) :
    Inh (Ty.lolli X (Ty.tensor R A)) :=
  Inh.of_check ![Ty.lolli (α 0) (Ty.tensor (α 1) (Ty.tensor Ty.one (α 2)))]
    (lam (α 0) (letPair (app (var 1) (var 0)) (letPair (var 0) (letUnit (var 1) (pair (var 3) (var 0))))))
    (Ty.lolli (α 0) (Ty.tensor (α 1) (α 2))) (by decide) (tl [X, R, A])
    (fun i => by fin_cases i; assumption)

/-- Merging a single variable. -/
theorem unitMerge {X R A : Ty}
    (μ : Inh (Ty.lolli (Ty.tensor R (Ty.tensor Ty.one A)) X)) :
    Inh (Ty.lolli (Ty.tensor R A) X) :=
  Inh.of_check ![Ty.lolli (Ty.tensor (α 1) (Ty.tensor Ty.one (α 2))) (α 0)]
    (lam (Ty.tensor (α 1) (α 2)) (letPair (var 0) (app (var 3) (pair (var 1) (pair unit (var 0))))))
    (Ty.lolli (Ty.tensor (α 1) (α 2)) (α 0)) (by decide) (tl [X, R, A])
    (fun i => by fin_cases i; assumption)

/-- The empty context splits into two empty contexts. -/
theorem oneSplit :
    Inh (Ty.lolli Ty.one (Ty.tensor Ty.one Ty.one)) :=
  Inh.of_check (n := 0) ![]
    (lam Ty.one (letUnit (var 0) (pair unit unit)))
    (Ty.lolli Ty.one (Ty.tensor Ty.one Ty.one)) (by decide) (tl [])
    (fun i => by exact i.elim0)

/-- Two empty contexts merge into the empty context. -/
theorem oneMerge :
    Inh (Ty.lolli (Ty.tensor Ty.one Ty.one) Ty.one) :=
  Inh.of_check (n := 0) ![]
    (lam (Ty.tensor Ty.one Ty.one) (letPair (var 0) (letUnit (var 0) (var 1))))
    (Ty.lolli (Ty.tensor Ty.one Ty.one) Ty.one) (by decide) (tl [])
    (fun i => by exact i.elim0)

/-- The identity function. -/
theorem idFun {A : Ty} :
    Inh (Ty.lolli A A) :=
  Inh.of_check (n := 0) ![]
    (lam (α 0) (var 0))
    (Ty.lolli (α 0) (α 0)) (by decide) (tl [A])
    (fun i => by exact i.elim0)

/-- Left injection. -/
theorem inlFun {A B : Ty} :
    Inh (Ty.lolli A (Ty.plus A B)) :=
  Inh.of_check (n := 0) ![]
    (lam (α 0) (inl (α 0) (α 1) (var 0)))
    (Ty.lolli (α 0) (Ty.plus (α 0) (α 1))) (by decide) (tl [A, B])
    (fun i => by exact i.elim0)

/-- Right injection. -/
theorem inrFun {A B : Ty} :
    Inh (Ty.lolli B (Ty.plus A B)) :=
  Inh.of_check (n := 0) ![]
    (lam (α 1) (inr (α 0) (α 1) (var 0)))
    (Ty.lolli (α 1) (Ty.plus (α 0) (α 1))) (by decide) (tl [A, B])
    (fun i => by exact i.elim0)

/-- First projection. -/
theorem fstFun {A B : Ty} :
    Inh (Ty.lolli (Ty.with A B) A) :=
  Inh.of_check (n := 0) ![]
    (lam (Ty.with (α 0) (α 1)) (fst (var 0)))
    (Ty.lolli (Ty.with (α 0) (α 1)) (α 0)) (by decide) (tl [A, B])
    (fun i => by exact i.elim0)

/-- Second projection. -/
theorem sndFun {A B : Ty} :
    Inh (Ty.lolli (Ty.with A B) B) :=
  Inh.of_check (n := 0) ![]
    (lam (Ty.with (α 0) (α 1)) (snd (var 0)))
    (Ty.lolli (Ty.with (α 0) (α 1)) (α 1)) (by decide) (tl [A, B])
    (fun i => by exact i.elim0)

/-- Introduction of `⊤`. -/
theorem trueFun {A : Ty} :
    Inh (Ty.lolli A Ty.top) :=
  Inh.of_check (n := 0) ![]
    (lam (α 0) (trueI (var 0)))
    (Ty.lolli (α 0) Ty.top) (by decide) (tl [A])
    (fun i => by exact i.elim0)

/-- `discard`. -/
theorem discardFun {A : Ty} :
    Inh (Ty.lolli (Ty.bang A) Ty.one) :=
  Inh.of_check (n := 0) ![]
    (lam (Ty.bang (α 0)) (discard (var 0)))
    (Ty.lolli (Ty.bang (α 0)) Ty.one) (by decide) (tl [A])
    (fun i => by exact i.elim0)

/-- `copy`. -/
theorem copyFun {A : Ty} :
    Inh (Ty.lolli (Ty.bang A) (Ty.tensor (Ty.bang A) (Ty.bang A))) :=
  Inh.of_check (n := 0) ![]
    (lam (Ty.bang (α 0)) (copy (var 0)))
    (Ty.lolli (Ty.bang (α 0)) (Ty.tensor (Ty.bang (α 0)) (Ty.bang (α 0)))) (by decide) (tl [A])
    (fun i => by exact i.elim0)

/-- `derelict`. -/
theorem derelictFun {A : Ty} :
    Inh (Ty.lolli (Ty.bang A) A) :=
  Inh.of_check (n := 0) ![]
    (lam (Ty.bang (α 0)) (derelict (var 0)))
    (Ty.lolli (Ty.bang (α 0)) (α 0)) (by decide) (tl [A])
    (fun i => by exact i.elim0)

end Comb

end FlowTyping
