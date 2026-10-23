module
public import RequestProject.FlowTyping.ContextIso

/-!
# The lens translation of `λF` into `λL` (Appendix C, Theorem C.2)

Every `λF` judgement is translated into a closed, conventionally well-typed `λL` lens:

* `Γ₁ ⊢ t : A ⊣ Γ₂` (linear term) ↦ `⊢ t̂ : (Γ₁°, Γ₂°) → (A°, 1)`,
* `Γ₁ ⊢ u : A/A' ⊣ Γ₂` (lens term) ↦ `⊢ û : (Γ₁°, Γ₂°) → (A°, A'°)`.

This is `LinTy.lensTrans` / `LensTy.lensTrans` (**Theorem C.2**).  The proof follows the
translation rules of Appendix C, rule by rule; each rule is realised by one of the closed
combinators of `RequestProject.FlowTyping.LensCombinators`, and context splits by the terms
`split(ψ)` and `merge(ψ)` of Definition C.1 (`FCtx.split_iso`).
-/

@[expose] public section

namespace FlowTyping

open LambdaF

/-! ## `(-)°` on type formers -/

namespace LambdaF

@[simp] lemma PTy.circ_lolli_pp (A B : PTy) :
    (PTy.lolli (.plain A) (.plain B)).circ = .lolli A.circ B.circ := by rw [PTy.circ]
@[simp] lemma PTy.circ_lolli_ps (A B B' : PTy) :
    (PTy.lolli (.plain A) (.slash B B')).circ =
      .lolli A.circ (.tensor B.circ (.lolli B'.circ .one)) := by rw [PTy.circ]
@[simp] lemma PTy.circ_lolli_sp (A A' B : PTy) :
    (PTy.lolli (.slash A A') (.plain B)).circ = .lolli A.circ (.tensor B.circ A'.circ) := by
  rw [PTy.circ]
@[simp] lemma PTy.circ_lolli_ss (A A' B B' : PTy) :
    (PTy.lolli (.slash A A') (.slash B B')).circ =
      .lolli A.circ (.tensor B.circ (.lolli B'.circ A'.circ)) := by rw [PTy.circ]
@[simp] lemma PTy.circ_tensor (A B : PTy) : (PTy.tensor A B).circ = .tensor A.circ B.circ := by
  rw [PTy.circ]
@[simp] lemma PTy.circ_one : PTy.one.circ = .one := by rw [PTy.circ]
@[simp] lemma PTy.circ_plus (A B : PTy) : (PTy.plus A B).circ = .plus A.circ B.circ := by
  rw [PTy.circ]
@[simp] lemma PTy.circ_zero : PTy.zero.circ = .zero := by rw [PTy.circ]
@[simp] lemma PTy.circ_with (A B : PTy) : (PTy.with A B).circ = .with A.circ B.circ := by
  rw [PTy.circ]
@[simp] lemma PTy.circ_top : PTy.top.circ = .top := by rw [PTy.circ]
@[simp] lemma PTy.circ_bang (A : PTy) : (PTy.bang A).circ = .bang A.circ := by rw [PTy.circ]

/-- The forward type `A°` of `T = A` or `T = A/A'`. -/
def FTy.fwd : FTy → Ty
  | .plain A => A.circ
  | .slash A _ => A.circ

/-- The backward type of `T`: `1` if `T = A`, and `A'°` if `T = A/A'`. -/
def FTy.bwd : FTy → Ty
  | .plain _ => .one
  | .slash _ A' => A'.circ

end LambdaF

/-! ## Auxiliary constructions -/

lemma Inh.withI {A B : Ty} (a : Inh A) (b : Inh B) : Inh (.with A B) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  exact ⟨.withPair a b, .withPair ha hb⟩

/-- Promotion of a function out of a context of `!`-typed variables. -/
theorem Inh.promote {k : ℕ} (As : Fin k → Ty) {B : Ty}
    (g : Inh (.lolli (Ctx.toTy (fun j => Entry.live (.bang (As j)))) B)) :
    Inh (.lolli (Ctx.toTy (fun j => Entry.live (.bang (As j)))) (.bang B)) := by
  obtain ⟨g, hg⟩ := g
  set Γ : Ctx k := fun j => Entry.live (.bang (As j)) with hΓ
  have hlive : Γ.liveOf = fun j => some (.bang (As j)) := by funext j; rfl
  have hbody : Lin (fun j => some (.bang (As j))) (.app g.weaken Γ.pack) B := by
    rw [← hlive]
    exact .app (Γ₁ := LCtx.empty k) (Γ₂ := Γ.liveOf) (fun i => Or.inl ⟨rfl, rfl⟩) hg.weaken
      Γ.pack_typing
  have hprom : Lin Γ.liveOf (.promote k (fun j => .var j) (.app g.weaken Γ.pack)) (.bang B) := by
    refine .promote (Γs := fun j => LCtx.single j (.bang (As j))) (fun i => ?_)
      (fun j => .var j _) hbody
    right
    refine ⟨i, by simp [LCtx.single, hlive], fun j hj => ?_⟩
    simp [LCtx.single, Ne.symm hj]
  exact Ctx.close Γ _ _ hprom

lemma LambdaF.FCtx.circ_bangs {k : ℕ} (As : Fin k → PTy) :
    FCtx.circ (fun j => FEntry.live (.bang (As j))) =
      Ctx.toTy (fun j => Entry.live (.bang (As j).circ)) := by
  rw [FCtx.circ_eq]
  congr 1
  funext j
  simp [FCtx.toCtx, FEntry.circ]

lemma LambdaF.FCtx.circ_bangs_succ {k : ℕ} (As : Fin (k + 1) → PTy) :
    FCtx.circ (fun j => FEntry.live (.bang (As j))) =
      .tensor (FCtx.circ (fun j : Fin k => FEntry.live (.bang (As j.succ)))) (As 0).circ.bang := by
  rw [FCtx.circ_bangs, FCtx.circ_bangs]; rfl

/-- The context-threading part of the translation of `Prom`. -/
theorem promote_chain {n : ℕ} : ∀ {k : ℕ} {Γs : Fin (k + 1) → FCtx n} {As : Fin k → PTy},
    (∀ j : Fin k, Inh (lensTy (Γs j.castSucc).circ (Γs j.succ).circ (PTy.bang (As j)).circ .one)) →
    Inh (lensTy (Γs 0).circ (Γs (Fin.last k)).circ
      (FCtx.circ (fun j => FEntry.live (.bang (As j)))) .one)
  | 0, Γs, As, _ => Comb.unitLens
  | k + 1, Γs, As, h => by
    have ih := promote_chain (Γs := fun j => Γs j.succ) (As := fun j => As j.succ) (fun j => by
      show Inh (lensTy (Γs j.castSucc.succ).circ (Γs j.succ.succ).circ _ _)
      rw [Fin.succ_castSucc]
      exact h j.succ)
    have h0 := h 0
    rw [PTy.circ_bang] at h0
    have := Comb.chain h0 ih
    rw [FCtx.circ_bangs_succ]
    exact this

/-! ## Theorem C.2 -/

open Comb in
mutual

/-- **Theorem C.2 (linear terms).** If `Γ₁ ⊢ t : A ⊣ Γ₂` in `λF`, then there is a closed `λL`
lens `⊢ t̂ : (Γ₁°, Γ₂°) → (A°, 1)`. -/
theorem LambdaF.LinTy.lensTrans {n : ℕ} {Γ Δ : FCtx n} {t : LinTm n} {A : PTy} :
    LinTy Γ t A Δ → Inh (lensTy Γ.circ Δ.circ A.circ .one)
  | .var h => by
    rw [FCtx.circ_update_dead]; exact ofSplit (FCtx.remove_iso h).1
  | .assign h₁ h₂ => assign h₁.lensTrans h₂.lensTrans
  | .unlens hs hu ht hs' => by
    have g := ht.lensTrans
    rw [FCtx.circ_dag] at g
    simpa using unlens (FCtx.split_iso hs).1 (FCtx.merge_dag hs') hu.lensTrans g
  | .letIn h₁ h₂ => by
    have g := h₂.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_dead] at g
    exact seq h₁.lensTrans g
  | .letInLens hs hu ht hs' => by
    have g := ht.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live] at g
    exact letLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 hu.lensTrans g
  | .lam (T := T) hs hb hs' => by
    have g := hb.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_dead, FCtx.circ_dag] at g
    cases T with
    | plain B =>
      simpa using lamGen (FCtx.split_iso hs).1 (FCtx.merge_dag hs') (curryPP g)
    | slash B B' =>
      simpa using lamGen (FCtx.split_iso hs).1 (FCtx.merge_dag hs') (curryPS g)
  | .lamSlash (T := T) hs hb hs' => by
    have g := hb.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_dag] at g
    cases T with
    | plain B =>
      simpa using lamGen (FCtx.split_iso hs).1 (FCtx.merge_dag hs') (currySP g)
    | slash B B' =>
      simpa using lamGen (FCtx.split_iso hs).1 (FCtx.merge_dag hs') (currySS g)
  | .app (T := T) h₁ h₂ => by
    have f := h₁.lensTrans
    have g := h₂.lensTrans
    cases T with
    | plain A => rw [PTy.circ_lolli_pp] at f; exact appPP f g
    | slash A A' => rw [PTy.circ_lolli_sp] at f; exact appSP f g
  | .pair h₁ h₂ => by simpa using pairLin h₁.lensTrans h₂.lensTrans
  | .letPair h₁ h₂ => by
    have f := h₁.lensTrans
    have g := h₂.lensTrans
    rw [PTy.circ_tensor] at f
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_cons_dead, FCtx.circ_cons_dead] at g
    exact letPairLin f g
  | .letPairLens hs hu ht hs' => by
    have u := hu.lensTrans
    have g := ht.lensTrans
    rw [PTy.circ_tensor, PTy.circ_tensor] at u
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_cons_live] at g
    exact letPairLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 u g
  | .unit => by simpa using unitLens
  | .letUnit h₁ h₂ => by
    have f := h₁.lensTrans
    rw [PTy.circ_one] at f
    exact letUnitLin f h₂.lensTrans
  | .letUnitLens hs hu ht hs' => by
    have u := hu.lensTrans
    rw [PTy.circ_one] at u
    exact letUnitLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 u ht.lensTrans
  | .inl h => by simpa using mapOut h.lensTrans inlFun
  | .inr h => by simpa using mapOut h.lensTrans inrFun
  | .case h h₁ h₂ => by
    have f := h.lensTrans
    have g₁ := h₁.lensTrans
    have g₂ := h₂.lensTrans
    rw [PTy.circ_plus] at f
    rw [FCtx.circ_cons_live, FCtx.circ_cons_dead] at g₁ g₂
    exact caseLin f (Inh.withI g₁ g₂)
  | .caseLens hs hu h₁ h₂ hs' => by
    have u := hu.lensTrans
    have g₁ := h₁.lensTrans
    have g₂ := h₂.lensTrans
    rw [PTy.circ_plus, PTy.circ_plus] at u
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live] at g₁ g₂
    exact caseLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 u (Inh.withI g₁ g₂)
  | .falseE h => by
    have f := h.lensTrans
    rw [PTy.circ_zero] at f
    exact falseLin f
  | .falseELens h => by
    have f := h.lensTrans
    rw [PTy.circ_zero] at f
    exact falseLens f
  | .withPair hs h₁ h₂ hs' => by
    have f := h₁.lensTrans
    have g := h₂.lensTrans
    rw [FCtx.circ_dag] at f g
    simpa using withLens (FCtx.split_iso hs).1 (FCtx.merge_dag hs')
      (Inh.withI (lensDone f) (lensDone g))
  | .fst h => by
    have f := h.lensTrans
    rw [PTy.circ_with] at f
    exact mapOut f fstFun
  | .snd h => by
    have f := h.lensTrans
    rw [PTy.circ_with] at f
    exact mapOut f sndFun
  | .trueI h => by simpa using mapOut h.lensTrans trueFun
  | .promote (Γs := Γs) (As := As) hts hb => by
    have g := hb.lensTrans
    rw [FCtx.circ_allDead, FCtx.circ_bangs] at g
    have p := Inh.promote (fun j => (As j).circ) (lensDone g)
    rw [← FCtx.circ_bangs] at p
    have c := promote_chain (fun j => (hts j).lensTrans)
    simpa using mapOut c p
  | .discard h => by
    have f := h.lensTrans
    rw [PTy.circ_bang] at f
    simpa using mapOut f discardFun
  | .copy h => by
    have f := h.lensTrans
    rw [PTy.circ_bang] at f
    simpa using mapOut f copyFun
  | .derelict h => by
    have f := h.lensTrans
    rw [PTy.circ_bang] at f
    exact mapOut f derelictFun

/-- **Theorem C.2 (lens terms).** If `Γ₁ ⊢ u : A/A' ⊣ Γ₂` in `λF`, then there is a closed `λL`
lens `⊢ û : (Γ₁°, Γ₂°) → (A°, A'°)`. -/
theorem LambdaF.LensTy.lensTrans {n : ℕ} {Γ Δ : FCtx n} {u : LensTm n} {A B : PTy} :
    LensTy Γ u A B Δ → Inh (lensTy Γ.circ Δ.circ A.circ B.circ)
  | .varLive (i := i) (A' := A') h => by
    have h' : Function.update Γ i (FEntry.live A') i = .live A' := by simp
    have m := (FCtx.remove_iso h').2
    rw [FCtx.update_update] at m
    exact varLive (FCtx.remove_iso h).1 m
  | .varDead (i := i) (A' := A') h => by
    have h' : Function.update Γ i (FEntry.live A') i = .live A' := by simp
    have m := (FCtx.remove_iso h').2
    rw [FCtx.update_update, ← FCtx.circ_of_dead h] at m
    simpa using varDead m
  | .lens h₁ h₂ => by
    have g := h₂.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_dead, PTy.circ_one] at g
    exact lensLit h₁.lensTrans g
  | .letIn h₁ h₂ => by
    have g := h₂.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_dead] at g
    exact seq h₁.lensTrans g
  | .letInLens hs hu ht hs' => by
    have g := ht.lensTrans
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live] at g
    exact letLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 hu.lensTrans g
  | .app (T := T) h₁ h₂ => by
    have f := h₁.lensTrans
    have g := h₂.lensTrans
    cases T with
    | plain A => rw [PTy.circ_lolli_ps] at f; exact appPS f g
    | slash A A' => rw [PTy.circ_lolli_ss] at f; exact appSS f g
  | .pair hs h₁ h₂ hs' => by
    simpa using pairLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 h₁.lensTrans h₂.lensTrans
  | .unit => by simpa using unitLens
  | .letPair h₁ h₂ => by
    have f := h₁.lensTrans
    have g := h₂.lensTrans
    rw [PTy.circ_tensor] at f
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_cons_dead, FCtx.circ_cons_dead] at g
    exact letPairLin f g
  | .letPairLens hs hu ht hs' => by
    have u := hu.lensTrans
    have g := ht.lensTrans
    rw [PTy.circ_tensor, PTy.circ_tensor] at u
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_cons_live, FCtx.circ_cons_live] at g
    exact letPairLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 u g
  | .letUnit h₁ h₂ => by
    have f := h₁.lensTrans
    rw [PTy.circ_one] at f
    exact letUnitLin f h₂.lensTrans
  | .letUnitLens hs hu ht hs' => by
    have u := hu.lensTrans
    rw [PTy.circ_one] at u
    exact letUnitLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 u ht.lensTrans
  | .case h h₁ h₂ => by
    have f := h.lensTrans
    have g₁ := h₁.lensTrans
    have g₂ := h₂.lensTrans
    rw [PTy.circ_plus] at f
    rw [FCtx.circ_cons_live, FCtx.circ_cons_dead] at g₁ g₂
    exact caseLin f (Inh.withI g₁ g₂)
  | .caseLens hs hu h₁ h₂ hs' => by
    have u := hu.lensTrans
    have g₁ := h₁.lensTrans
    have g₂ := h₂.lensTrans
    rw [PTy.circ_plus, PTy.circ_plus] at u
    rw [FCtx.circ_cons_live, FCtx.circ_cons_live] at g₁ g₂
    exact caseLens (FCtx.split_iso hs).1 (FCtx.split_iso hs').2 u (Inh.withI g₁ g₂)
  | .falseE h => by
    have f := h.lensTrans
    rw [PTy.circ_zero] at f
    exact falseLin f
  | .falseELens h => by
    have f := h.lensTrans
    rw [PTy.circ_zero] at f
    exact falseLens f

/-- **Theorem C.2** for terms `s ::= t | ~u`. -/
theorem LambdaF.TmTy.lensTrans {n : ℕ} {Γ Δ : FCtx n} {s : Tm n} {T : FTy} :
    TmTy Γ s T Δ → Inh (lensTy Γ.circ Δ.circ T.fwd T.bwd)
  | .lin h => h.lensTrans
  | .lens h => h.lensTrans

end

end FlowTyping
