module
public import RequestProject.FlowTyping.Metatheory

/-!
# Typing proofs for `λL` (Appendix B)

* `Term.Occurs i t`: the variable `i` occurs free in `t`.
* `Flow.dead_preserved`: **Lemma B.1** — dead variables stay dead.
* `Flow.occurs_iff_usedUp`: **Lemma B.2** — a variable occurs free in `t` iff it is *used up*
  by the flow derivation of `t` (live in the input context, dead in the output context).
* `Flow.restrict_free`: **Corollary B.3** — restricting the input context to the free
  variables of `t` gives `Γ ⊢ t : A ⊣ Γ†`.
* `Flow.unique`: **Theorem B.5** — the type and the output context of a flow judgement are
  determined by the term and the input context.

(Theorem B.4 is Theorem 4.6, `lin_iff_flow`.)
-/

@[expose] public section

namespace FlowTyping

/-- `t.Occurs i`: the variable `i` occurs free in `t`. -/
def Term.Occurs : {n : ℕ} → Fin n → Term n → Prop
  | _, i, .var j => i = j
  | _, i, .letIn t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ
  | _, i, .lam _ t => t.Occurs i.succ
  | _, i, .app t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .pair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .letPair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i.succ.succ
  | _, _, .unit => False
  | _, i, .letUnit t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .inl _ _ t => t.Occurs i
  | _, i, .inr _ _ t => t.Occurs i
  | _, i, .case t t₁ t₂ => t.Occurs i ∨ (t₁.Occurs i.succ ∨ t₂.Occurs i.succ)
  | _, i, .falseE _ t => t.Occurs i
  | _, i, .withPair t₁ t₂ => t₁.Occurs i ∨ t₂.Occurs i
  | _, i, .fst t => t.Occurs i
  | _, i, .snd t => t.Occurs i
  | _, i, .trueI t => t.Occurs i
  | _, i, .promote _ ts _ => ∃ j, (ts j).Occurs i
  | _, i, .discard t => t.Occurs i
  | _, i, .copy t => t.Occurs i
  | _, i, .derelict t => t.Occurs i

/-- **Lemma B.1.** If `Γ₁ ⊢ t : A ⊣ Γ₂` and `x` is dead in `Γ₁`, then `x` is dead in `Γ₂`. -/
theorem Flow.dead_preserved {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    {i : Fin n} (hi : Γ i = .dead) : Δ i = .dead :=
  Entry.Step.of_dead (hi ▸ h.step i)

/-- The behaviour of a single variable through a judgement, depending on whether it occurs
free (`P`). -/
def Track (P : Prop) (a b : Entry) : Prop :=
  (P → (∃ B, a = .live B) ∧ b = .dead) ∧ (¬ P → b = a)

lemma Track.seq {P Q : Prop} {a b c : Entry} (h₁ : Track P a b) (h₂ : Track Q b c) :
    Track (P ∨ Q) a c := by
  constructor
  · rintro (hP | hQ)
    · obtain ⟨ha, hb⟩ := h₁.1 hP
      refine ⟨ha, ?_⟩
      by_cases hQ : Q
      · obtain ⟨⟨B, hB⟩, -⟩ := h₂.1 hQ; rw [hb] at hB; cases hB
      · rw [h₂.2 hQ, hb]
    · by_cases hP : P
      · obtain ⟨-, hb⟩ := h₁.1 hP
        obtain ⟨⟨B, hB⟩, -⟩ := h₂.1 hQ; rw [hb] at hB; cases hB
      · rw [← h₁.2 hP]; exact h₂.1 hQ
  · intro h
    push_neg at h
    rw [h₂.2 h.2, h₁.2 h.1]

lemma Track.or {P Q : Prop} {a b : Entry} (h₁ : Track P a b) (h₂ : Track Q a b) :
    Track (P ∨ Q) a b :=
  ⟨fun h => h.elim h₁.1 h₂.1, fun h => h₁.2 (fun hP => h (Or.inl hP))⟩

lemma Track.split {n : ℕ} {Γ Γ₁ Γ₂ Δ : Ctx n} (hs : Γ.Split Γ₁ Γ₂) (hs' : Δ.Split Γ₁ Γ₂.dag)
    {P : Prop} {i : Fin n} (h : Track P (Γ₂ i) (Γ₂.dag i)) : Track P (Γ i) (Δ i) := by
  rcases Ctx.split_dag hs hs' i with ⟨h2, h1, hΔ⟩ | ⟨h1, h2, hΔ⟩
  · constructor
    · intro hP; obtain ⟨⟨B, hB⟩, -⟩ := h.1 hP; rw [h2] at hB; cases hB
    · intro _; exact hΔ
  · rw [Ctx.dag_apply, h2] at h
    constructor
    · intro hP; refine ⟨(h.1 hP).1, ?_⟩; rw [hΔ]; obtain ⟨⟨B, hB⟩, -⟩ := h.1 hP; rw [hB]; rfl
    · intro hP; rw [hΔ]; exact h.2 hP

lemma Track.chain : ∀ {k : ℕ} {e : Fin (k + 1) → Entry} {P : Fin k → Prop},
    (∀ j, Track (P j) (e j.castSucc) (e j.succ)) → Track (∃ j, P j) (e 0) (e (Fin.last k))
  | 0, _, _, _ => ⟨fun ⟨j, _⟩ => j.elim0, fun _ => rfl⟩
  | k + 1, e, P, h => by
    have ih := Track.chain (e := fun j => e j.succ) (P := fun j => P j.succ) (fun j => by
      show Track (P j.succ) (e j.castSucc.succ) (e j.succ.succ)
      rw [Fin.succ_castSucc]
      exact h j.succ)
    have h0 : Track (P 0) (e 0) (e 1) := h 0
    have := h0.seq ih
    refine ⟨fun ⟨j, hj⟩ => this.1 ?_, fun hn => this.2 ?_⟩
    · cases j using Fin.cases with
      | zero => exact Or.inl hj
      | succ j => exact Or.inr ⟨j, hj⟩
    · rintro (h' | ⟨j, hj⟩)
      · exact hn ⟨0, h'⟩
      · exact hn ⟨j.succ, hj⟩

lemma Track.dag_of_not {e : Entry} {P : Prop} (h : Track P e e.dag) (hP : ¬ P) :
    e = .absent ∨ e = .dead := by
  have := h.2 hP
  cases e <;> simp_all [Entry.dag]

/-- The strong form of Lemma B.2: each variable either occurs free and goes from live to dead,
or does not occur free and is unchanged. -/
theorem Flow.track {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    ∀ i, Track (t.Occurs i) (Γ i) (Δ i) := by
  induction h with
  | @var n Γ j A hΓ =>
    intro i
    by_cases hij : i = j
    · subst hij; exact ⟨fun _ => ⟨⟨A, hΓ⟩, by simp⟩, by simp [Term.Occurs]⟩
    · refine ⟨fun h => absurd h hij, fun _ => ?_⟩
      simp [Function.update_of_ne hij]
  | letIn _ _ ih₁ ih₂ =>
    intro i
    have := ih₂ i.succ
    simp only [Fin.cons_succ] at this
    exact (ih₁ i).seq this
  | lam hs _ hs' ih =>
    intro i
    have := ih i.succ
    simp only [Fin.cons_succ] at this
    exact Track.split hs hs' this
  | app _ _ ih₁ ih₂ => intro i; exact (ih₁ i).seq (ih₂ i)
  | pair _ _ ih₁ ih₂ => intro i; exact (ih₁ i).seq (ih₂ i)
  | letPair _ _ ih₁ ih₂ =>
    intro i
    have := ih₂ i.succ.succ
    simp only [Fin.cons_succ] at this
    exact (ih₁ i).seq this
  | unit => intro i; exact ⟨fun h => h.elim, fun _ => rfl⟩
  | letUnit _ _ ih₁ ih₂ => intro i; exact (ih₁ i).seq (ih₂ i)
  | inl _ ih => exact ih
  | inr _ ih => exact ih
  | case _ _ _ ih₁ ih₂ ih₃ =>
    intro i
    have h₂ := ih₂ i.succ
    have h₃ := ih₃ i.succ
    simp only [Fin.cons_succ] at h₂ h₃
    exact (ih₁ i).seq (h₂.or h₃)
  | falseE _ ih => exact ih
  | withPair hs _ _ hs' ih₁ ih₂ =>
    intro i
    exact Track.split hs hs' ((ih₁ i).or (ih₂ i))
  | fst _ ih => exact ih
  | snd _ ih => exact ih
  | trueI _ ih => exact ih
  | @promote n k Γs ts t As B _ _ ih _ =>
    intro i
    exact Track.chain (e := fun j => Γs j i) (P := fun j => (ts j).Occurs i) (fun j => ih j i)
  | discard _ ih => exact ih
  | copy _ ih => exact ih
  | derelict _ ih => exact ih

/-- A variable that does not occur free is unchanged by a flow judgement. -/
theorem Flow.unchanged {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    {i : Fin n} (hi : ¬ t.Occurs i) : Δ i = Γ i :=
  (h.track i).2 hi

/-- **Lemma B.2.** Let `Γ₁ ⊢ t : A ⊣ Γ₂` in `λL` with the flow type system.  Then `x` occurs
free in `t` if and only if it is used up by the derivation, i.e. it is live in `Γ₁` and dead in
`Γ₂`. -/
theorem Flow.occurs_iff_usedUp {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    (i : Fin n) : t.Occurs i ↔ (∃ B, Γ i = .live B) ∧ Δ i = .dead := by
  refine ⟨(h.track i).1, fun ⟨⟨B, hB⟩, hd⟩ => ?_⟩
  by_contra hn
  rw [(h.track i).2 hn, hB] at hd
  cases hd

open Classical in
/-- The sub-context of `Γ` consisting of the variables occurring free in `t`. -/
noncomputable def Ctx.restrictFV {n : ℕ} (Γ : Ctx n) (t : Term n) : Ctx n :=
  fun i => if t.Occurs i then Γ i else .absent

open Classical in
lemma Flow.restrict_set {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, ¬ t.Occurs i) :
    Flow (fun i => if i ∈ S then .absent else Γ i) t A
      (fun i => if i ∈ S then .absent else Δ i) := by
  induction S using Finset.induction_on with
  | empty => simpa using h
  | insert a S ha ih =>
    have ih := ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
    have hu := ih.strengthen a (by simp [ha, h.unchanged (hS a (Finset.mem_insert_self a S))])
    convert hu using 1 <;>
    · funext j
      by_cases hj : j = a
      · subst hj; simp
      · simp [hj]

/-- **Corollary B.3.** If `Γ₁ ⊢ t : A ⊣ Γ₂` and `Γ` is the sub-context of `Γ₁` consisting of the
free variables of `t`, then `Γ ⊢ t : A ⊣ Γ†`. -/
theorem Flow.restrict_free {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    Flow (Γ.restrictFV t) t A (Γ.restrictFV t).dag := by
  classical
  have := h.restrict_set (Finset.univ.filter fun i => ¬ t.Occurs i) (by simp)
  convert this using 1
  · funext i; by_cases hi : t.Occurs i <;> simp [Ctx.restrictFV, hi]
  · funext i
    by_cases hi : t.Occurs i
    · obtain ⟨⟨B, hB⟩, hd⟩ := (h.track i).1 hi
      simp [Ctx.restrictFV, hi, hB, hd]
    · simp [Ctx.restrictFV, hi]

open Classical in
/-- The output context of a flow judgement is determined by the input context and the term. -/
theorem Flow.output_eq {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ)
    (i : Fin n) : Δ i = if t.Occurs i then .dead else Γ i := by
  classical
  by_cases hi : t.Occurs i
  · rw [if_pos hi]; exact ((h.track i).1 hi).2
  · rw [if_neg hi]; exact (h.track i).2 hi


lemma Flow.agree_mid {n : ℕ} {Γ Γ' Δ Δ' : Ctx n} {t : Term n} {A A' : Ty}
    (h : Flow Γ t A Δ) (h' : Flow Γ' t A' Δ') {i : Fin n} (hlive : ∃ B, Δ i = .live B)
    (hag : Γ i = Γ' i) : Δ i = Δ' i := by
  by_cases hi : t.Occurs i
  · obtain ⟨B, hB⟩ := hlive
    rw [((h.track i).1 hi).2] at hB; cases hB
  · rw [h.unchanged hi, h'.unchanged hi, hag]

lemma Ctx.Split.eq_of_live {n : ℕ} {Γ Γ₁ Γ₂ : Ctx n} (hs : Γ.Split Γ₁ Γ₂) {i : Fin n}
    (h : ∃ B, Γ₂ i = .live B) : Γ₂ i = Γ i := by
  obtain ⟨B, hB⟩ := h
  rcases hs i with ⟨_, h2⟩ | ⟨h2, _⟩
  · exact h2
  · rw [h2] at hB; cases hB

lemma Track.live_of {P : Prop} {a b : Entry} (h : Track P a b) (hP : P) : ∃ B, a = .live B :=
  (h.1 hP).1

/-- Uniqueness of types: the type of a term only depends on the entries of its free
variables in the input context. -/
theorem Flow.type_unique {n : ℕ} {Γ Δ : Ctx n} {t : Term n} {A : Ty} (h : Flow Γ t A Δ) :
    ∀ {Γ' Δ' : Ctx n} {A' : Ty}, Flow Γ' t A' Δ' → (∀ i, t.Occurs i → Γ i = Γ' i) → A = A' := by
  induction h with
  | @var n Γ i A hΓ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | var hΓ' =>
      have := hag i rfl
      rw [hΓ, hΓ'] at this; cases this; rfl
  | letIn h₁ h₂ ih₁ ih₂ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | letIn h₁' h₂' =>
      have e₁ := ih₁ h₁' (fun i hi => hag i (Or.inl hi))
      subst e₁
      refine ih₂ h₂' (fun i hi => ?_)
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        simp only [Fin.cons_succ]
        have hl := (h₂.track i.succ).live_of hi
        simp only [Fin.cons_succ] at hl
        exact h₁.agree_mid h₁' hl (hag i (Or.inr hi))
  | lam hs hb hs' ih =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | lam hs₂ hb₂ hs₂' =>
      congr 1
      refine ih hb₂ (fun i hi => ?_)
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        simp only [Fin.cons_succ]
        have hl := (hb.track i.succ).live_of hi
        have hl' := (hb₂.track i.succ).live_of hi
        simp only [Fin.cons_succ] at hl hl'
        rw [hs.eq_of_live hl, hs₂.eq_of_live hl']
        exact hag i hi
  | app h₁ h₂ ih₁ ih₂ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | app h₁' h₂' =>
      have := ih₁ h₁' (fun i hi => hag i (Or.inl hi))
      cases this; rfl
  | pair h₁ h₂ ih₁ ih₂ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | pair h₁' h₂' =>
      rw [ih₁ h₁' (fun i hi => hag i (Or.inl hi)),
        ih₂ h₂' (fun i hi => h₁.agree_mid h₁' ((h₂.track i).live_of hi) (hag i (Or.inr hi)))]
  | letPair h₁ h₂ ih₁ ih₂ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | letPair h₁' h₂' =>
      have e₁ := ih₁ h₁' (fun i hi => hag i (Or.inl hi))
      cases e₁
      refine ih₂ h₂' (fun i hi => ?_)
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          simp only [Fin.cons_succ]
          have hl := (h₂.track i.succ.succ).live_of hi
          simp only [Fin.cons_succ] at hl
          exact h₁.agree_mid h₁' hl (hag i (Or.inr hi))
  | unit => intro Γ' Δ' A' h' _; cases h'; rfl
  | letUnit h₁ h₂ ih₁ ih₂ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | letUnit h₁' h₂' =>
      exact ih₂ h₂' (fun i hi => h₁.agree_mid h₁' ((h₂.track i).live_of hi) (hag i (Or.inr hi)))
  | inl _ _ => intro Γ' Δ' A' h' _; cases h'; rfl
  | inr _ _ => intro Γ' Δ' A' h' _; cases h'; rfl
  | case h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | case h₁' h₂' h₃' =>
      have e₁ := ih₁ h₁' (fun i hi => hag i (Or.inl hi))
      cases e₁
      refine ih₂ h₂' (fun i hi => ?_)
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        simp only [Fin.cons_succ]
        have hl := (h₂.track i.succ).live_of hi
        simp only [Fin.cons_succ] at hl
        exact h₁.agree_mid h₁' hl (hag i (Or.inr (Or.inl hi)))
  | falseE _ _ => intro Γ' Δ' A' h' _; cases h'; rfl
  | withPair hs h₁ h₂ hs' ih₁ ih₂ =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | withPair hs₂ h₁' h₂' hs₂' =>
      rw [ih₁ h₁' (fun i hi => by
          rw [hs.eq_of_live ((h₁.track i).live_of hi), hs₂.eq_of_live ((h₁'.track i).live_of hi)]
          exact hag i (Or.inl hi)),
        ih₂ h₂' (fun i hi => by
          rw [hs.eq_of_live ((h₂.track i).live_of hi), hs₂.eq_of_live ((h₂'.track i).live_of hi)]
          exact hag i (Or.inr hi))]
  | fst _ ih =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | fst h₁' => have := ih h₁' hag; cases this; rfl
  | snd _ ih =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | snd h₁' => have := ih h₁' hag; cases this; rfl
  | trueI _ _ => intro Γ' Δ' A' h' _; cases h'; rfl
  | @promote n k Γs ts t As B hts hb ihs ihb =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | @promote _ _ Γs' _ _ As' B' hts' hb' =>
      -- a variable occurring in `ts j` is unchanged along the chain before `j`
      have pre : ∀ {Θs : Fin (k + 1) → Ctx n} {Xs : Fin k → Ty},
          (∀ j, Flow (Θs j.castSucc) (ts j) (.bang (Xs j)) (Θs j.succ)) →
          ∀ (j : Fin k) (i : Fin n), (ts j).Occurs i → Θs j.castSucc i = Θs 0 i := by
        intro Θs Xs hΘ j i hi
        have := chain_rel_le (fun a b : Ctx n => (∃ B, b i = .live B) → b i = a i)
          (fun _ _ => rfl)
          (fun a b c h₁ h₂ hc => by
            have e := h₂ hc
            rw [e] at hc ⊢
            exact h₁ hc)
          Θs (fun j' hl => by
            by_cases hj : (ts j').Occurs i
            · obtain ⟨B, hB⟩ := hl
              rw [(((hΘ j').track i).1 hj).2] at hB; cases hB
            · exact ((hΘ j').track i).2 hj)
          (Fin.zero_le j.castSucc)
        exact this (((hΘ j).track i).live_of hi)
      have eAs : As = As' := funext fun j => by
        have := ihs j (hts' j) (fun i hi => by
          rw [pre hts j i hi, pre hts' j i hi]; exact hag i ⟨j, hi⟩)
        exact Ty.bang.inj this
      subst eAs
      rw [ihb hb' (fun _ _ => rfl)]
  | discard _ _ => intro Γ' Δ' A' h' _; cases h'; rfl
  | copy _ ih =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | copy h₁' => have := ih h₁' hag; cases this; rfl
  | derelict _ ih =>
    intro Γ' Δ' A' h' hag
    cases h' with
    | derelict h₁' => have := ih h₁' hag; cases this; rfl

/-- **Theorem B.5.** A `λL` term has at most one type and output context, given a fixed
input context. -/
theorem Flow.unique {n : ℕ} {Γ Δ Δ' : Ctx n} {t : Term n} {A A' : Ty} (h : Flow Γ t A Δ)
    (h' : Flow Γ t A' Δ') : A = A' ∧ Δ = Δ' :=
  ⟨h.type_unique h' (fun _ _ => rfl),
    funext fun i => by rw [h.output_eq i, h'.output_eq i]⟩

end FlowTyping
