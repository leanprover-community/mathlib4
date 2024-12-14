/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Term
import Mathlib.Tactic.Tendsto.Multiseries.Trimming

/-!
Here we find the limit of series by reducing the problem to computing limits for its leading
term.
-/

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open Stream' Seq

/-- `ms.leadingTerm` is its leading monomial. -/
def leadingTerm {basis : Basis} (ms : PreMS basis) : Term :=
  match basis with
  | [] => ⟨ms, []⟩
  | List.cons _ _ =>
    match head ms with
    | none => ⟨0, List.range basis.length |>.map fun _ => 0⟩
    | some (exp, coef) =>
      let pre := coef.leadingTerm
      ⟨pre.coef, exp :: pre.exps⟩

/-- `Term.coef ms.coef.leadingTerm` is equal to `Term.coef ms.leadingTerm`. -/
theorem leadingTerm_cons_coef {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    (@leadingTerm (basis_hd :: basis_tl) (cons (exp, coef) tl)).coef = coef.leadingTerm.coef := by
  conv => lhs; simp [leadingTerm]

theorem leadingTerm_length {basis : Basis} {ms : PreMS basis} :
    ms.leadingTerm.exps.length = basis.length :=
  match basis with
  | [] => by simp [leadingTerm]
  | List.cons basis_hd basis_tl => by
    cases ms <;> simp [leadingTerm, leadingTerm_length]

theorem leadingTerm_cons_toFun {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} (x : ℝ) :
    (leadingTerm (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)).toFun
      (basis_hd :: basis_tl) x =
    (basis_hd x)^exp * (leadingTerm coef).toFun basis_tl x := by
  simp [leadingTerm, Term.toFun]
  conv =>
    congr <;> rw [Term.fold_eq_mul]
    lhs
    rw [mul_comm] -- why do I need these rws? Why ring_nf can't solve the goal?
  rw [← mul_assoc]

theorem zero_of_leadingTerm_zero_coef {basis : Basis} {ms : PreMS basis} (h_trimmed : ms.Trimmed)
    (h : ms.leadingTerm.coef = 0) : ms = zero basis := by
  cases basis with
  | nil =>
    simp [leadingTerm] at h
    exact h
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · rfl
    simp [leadingTerm] at h
    replace h_trimmed := Trimmed_cons h_trimmed
    have : coef = zero _ := zero_of_leadingTerm_zero_coef h_trimmed.left h
    simp [this, zero_FlatZero] at h_trimmed

/-- If `ms` is not flat zero, then eventually `ms.leadingTerm.toFun` is non-zero. -/
theorem leadingTerm_eventually_ne_zero {basis : Basis} {ms : PreMS basis}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ¬ ms.FlatZero)
    (h_basis : WellFormedBasis basis) :
    ∀ᶠ x in atTop, ms.leadingTerm.toFun basis x ≠ 0 := by
  cases basis with
  | nil =>
    unfold leadingTerm
    simp [Term.toFun]
    use default
    intros
    intro
    absurd h_ne_zero
    constructor
    assumption
  | cons basis_hd basis_tl =>
    cases' ms with exp coef tl
    · absurd h_ne_zero
      constructor
    · obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      let coef_ih := coef.leadingTerm_eventually_ne_zero h_coef_trimmed h_coef_ne_zero
        (h_basis.tail)
      apply Eventually.mono <| coef_ih.and (basis_head_eventually_pos h_basis)
      rintro x ⟨coef_ih, h_basis_hd_pos⟩
      simp [leadingTerm, Term.toFun, -ne_eq]
      simp only [Term.toFun] at coef_ih
      conv =>
        rw [Term.fold_eq_mul]
        lhs
        lhs
        rw [mul_comm]
      rw [mul_assoc]
      rw [Term.fold_eq_mul] at coef_ih
      apply mul_ne_zero
      · exact (Real.rpow_pos_of_pos h_basis_hd_pos _).ne.symm
      · exact coef_ih

mutual
  /-- If function `F` is approximated by `cons (exp, coef) tl` and `coef` approximates `C`, then
  `F` is asymptotically equivalent to `C * basis_hd ^ exp`. -/
  theorem IsEquivalent_coef {basis_hd C F : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
      {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
      (h_coef : coef.Approximates C)
      (h_coef_wo : coef.WellOrdered)
      (h_coef_trimmed : coef.Trimmed)
      (h_coef_ne_zero : ¬coef.FlatZero)
      (h_tl : tl.Approximates (fun x ↦ F x - (basis_hd x)^exp * C x))
      (h_comp : leadingExp tl < ↑exp)
      (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
      F ~[atTop] fun x ↦ (basis_hd x)^exp * (C x) := by
    have coef_ih := coef.IsEquivalent_leadingTerm (F := C) h_coef_wo h_coef h_coef_trimmed
      (h_basis.tail)
    simp [IsEquivalent]
    eta_expand
    simp only [Pi.sub_apply]
    cases' tl with tl_exp tl_coef tl_tl
    · apply Approximates_nil at h_tl
      apply EventuallyEq.trans_isLittleO h_tl
      apply Asymptotics.isLittleO_zero -- should be simp lemma
    · obtain ⟨tl_C, _, h_tl_maj, _⟩ := Approximates_cons h_tl
      simp at h_comp
      let exp' := (exp + tl_exp) / 2
      specialize h_tl_maj exp' (by simp only [exp']; linarith)
      apply IsLittleO.trans h_tl_maj
      apply (isLittleO_iff_tendsto' _).mpr
      · simp_rw [← div_div]
        conv in _ / _ =>
          rw [div_eq_mul_inv, div_mul_comm, div_mul]
        apply (isLittleO_iff_tendsto' _).mp
        · have : (fun x ↦ basis_hd x ^ exp / basis_hd x ^ exp') =ᶠ[atTop]
              fun x ↦ (basis_hd x)^(exp - exp') := by
            apply Eventually.mono <| basis_head_eventually_pos h_basis
            intro x h
            simp only
            rw [← Real.rpow_sub h]
          apply IsLittleO.trans_eventuallyEq _ this.symm
          have := IsEquivalent.inv coef_ih
          apply IsEquivalent.trans_isLittleO this
          apply EventuallyEq.trans_isLittleO (Term.inv_toFun ((h_basis.tail)))
          apply Term.tail_fun_IsLittleO_head
          · rw [Term.inv_length, leadingTerm_length]
          · exact h_basis
          · simp only [exp']
            linarith
        · apply Eventually.mono <| basis_head_eventually_pos h_basis
          intro x h1 h2
          absurd h2
          apply div_ne_zero <;> exact (Real.rpow_pos_of_pos h1 _).ne.symm
      · have h_C_ne_zero : ∀ᶠ x in atTop, C x ≠ 0 := by
          obtain ⟨φ, h_φ, h_C⟩ := Asymptotics.IsEquivalent.exists_eq_mul coef_ih
          have h_φ_pos : ∀ᶠ x in atTop, 0 < φ x := by
            apply eventually_gt_of_tendsto_gt (by simp) h_φ
          apply EventuallyEq.rw (p := fun _ b => b ≠ 0) h_C.symm
          apply Eventually.mono <| h_φ_pos.and (leadingTerm_eventually_ne_zero
            h_coef_trimmed h_coef_ne_zero ((h_basis.tail)))
          rintro x ⟨h_φ_pos, h⟩
          exact mul_ne_zero h_φ_pos.ne.symm h
        apply Eventually.mono <| h_C_ne_zero.and
          (basis_head_eventually_pos h_basis)
        rintro x ⟨h_C_ne_zero, h_basis_pos⟩
        intro h
        absurd h
        apply mul_ne_zero _ h_C_ne_zero
        exact (Real.rpow_pos_of_pos h_basis_pos _).ne.symm

  /-- If `F` is approximated by trimmed multiseries `ms`, then it is asymptotically equivalent to
  `ms.leadingTerm.toFun`. -/
  theorem IsEquivalent_leadingTerm {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
      (h_wo : ms.WellOrdered)
      (h_approx : ms.Approximates F) (h_trimmed : ms.Trimmed)
      (h_basis : WellFormedBasis basis)
      : F ~[atTop] ms.leadingTerm.toFun basis := by
    cases basis with
    | nil =>
      simp [Approximates] at h_approx
      simp [leadingTerm]
      apply EventuallyEq.isEquivalent (by assumption)
    | cons basis_hd basis_tl =>
      cases' ms with exp coef tl
      · have hF := Approximates_nil h_approx
        unfold leadingTerm
        simp [Term.zero_coef_toFun]
        apply EventuallyEq.isEquivalent (by assumption)
      · obtain ⟨C, h_coef, _, h_tl⟩ := Approximates_cons h_approx
        obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
        obtain ⟨h_coef_wo, h_comp, _⟩ := WellOrdered_cons h_wo
        have coef_ih := coef.IsEquivalent_leadingTerm (F := C) h_coef_wo h_coef h_coef_trimmed
          (h_basis.tail)
        have : F ~[atTop] fun x ↦ (basis_hd x)^exp * (C x) :=
          IsEquivalent_coef h_coef h_coef_wo h_coef_trimmed h_coef_ne_zero h_tl h_comp h_basis
        apply IsEquivalent.trans this
        eta_expand
        simp_rw [leadingTerm_cons_toFun]
        apply IsEquivalent.mul IsEquivalent.refl
        exact coef_ih
end

-- TODO: to another file
-- TODO: generalize
lemma eventually_pos_of_IsEquivallent {l : Filter ℝ} {f g : ℝ → ℝ} (h : f ~[l] g)
    (hg : ∀ᶠ x in l, 0 < g x) : ∀ᶠ x in l, 0 < f x := by
  obtain ⟨φ, hφ_tendsto, h_eq⟩ := Asymptotics.IsEquivalent.exists_eq_mul h
  have hφ : ∀ᶠ x in l, 1/2 < φ x := by
    apply eventually_gt_of_tendsto_gt _ hφ_tendsto
    linarith
  apply Eventually.mono <| (h_eq.and hφ).and hg
  intro x ⟨⟨h_eq, hφ⟩, hg⟩
  rw [h_eq]
  simp
  nlinarith

/-- If `f` is approximated by `ms`, and `ms.leadingTerm.coef > 0`, then
`f` is eventually positive. -/
theorem eventually_pos_of_coef_pos {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_pos : 0 < ms.leadingTerm.coef) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis):
    ∀ᶠ x in atTop, 0 < F x := by
  apply eventually_pos_of_IsEquivallent (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)
  exact Term.toFun_pos h_basis h_pos

/-- If `f` is approximated by `ms`, and `ms` is not flat zero, then
`f` is eventually non-zero. -/
theorem eventually_ne_zero_of_not_FlatZero {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_ne_zero : ¬ ms.FlatZero) (h_wo : ms.WellOrdered) (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis):
    ∀ᶠ x in atTop, F x ≠ 0 := by
  have := IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis
  obtain ⟨φ, hφ_tendsto, h_eq⟩ := Asymptotics.IsEquivalent.exists_eq_mul this
  have hφ : ∀ᶠ x in atTop, 1/2 < φ x := by
    apply eventually_gt_of_tendsto_gt _ hφ_tendsto
    linarith
  have h_leadingTerm := leadingTerm_eventually_ne_zero h_trimmed h_ne_zero h_basis
  simp only [EventuallyEq] at h_eq
  apply Eventually.mono <| (h_eq.and hφ).and h_leadingTerm
  intro x ⟨⟨h_eq, hφ⟩, h_leadingTerm⟩
  rw [h_eq]
  simp
  constructor
  · linarith
  · exact h_leadingTerm

--------------------------------

-- TODO: remove assumptions here using `zero_of_leadingTerm_zero_coef`
theorem tendsto_zero_of_zero_coef {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_coef : t_coef = 0) :
    Tendsto F atTop (nhds 0) := by
  apply (IsEquivalent.tendsto_nhds_iff (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  rw [h_eq]
  apply Term.tendsto_zero_of_coef_zero _ h_coef

theorem tendsto_const_of_AllZero {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.AllZero t_exps) :
    Tendsto F atTop (nhds t_coef) := by
  apply (IsEquivalent.tendsto_nhds_iff (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  rw [h_eq]
  apply Term.tendsto_const_of_AllZero _ h_exps
  · convert leadingTerm_length (ms := ms)
    simp [h_eq]

theorem tendsto_zero_of_FirstIsNeg {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.FirstIsNeg t_exps) :
    Tendsto F atTop (nhds 0) := by
  cases' basis with basis_hd basis_tl
  · simp [leadingTerm] at h_eq
    simp [h_eq.right, Term.FirstIsNeg] at h_exps
  cases' ms with exp coef tl
  · apply Approximates_nil at h_approx
    apply Tendsto.congr' h_approx.symm
    apply tendsto_const_nhds
  · obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
    obtain ⟨C, h_coef_approx, h_maj, h_tl_approx⟩ := Approximates_cons h_approx
    simp [leadingTerm] at h_eq
    simp [← h_eq.right, Term.FirstIsNeg] at h_exps
    cases' h_exps with h_neg h_zero
    · exact majorated_tendsto_zero_of_neg h_neg h_maj
    have hC : Tendsto C atTop (nhds 0) := by
      apply tendsto_zero_of_FirstIsNeg (t_coef := t_coef) h_coef_wo h_coef_approx _ h_zero.right
      rw [← h_eq.left]
    have h_tl : Tendsto (F - C) atTop (nhds 0) := by
      have h : Tendsto (fun x ↦ F x - basis_hd x ^ exp * C x) atTop (nhds 0) := by
        apply neg_leadingExp_tendsto_zero _ h_tl_approx
        convert h_comp
        simp [h_zero.left]
      apply Tendsto.congr' _ h
      simp [h_zero.left]
      rfl
    simpa using Tendsto.add h_tl hC

theorem tendsto_top_of_FirstIsPos {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.FirstIsPos t_exps)
    (h_coef : 0 < t_coef) :
    Tendsto F atTop atTop := by
  apply (IsEquivalent.tendsto_atTop_iff (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  apply Term.tendsto_top_of_FirstIsPos h_basis leadingTerm_length
  all_goals simpa [h_eq]

theorem tendsto_bot_of_FirstIsPos {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates F)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : List ℝ}
    (h_eq : ms.leadingTerm = ⟨t_coef, t_exps⟩)
    (h_exps : Term.FirstIsPos t_exps)
    (h_coef : t_coef < 0) :
    Tendsto F atTop atBot := by
  apply (IsEquivalent.tendsto_atBot_iff (IsEquivalent_leadingTerm h_wo h_approx h_trimmed h_basis)).mpr
  apply Term.tendsto_bot_of_FirstIsPos h_basis leadingTerm_length
  all_goals simpa [h_eq]

end PreMS

end TendstoTactic
