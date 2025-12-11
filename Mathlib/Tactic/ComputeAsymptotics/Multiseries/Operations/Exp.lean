/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Powser

/-!
# Exponent of Multiseries

-/

@[expose] public section

open Filter Asymptotics Topology

namespace ComputeAsymptotics

namespace PreMS

open LazySeries Stream' Seq
open scoped Nat

/-- Series defining the exponential function:
```
exp x = 1 + x/1! + x^2/2! + x^3/3! + ...
```
-/
noncomputable def expSeries : LazySeries :=
  ofFn fun n ↦ (n ! : ℝ)⁻¹

theorem expSeries_eq_cons :
    expSeries = Seq.cons 1 (ofFnFrom (fun n ↦ (n ! : ℝ)⁻¹) 1) := by
  simp only [expSeries, ofFn]
  rw [ofFnFrom_eq_cons]
  congr
  norm_num

theorem expSeries_get {n : ℕ} : expSeries.get? n = some ((n ! : ℝ)⁻¹) := by
  simp [expSeries]

theorem expSeries_toFormalMultilinearSeries_eq :
    expSeries.toFormalMultilinearSeries = NormedSpace.expSeries ℝ ℝ := by
  simp only [toFormalMultilinearSeries]
  unfold NormedSpace.expSeries FormalMultilinearSeries.ofScalars
  simp [coeff, expSeries_get]

theorem expSeries_analytic : expSeries.Analytic := by
  apply analytic_of_HasFPowerSeriesAt (f := Real.exp)
  rw [expSeries_toFormalMultilinearSeries_eq]
  convert NormedSpace.exp_hasFPowerSeriesAt_zero
  · exact Real.exp_eq_exp_ℝ
  · infer_instance

theorem expSeries_toFun : expSeries.toFun = Real.exp := by
  have := NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := ℝ)
  rw [← expSeries_toFormalMultilinearSeries_eq, ← Real.exp_eq_exp_ℝ] at this
  ext x
  simp only [toFun]
  conv_rhs => rw [show x = 0 + x by simp]
  symm
  exact HasFPowerSeriesOnBall.sum this (by simp)

/-- If `ms` approximates an eventually bounded function `f` and,
then `ms.exp` approximates `Real.exp ∘ f`. -/
noncomputable def exp {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Real.exp ms
  | List.cons _ _ =>
    match destruct ms with
    | .none => PreMS.one _
    | .some (exp, coef, tl) =>
      if exp < 0 then
        expSeries.apply ms
      else -- assume that exp = 0
        (expSeries.apply tl).mulMonomial coef.exp 0

theorem exp_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h : ms.WellOrdered)
    (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
    ms.exp.WellOrdered := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · apply WellOrdered.const
  cases ms with
  | nil => simpa [exp] using one_WellOrdered
  | cons exp coef tl =>
  simp only [PreMS.exp, destruct_cons]
  split_ifs with h_if
  · apply apply_WellOrdered h
    simpa
  have h_exp : exp = 0 := by
    unfold leadingTerm at h_nonpos
    simp only [head_cons] at h_nonpos
    contrapose! h_nonpos
    constructor
    simp only [not_lt] at h_if
    exact lt_of_le_of_ne h_if h_nonpos.symm
  subst h_exp
  clear h_if
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h
  apply mulMonomial_WellOrdered
  · exact apply_WellOrdered h_tl_wo h_comp
  · apply exp_WellOrdered h_coef_wo
    contrapose! h_nonpos
    exact Term.FirstIsPos_of_tail rfl h_nonpos

theorem exp_Approximates {f : ℝ → ℝ} {basis : Basis} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates f)
    (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
    ms.exp.Approximates (Real.exp ∘ f) := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [Approximates_const_iff, exp] at h_approx ⊢
    apply h_approx.mono
    simp
  cases ms with
  | nil =>
    simp only [exp, destruct_nil]
    apply Approximates_nil at h_approx
    apply Approximates_of_EventuallyEq (f := fun _ ↦ 1)
    · apply h_approx.mono
      simp +contextual
    exact one_Approximates h_basis
  | cons exp coef tl =>
  simp only [PreMS.exp, destruct_cons]
  split_ifs with h_if
  · rw [← expSeries_toFun]
    exact apply_Approximates expSeries_analytic h_basis (by simpa) h_approx
  have h_exp : exp = 0 := by
    unfold leadingTerm at h_nonpos
    simp only [head_cons] at h_nonpos
    contrapose! h_nonpos
    constructor
    simp only [not_lt] at h_if
    exact lt_of_le_of_ne h_if h_nonpos.symm
  subst h_exp
  clear h_if
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
  simp only [Real.rpow_zero, one_mul] at h_tl
  convert_to ((expSeries.apply tl).mulMonomial coef.exp 0).Approximates
      (fun t ↦ (Real.exp ∘ fC) t * basis_hd t ^ (0 : ℝ) * (Real.exp ∘ (fun s ↦ f s - fC s)) t)
  · ext t
    simp [← Real.exp_add]
  apply mulMonomial_Approximates h_basis
  · rw [← expSeries_toFun]
    exact apply_Approximates expSeries_analytic h_basis h_comp h_tl
  apply exp_Approximates h_basis.tail h_coef_wo h_coef
  contrapose! h_nonpos
  exact Term.FirstIsPos_of_tail rfl h_nonpos

theorem exp_Approximates_pow_of_pos
    {basis1 basis2 : Basis} {ms1 : PreMS basis1} {ms2 : PreMS basis2}
    {f g : ℝ → ℝ}
    (h_basis1 : WellFormedBasis basis1)
    (h_wo1 : ms1.WellOrdered) (h_approx1 : ms1.Approximates f) (h_trimmed1 : ms1.Trimmed)
    (h_pos1 : 0 < ms1.leadingTerm.coef)
    (h_approx2 : ms2.Approximates (Real.exp ∘ ((Real.log ∘ f) * g))) :
    ms2.Approximates (fun x ↦ (f x) ^ (g x)) := by
  apply Approximates_of_EventuallyEq _ h_approx2
  have hf_pos : ∀ᶠ t in atTop, 0 < f t :=
    eventually_pos_of_coef_pos h_pos1 h_wo1 h_approx1 h_trimmed1 h_basis1
  apply hf_pos.mono
  intro x hx
  simp [Real.rpow_def_of_pos hx]

end PreMS

end ComputeAsymptotics
