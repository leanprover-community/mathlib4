/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Powser

/-!
# Exponent of Multiseries

-/

open Filter Asymptotics Topology

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq
open scoped Nat

-- exp (x) = 1 + x/1! + x^2/2! + x^3/3! + ...

noncomputable def expSeries : LazySeries :=
  ofFn fun n ↦ (n ! : ℝ)⁻¹

theorem expSeries_eq_cons :
    expSeries = Seq.cons 1 (ofFnFrom (fun n ↦ (n ! : ℝ)⁻¹) 1) := by
  simp [expSeries, ofFn]
  rw [ofFnFrom_eq_cons]
  congr
  norm_num

theorem expSeries_get {n : ℕ} : expSeries.get? n = some ((n ! : ℝ)⁻¹) := by
  simp [expSeries]

theorem expSeries_toFormalMultilinearSeries_eq :
    expSeries.toFormalMultilinearSeries = NormedSpace.expSeries ℝ ℝ := by
  simp [toFormalMultilinearSeries]
  unfold NormedSpace.expSeries FormalMultilinearSeries.ofScalars
  simp [coeff, expSeries_get]

theorem expSeries_analytic : expSeries.analytic := by
  apply analytic_of_HasFPowerSeriesAt (f := Real.exp)
  rw [expSeries_toFormalMultilinearSeries_eq]
  convert NormedSpace.exp_hasFPowerSeriesAt_zero
  · exact Real.exp_eq_exp_ℝ
  · infer_instance

theorem expSeries_toFun : expSeries.toFun = Real.exp := by
  have := NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℝ) (𝔸 := ℝ)
  rw [← expSeries_toFormalMultilinearSeries_eq, ← Real.exp_eq_exp_ℝ] at this
  ext x
  simp [toFun]
  conv => rhs; rw [show x = 0 + x by simp]
  symm
  exact HasFPowerSeriesOnBall.sum this (by simp)

-- we assume that ms -> 0
-- noncomputable def exp {basis : Basis} (ms : PreMS basis) : PreMS basis :=
--   match basis with
--   | [] => Real.exp ms
--   | List.cons _ _ =>
--     expSeries.apply ms

-- -- we assume that leadingExp is negative
-- noncomputable def exp {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : PreMS (basis_hd :: basis_tl)) :
--     PreMS (basis_hd :: basis_tl) :=
--   expSeries.apply ms

-- we assume that leadingTerm is nonpositive, i.e. ms tendsto constant (maybe zero)
noncomputable def exp {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Real.exp ms
  | List.cons _ _ =>
    match destruct ms with
    | .none => PreMS.one _
    | .some ((exp, coef), tl) =>
      if exp < 0 then
        expSeries.apply ms
      else -- assume that exp = 0
        (expSeries.apply tl).mulMonomial coef.exp 0

theorem exp_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h : ms.WellOrdered)
    (h_nonpos : ¬ Term.FirstIsPos ms.leadingTerm.exps) :
    ms.exp.WellOrdered := by
  cases' basis with basis_hd basis_tl
  · apply WellOrdered.const
  cases' ms with exp coef tl
  · simpa [exp] using one_WellOrdered
  simp [PreMS.exp]
  split_ifs with h_if
  · apply apply_WellOrdered h
    simpa
  have h_exp : exp = 0 := by
    unfold leadingTerm at h_nonpos
    simp at h_nonpos
    contrapose! h_nonpos
    constructor
    simp at h_if
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
  cases' basis with basis_hd basis_tl
  · simp [exp, Approximates] at h_approx ⊢
    apply h_approx.mono
    simp
  cases' ms with exp coef tl
  · simp [exp]
    apply Approximates_nil at h_approx
    apply Approximates_of_EventuallyEq (f := fun _ ↦ 1)
    · apply h_approx.mono
      simp +contextual
    exact one_Approximates h_basis
  simp [PreMS.exp]
  split_ifs with h_if
  · rw [← expSeries_toFun]
    exact apply_Approximates expSeries_analytic h_basis h_wo (by simpa) h_approx
  have h_exp : exp = 0 := by
    unfold leadingTerm at h_nonpos
    simp at h_nonpos
    contrapose! h_nonpos
    constructor
    simp at h_if
    exact lt_of_le_of_ne h_if h_nonpos.symm
  subst h_exp
  clear h_if
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  obtain ⟨fC, h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
  simp at h_tl
  convert_to ((expSeries.apply tl).mulMonomial coef.exp 0).Approximates
      (fun t ↦ (Real.exp ∘ fC) t * basis_hd t ^ (0 : ℝ) * (Real.exp ∘ (fun s ↦ f s - fC s)) t)
  · ext t
    simp [← Real.exp_add]
  apply mulMonomial_Approximates h_basis
  · rw [← expSeries_toFun]
    exact apply_Approximates expSeries_analytic h_basis h_tl_wo h_comp h_tl
  apply exp_Approximates h_basis.tail h_coef_wo h_coef
  contrapose! h_nonpos
  exact Term.FirstIsPos_of_tail rfl h_nonpos

end PreMS

end TendstoTactic
