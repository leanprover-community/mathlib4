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

set_option linter.flexible false
set_option linter.style.longLine false

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
  simp only [LazySeries.toFun]
  conv_rhs => rw [show x = 0 + x by simp]
  symm
  exact HasFPowerSeriesOnBall.sum this (by simp)

mutual

/-- If `ms` approximates an eventually bounded function `f` and,
then `ms.exp` approximates `Real.exp ∘ f`. -/
noncomputable def SeqMS.exp {basis_hd : ℝ → ℝ} {basis_tl : Basis} (ms : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  match ms.destruct with
  | .none => SeqMS.one
  | .some (exp, coef, tl) =>
    if exp < 0 then
      ms.apply expSeries
    else -- assume that exp = 0
      (tl.apply expSeries).mulMonomial coef.exp 0

/-- If `ms` approximates an eventually bounded function `f` and,
then `ms.exp` approximates `Real.exp ∘ f`. -/
noncomputable def exp {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  match basis with
  | [] => Real.exp ms.toReal
  | List.cons _ _ =>
    mk (SeqMS.exp ms.seq) (Real.exp ∘ ms.toFun)

end

@[simp]
theorem exp_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    ms.exp.seq = SeqMS.exp ms.seq := by
  simp [exp]

@[simp]
theorem exp_toFun {basis : Basis} {ms : PreMS basis} :
    ms.exp.toFun = Real.exp ∘ ms.toFun := by
  ext t
  cases basis with
  | nil => simp [exp, toReal]
  | cons => simp [exp]

mutual

theorem SeqMS.exp_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : ms.WellOrdered)
    (h_nonpos : ¬ Term.FirstIsPos ms.exps) :
    ms.exp.WellOrdered := by
  cases ms with
  | nil => simpa [SeqMS.exp] using SeqMS.one_WellOrdered
  | cons exp coef tl =>
  simp [SeqMS.exp, SeqMS.destruct_cons]
  split_ifs with h_if
  · apply SeqMS.apply_WellOrdered h
    simpa
  have h_exp : exp = 0 := by
    contrapose! h_nonpos
    simp
    constructor
    grind
  subst h_exp
  clear h_if
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h
  apply SeqMS.mulMonomial_WellOrdered
  · exact SeqMS.apply_WellOrdered h_tl_wo h_comp
  · apply exp_WellOrdered h_coef_wo
    contrapose! h_nonpos
    simp
    exact Term.FirstIsPos_of_tail rfl h_nonpos

theorem exp_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h : ms.WellOrdered)
    (h_nonpos : ¬ Term.FirstIsPos ms.exps) :
    ms.exp.WellOrdered := by
  cases basis with
  | nil => apply WellOrdered.const
  | cons basis_hd basis_tl =>
    simp at *
    apply SeqMS.exp_WellOrdered h h_nonpos

end

theorem exp_Approximates {basis : Basis} {ms : PreMS basis}
    (h_basis : WellFormedBasis basis)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates)
    (h_nonpos : ¬ Term.FirstIsPos ms.exps) :
    ms.exp.Approximates := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp
  cases ms with
  | nil f =>
    simp [exp, SeqMS.exp, SeqMS.destruct_nil]
    apply Approximates_nil at h_approx
    convert replaceFun_Approximates _ (one_Approximates h_basis)
    · ext g
      simp [ms_eq_ms_iff_mk_eq_mk]
    · apply h_approx.mono
      simp +contextual
  | cons exp coef tl f =>
  simp [PreMS.exp, SeqMS.exp, SeqMS.destruct_cons]
  split_ifs with h_if
  · rw [← expSeries_toFun]
    exact apply_Approximates expSeries_analytic h_basis (by simpa) h_wo h_approx
  have h_exp : exp = 0 := by
    contrapose! h_nonpos
    simp
    constructor
    grind
  subst h_exp
  clear h_if
  obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons h_wo
  obtain ⟨h_coef, h_majorated, h_tl⟩ := Approximates_cons h_approx
  let ms := ((mk tl (f - basis_hd ^ 0 * coef.toFun)).apply expSeries).mulMonomial coef.exp 0
  have h : ms.Approximates := by
    simp [ms]
    apply mulMonomial_Approximates h_basis
    · apply apply_Approximates expSeries_analytic h_basis (by simpa) (by simpa)
      convert h_tl
      simp
    · apply exp_Approximates h_basis.tail h_coef_wo h_coef
      contrapose! h_nonpos
      simp
      exact Term.FirstIsPos_of_tail rfl h_nonpos
  apply replaceFun_Approximates _ h
  simp [ms, expSeries_toFun]
  apply EventuallyEq.of_eq
  ext t
  simp [← Real.exp_add]

-- theorem exp_Approximates_pow_of_pos
--     {basis1 basis2 : Basis} {ms1 : PreMS basis1} {ms2 : PreMS basis2}
--     {f g : ℝ → ℝ}
--     (h_basis1 : WellFormedBasis basis1)
--     (h_wo1 : ms1.WellOrdered) (h_approx1 : ms1.Approximates f) (h_trimmed1 : ms1.Trimmed)
--     (h_pos1 : 0 < ms1.leadingTerm.coef)
--     (h_approx2 : ms2.Approximates (Real.exp ∘ ((Real.log ∘ f) * g))) :
--     ms2.Approximates (fun x ↦ (f x) ^ (g x)) := by
--   apply Approximates_of_EventuallyEq _ h_approx2
--   have hf_pos : ∀ᶠ t in atTop, 0 < f t :=
--     eventually_pos_of_coef_pos h_pos1 h_wo1 h_approx1 h_trimmed1 h_basis1
--   apply hf_pos.mono
--   intro x hx
--   simp [Real.rpow_def_of_pos hx]

end PreMS

end ComputeAsymptotics
