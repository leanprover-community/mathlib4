/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! # The basic continuous linear maps associated to `ℂ`

The continuous linear maps `Complex.reCLM` (real part), `Complex.imCLM` (imaginary part),
`Complex.conjCLE` (conjugation), and `Complex.ofRealCLM` (inclusion of `ℝ`) were introduced in
`Analysis.Complex.Basic`. This file contains a few calculations requiring more imports:
the operator norm and (for `Complex.conjCLE`) the determinant.
-/

public section

open ContinuousLinearMap

namespace Complex

/-- The determinant of `conjLIE`, as a linear map. -/
@[simp]
theorem det_conjLIE : LinearMap.det (conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 :=
  det_conjAe

/-- The determinant of `conjLIE`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjLIE : LinearEquiv.det conjLIE.toLinearEquiv = -1 :=
  linearEquiv_det_conjAe

@[simp]
theorem reCLM_norm : ‖reCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖reCLM 1‖ := by simp
      _ ≤ ‖reCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
theorem reCLM_enorm : ‖reCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
theorem reCLM_nnnorm : ‖reCLM‖₊ = 1 :=
  Subtype.ext reCLM_norm

@[simp]
theorem imCLM_norm : ‖imCLM‖ = 1 :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) <|
    calc
      1 = ‖imCLM I‖ := by simp
      _ ≤ ‖imCLM‖ := unit_le_opNorm _ _ (by simp)

@[simp]
theorem imCLM_enorm : ‖imCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
theorem imCLM_nnnorm : ‖imCLM‖₊ = 1 :=
  Subtype.ext imCLM_norm

@[simp]
theorem conjCLE_norm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ = 1 :=
  conjLIE.toLinearIsometry.norm_toContinuousLinearMap

@[simp]
theorem conjCLE_enorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
theorem conjCLE_nnorm : ‖(conjCLE : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
  Subtype.ext conjCLE_norm

@[simp]
theorem ofRealCLM_norm : ‖ofRealCLM‖ = 1 :=
  ofRealLI.norm_toContinuousLinearMap

@[simp]
theorem ofRealCLM_enorm : ‖ofRealCLM‖ₑ = 1 := by simp [← ofReal_norm]

@[simp]
theorem ofRealCLM_nnnorm : ‖ofRealCLM‖₊ = 1 :=
  Subtype.ext <| ofRealCLM_norm

end Complex
