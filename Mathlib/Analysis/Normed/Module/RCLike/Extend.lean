/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Norm properties of the extension of continuous `ℝ`-linear functionals to `𝕜`-linear functionals

This file shows that `StrongDual.extendRCLike` preserves the norm of the functional.
-/

public section

open RCLike ContinuousLinearMap
open scoped ComplexConjugate

namespace StrongDual


variable {𝕜 F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The norm of the extension is bounded by `‖fr‖`. -/
theorem norm_extendRCLike_bound (fr : StrongDual ℝ F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ := by
  set lm : StrongDual 𝕜 F := fr.extendRCLike
  by_cases h : lm x = 0
  · rw [h, norm_zero]
    positivity
  rw [← mul_le_mul_iff_right₀ (norm_pos_iff.2 h), ← sq]
  calc
    ‖lm x‖ ^ 2 = fr (conj (lm x : 𝕜) • x) := Module.Dual.norm_extendRCLike_apply_sq fr.toLinearMap x
    _ ≤ ‖fr (conj (lm x : 𝕜) • x)‖ := le_abs_self _
    _ ≤ ‖fr‖ * ‖conj (lm x : 𝕜) • x‖ := le_opNorm _ _
    _ = ‖(lm x : 𝕜)‖ * (‖fr‖ * ‖x‖) := by rw [norm_smul, norm_conj, mul_left_comm]

@[simp]
theorem norm_extendRCLike (fr : StrongDual ℝ F) : ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ = ‖fr‖ :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendRCLike_bound) <|
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendRCLike x : 𝕜)‖ := by simp
        _ ≤ ‖(fr.extendRCLike x : 𝕜)‖ := abs_re_le_norm _
        _ ≤ ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ * ‖x‖ := le_opNorm _ _

/-- `StrongDual.extendRCLike` bundled into a linear isometry equivalence. -/
@[expose, simps! -isSimp apply symm_apply]
noncomputable def extendRCLikeₗᵢ : StrongDual ℝ F ≃ₗᵢ[ℝ] StrongDual 𝕜 F where
  toLinearEquiv := StrongDual.extendRCLikeₗ
  norm_map' := norm_extendRCLike

end StrongDual

namespace ContinuousLinearMap
open StrongDual

@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_bound := norm_extendRCLike_bound
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜' := norm_extendRCLike
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜 := norm_extendRCLike

end ContinuousLinearMap
