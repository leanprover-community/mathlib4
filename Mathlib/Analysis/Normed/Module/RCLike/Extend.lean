/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Norm properties of the extension of continuous `ℝ`-linear functionals to `𝕜`-linear functionals

This file shows that `ContinuousLinearMap.extendTo𝕜` preserves the norm of the functional.
-/

public section

open RCLike
open scoped ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

section ScalarTower

variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The norm of the extension is bounded by `‖fr‖`. -/
theorem norm_extendTo𝕜'_bound (fr : StrongDual ℝ F) (x : F) :
    ‖(fr.extendTo𝕜' x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ := by
  set lm : F →L[𝕜] 𝕜 := fr.extendTo𝕜'
  by_cases h : lm x = 0
  · rw [h, norm_zero]
    positivity
  rw [← mul_le_mul_iff_right₀ (norm_pos_iff.2 h), ← sq]
  calc
    ‖lm x‖ ^ 2 = fr (conj (lm x : 𝕜) • x) := fr.toLinearMap.norm_extendTo𝕜'_apply_sq x
    _ ≤ ‖fr (conj (lm x : 𝕜) • x)‖ := le_abs_self _
    _ ≤ ‖fr‖ * ‖conj (lm x : 𝕜) • x‖ := le_opNorm _ _
    _ = ‖(lm x : 𝕜)‖ * (‖fr‖ * ‖x‖) := by rw [norm_smul, norm_conj, mul_left_comm]

@[simp]
theorem norm_extendTo𝕜' (fr : StrongDual ℝ F) : ‖(fr.extendTo𝕜' : StrongDual 𝕜 F)‖ = ‖fr‖ :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendTo𝕜'_bound) <|
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendTo𝕜' x : 𝕜)‖ := congr_arg norm (fr.extendTo𝕜'_apply_re x).symm
        _ ≤ ‖(fr.extendTo𝕜' x : 𝕜)‖ := abs_re_le_norm _
        _ ≤ ‖(fr.extendTo𝕜' : StrongDual 𝕜 F)‖ * ‖x‖ := le_opNorm _ _

end ScalarTower

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem norm_extendTo𝕜 (fr : StrongDual ℝ (RestrictScalars ℝ 𝕜 F)) :
    ‖fr.extendTo𝕜‖ = ‖fr‖ :=
  fr.norm_extendTo𝕜'

end ContinuousLinearMap
