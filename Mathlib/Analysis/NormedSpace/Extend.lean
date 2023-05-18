/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde

! This file was ported from Lean 3 source module analysis.normed_space.extend
! leanprover-community/mathlib commit 3f655f5297b030a87d641ad4e825af8d9679eb0b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Data.IsROrC.Basic

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

## Main definitions

* `linear_map.extend_to_𝕜`
* `continuous_linear_map.extend_to_𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars ℝ 𝕜 F`.
Alternate forms which operate on `[is_scalar_tower ℝ 𝕜 F]` instead are provided with a primed name.

-/


open IsROrC

open ComplexConjugate

variable {𝕜 : Type _} [IsROrC 𝕜] {F : Type _} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace LinearMap

variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `‖fr‖` if `fr` is continuous. -/
noncomputable def extendTo𝕜' (fr : F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  by
  let fc : F → 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add : ∀ x y : F, fc (x + y) = fc x + fc y :=
    by
    intro x y
    simp only [fc]
    simp only [smul_add, LinearMap.map_add, of_real_add]
    rw [mul_add]
    abel
  have A : ∀ (c : ℝ) (x : F), (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) :=
    by
    intro c x
    rw [← of_real_mul]
    congr 1
    rw [IsROrC.ofReal_alg, smul_assoc, fr.map_smul, Algebra.id.smul_eq_mul, one_smul]
  have smul_ℝ : ∀ (c : ℝ) (x : F), fc ((c : 𝕜) • x) = (c : 𝕜) * fc x :=
    by
    intro c x
    simp only [fc, A]
    rw [A c x]
    rw [smul_smul, mul_comm I (c : 𝕜), ← smul_smul, A, mul_sub]
    ring
  have smul_I : ∀ x : F, fc ((I : 𝕜) • x) = (I : 𝕜) * fc x :=
    by
    intro x
    simp only [fc]
    cases' @I_mul_I_ax 𝕜 _ with h h
    · simp [h]
    rw [mul_sub, ← mul_assoc, smul_smul, h]
    simp only [neg_mul, LinearMap.map_neg, one_mul, one_smul, mul_neg, of_real_neg, neg_smul,
      sub_neg_eq_add, add_comm]
  have smul_𝕜 : ∀ (c : 𝕜) (x : F), fc (c • x) = c • fc x :=
    by
    intro c x
    rw [← re_add_im c, add_smul, add_smul, add, smul_ℝ, ← smul_smul, smul_ℝ, smul_I, ← mul_assoc]
    rfl
  exact
    { toFun := fc
      map_add' := add
      map_smul' := smul_𝕜 }
#align linear_map.extend_to_𝕜' LinearMap.extendTo𝕜'

theorem extendTo𝕜'_apply (fr : F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x) :=
  rfl
#align linear_map.extend_to_𝕜'_apply LinearMap.extendTo𝕜'_apply

@[simp]
theorem extendTo𝕜'_apply_re (fr : F →ₗ[ℝ] ℝ) (x : F) : re (fr.extendTo𝕜' x : 𝕜) = fr x := by
  simp only [extend_to_𝕜'_apply, map_sub, MulZeroClass.zero_mul, MulZeroClass.mul_zero, sub_zero,
    is_R_or_C_simps]
#align linear_map.extend_to_𝕜'_apply_re LinearMap.extendTo𝕜'_apply_re

theorem norm_extendTo𝕜'_apply_sq (f : F →ₗ[ℝ] ℝ) (x : F) :
    ‖(f.extendTo𝕜' x : 𝕜)‖ ^ 2 = f (conj (f.extendTo𝕜' x : 𝕜) • x) :=
  calc
    ‖(f.extendTo𝕜' x : 𝕜)‖ ^ 2 = re (conj (f.extendTo𝕜' x) * f.extendTo𝕜' x : 𝕜) := by
      rw [IsROrC.conj_mul, norm_sq_eq_def', of_real_re]
    _ = f (conj (f.extendTo𝕜' x : 𝕜) • x) := by
      rw [← smul_eq_mul, ← map_smul, extend_to_𝕜'_apply_re]
    
#align linear_map.norm_extend_to_𝕜'_apply_sq LinearMap.norm_extendTo𝕜'_apply_sq

end LinearMap

namespace ContinuousLinearMap

variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The norm of the extension is bounded by `‖fr‖`. -/
theorem norm_extendTo𝕜'_bound (fr : F →L[ℝ] ℝ) (x : F) :
    ‖(fr.toLinearMap.extendTo𝕜' x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ :=
  by
  set lm : F →ₗ[𝕜] 𝕜 := fr.to_linear_map.extend_to_𝕜'
  classical
    by_cases h : lm x = 0
    · rw [h, norm_zero]
      apply mul_nonneg <;> exact norm_nonneg _
    rw [← mul_le_mul_left (norm_pos_iff.2 h), ← sq]
    calc
      ‖lm x‖ ^ 2 = fr (conj (lm x : 𝕜) • x) := fr.to_linear_map.norm_extend_to_𝕜'_apply_sq x
      _ ≤ ‖fr (conj (lm x : 𝕜) • x)‖ := (le_abs_self _)
      _ ≤ ‖fr‖ * ‖conj (lm x : 𝕜) • x‖ := (le_op_norm _ _)
      _ = ‖(lm x : 𝕜)‖ * (‖fr‖ * ‖x‖) := by rw [norm_smul, norm_conj, mul_left_comm]
      
#align continuous_linear_map.norm_extend_to_𝕜'_bound ContinuousLinearMap.norm_extendTo𝕜'_bound

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def extendTo𝕜' (fr : F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous _ ‖fr‖ fr.norm_extendTo𝕜'_bound
#align continuous_linear_map.extend_to_𝕜' ContinuousLinearMap.extendTo𝕜'

theorem extendTo𝕜'_apply (fr : F →L[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜' x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x) :=
  rfl
#align continuous_linear_map.extend_to_𝕜'_apply ContinuousLinearMap.extendTo𝕜'_apply

@[simp]
theorem norm_extendTo𝕜' (fr : F →L[ℝ] ℝ) : ‖(fr.extendTo𝕜' : F →L[𝕜] 𝕜)‖ = ‖fr‖ :=
  le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) <|
    op_norm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendTo𝕜' x : 𝕜)‖ := congr_arg norm (fr.extendTo𝕜'_apply_re x).symm
        _ ≤ ‖(fr.extendTo𝕜' x : 𝕜)‖ := (abs_re_le_norm _)
        _ ≤ ‖(fr.extendTo𝕜' : F →L[𝕜] 𝕜)‖ * ‖x‖ := le_op_norm _ _
        
#align continuous_linear_map.norm_extend_to_𝕜' ContinuousLinearMap.norm_extendTo𝕜'

end ContinuousLinearMap

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜`. -/
noncomputable def LinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  fr.extendTo𝕜'
#align linear_map.extend_to_𝕜 LinearMap.extendTo𝕜

theorem LinearMap.extendTo𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x : _) :=
  rfl
#align linear_map.extend_to_𝕜_apply LinearMap.extendTo𝕜_apply

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  fr.extendTo𝕜'
#align continuous_linear_map.extend_to_𝕜 ContinuousLinearMap.extendTo𝕜

theorem ContinuousLinearMap.extendTo𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) (x : F) :
    fr.extendTo𝕜 x = (fr x : 𝕜) - (i : 𝕜) * fr ((i : 𝕜) • x : _) :=
  rfl
#align continuous_linear_map.extend_to_𝕜_apply ContinuousLinearMap.extendTo𝕜_apply

@[simp]
theorem ContinuousLinearMap.norm_extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) :
    ‖fr.extendTo𝕜‖ = ‖fr‖ :=
  fr.norm_extendTo𝕜'
#align continuous_linear_map.norm_extend_to_𝕜 ContinuousLinearMap.norm_extendTo𝕜

