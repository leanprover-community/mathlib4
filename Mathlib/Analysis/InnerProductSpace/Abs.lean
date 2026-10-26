/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Absolute value

This file defines the absolute value `|T| = √(T†∘T)` for continuous linear maps `T : E →L[ℂ] F`
between (potentially distinct) Hilbert spaces `E` and `F`.

## Implementation details
The absolute value `ContinuousLinearMap.abs T` is similar to `CFC.abs T` for a continuous linear
map `T : E →L[ℂ] E` acting on a Hilbert space `E`. They agree when `E = F`, see the theorem
`abs_eq_abs`. However, when `E ≠ F`, the adjoint is no longer a star operation and thus
`CFC.abs T` is no longer defined.

The absolute value `ContinuousLinearMap.abs T` is also known in the literature under the name
modulus. The name `ContinuousLinearMap.abs` has been chosen to be consistent with `CFC.abs` and
`Complex.abs`.

-/

public noncomputable section

namespace ContinuousLinearMap

section Abs

open scoped ENNReal NNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The abs `|T| = √(T†∘T)` of a continuous linear map `T : E →L[ℂ] F`. -/
@[expose]
def abs (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T.adjoint ∘L T)

@[inherit_doc]
local notation "|" T "|" => abs T

theorem abs_apply (T : E →L[ℂ] F) : |T| = CFC.sqrt (T.adjoint ∘L T) := rfl

@[simp] theorem abs_zero : |(0 : E →L[ℂ] F)| = 0 := by simp [abs]
@[simp] theorem abs_neg (T : E →L[ℂ] F) : |-T| = |T| := by simp [abs]
@[simp] theorem abs_nonneg (T : E →L[ℂ] F) : 0 ≤ |T| := by simp [abs]
@[simp] theorem abs_abs (T : E →L[ℂ] F) : |(|T|)| = |T| := by
  rw [abs, T.abs_nonneg.isSelfAdjoint.adjoint_eq]
  exact CFC.sqrt_mul_self |T|

theorem abs_eq_cfcAbs (T : E →L[ℂ] E) : |T| = CFC.abs T := rfl

@[simp]
theorem adjoint_comp_self_nonneg (T : E →L[ℂ] F) : 0 ≤ T.adjoint ∘L T :=
    nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T)

theorem abs_eq_zero (T : E →L[ℂ] F) : |T| = 0 ↔ T = 0 := by
  simp [abs, CFC.sqrt_eq_zero_iff, adjoint_comp_self_eq_zero_iff]

theorem abs_comp_abs (T : E →L[ℂ] F) : |T| ∘L |T| = T.adjoint ∘L T := by
  simp [abs, ← mul_def, CFC.sqrt_mul_sqrt_self]

theorem norm_abs_apply (T : E →L[ℂ] F) (x : E) : ‖|T| x‖ = ‖T x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp_rw [apply_norm_sq_eq_inner_adjoint_left, ContinuousLinearMap.comp_apply]
  rw [T.abs_nonneg.isSelfAdjoint.adjoint_eq]
  simp [abs, ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self, ContinuousLinearMap.comp_apply]

theorem ker_abs_eq (T : E →L[ℂ] F) : |T|.ker = T.ker := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero (a := T.toLinearMap x),
    ← norm_eq_zero (a := |T|.toLinearMap x)]
  simp [norm_abs_apply]

@[simp]
theorem norm_abs (T : E →L[ℂ] F) : ‖|T|‖ = ‖T‖ := by
  simp_rw [norm_def |T|, norm_abs_apply, norm_def]

theorem abs_nnrpow_two (T : E →L[ℂ] F) : |T| ^ (2 : ℝ≥0) = T.adjoint ∘L T := by
  rw [CFC.nnrpow_two _ T.abs_nonneg, ContinuousLinearMap.mul_def]
  exact abs_comp_abs T

theorem abs_nnrpow_two_mul (T : E →L[ℂ] F) (x : ℝ≥0) :
    |T| ^ (2 * x) = (T.adjoint ∘L T) ^ x := by
  rw [← CFC.nnrpow_nnrpow, abs_nnrpow_two]

theorem abs_nnrpow (T : E →L[ℂ] F) (x : ℝ≥0) :
    |T| ^ x = (T.adjoint ∘L T) ^ (x / 2) := by
  simp [← abs_nnrpow_two_mul, mul_div_left_comm]

theorem abs_of_nonneg (S : E →L[ℂ] E) (hS : 0 ≤ S := by cfc_tac) : |S| = S := by
  rw [abs_eq_cfcAbs]
  exact CFC.abs_of_nonneg _ hS

theorem abs_of_nonpos (S : E →L[ℂ] E) (hS : S ≤ 0 := by cfc_tac) : |S| = -S := by
  rw [abs_eq_cfcAbs]
  exact CFC.abs_of_nonpos _ hS

theorem abs_adjoint_comp_self (T : E →L[ℂ] F) : |T.adjoint ∘L T| = |T| ∘L |T| := by
  rw [abs_comp_abs]
  exact abs_of_nonneg _

theorem abs_smul (c : ℂ) (T : E →L[ℂ] F) : |c • T| = ‖c‖ • |T| := by
  rw [abs, CFC.sqrt_eq_iff _ _ (nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self (c • T)))
    (smul_nonneg (norm_nonneg c) T.abs_nonneg), smul_mul_smul_comm, mul_def, abs_comp_abs]
  simp [LinearIsometryEquiv.map_smulₛₗ, ← smul_assoc, Complex.mul_conj', ← sq]
  norm_cast

end Abs

end ContinuousLinearMap
