/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Absolute value

This file defines the absolute value `|T| = √(T†∘T)` for continuous linear maps `T : E →L[ℂ] F`
between (potentially distinct) Hilbert spaces `E` and `F`.

## Implementation notes

The absolute value `ContinuousLinearMap.abs T` is similar to `CFC.abs T` for a continuous linear
map `T : E →L[ℂ] E` acting on a Hilbert space `E`. They agree when `E = F`, see the theorem
`abs_eq_cfcAbs`. However, when `E ≠ F`, the adjoint is no longer a star operation and thus
`CFC.abs T` is no longer defined.

The absolute value `ContinuousLinearMap.abs T` is also known in the literature under the name
modulus. The name `ContinuousLinearMap.abs` has been chosen to be consistent with `CFC.abs` and
`Complex.abs`.

## TODO:
   - generalize from `T : E →L[ℂ] F` to `T : E →L[𝕜] F` once CFC becomes available for the latter.

-/

public section

namespace ContinuousLinearMap

section Abs

open scoped NNReal InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The absolute value `|T| = √(T†∘T)` of a continuous linear map `T : E →L[ℂ] F`. -/
@[expose]
protected noncomputable def abs (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T† ∘L T)

protected theorem abs_def (T : E →L[ℂ] F) : T.abs = CFC.sqrt (T† ∘L T) := rfl

@[simp]
protected theorem abs_zero : (0 : E →L[ℂ] F).abs = 0 := by
  simp [ContinuousLinearMap.abs_def]

@[simp]
protected theorem abs_neg (T : E →L[ℂ] F) : (-T).abs = T.abs := by
  simp [ContinuousLinearMap.abs_def]

protected theorem abs_sub_comm (S T : E →L[ℂ] F) : (S - T).abs = (T - S).abs := by
  rw [← neg_sub, ContinuousLinearMap.abs_neg]

@[simp]
theorem isPositive_abs (T : E →L[ℂ] F) : T.abs.IsPositive := by
  simp [ContinuousLinearMap.abs_def, ← ContinuousLinearMap.nonneg_iff_isPositive]

@[simp]
theorem isSelfAdjoint_abs (T : E →L[ℂ] F) : IsSelfAdjoint T.abs := T.isPositive_abs.isSelfAdjoint

@[simp]
protected theorem abs_abs (T : E →L[ℂ] F) : T.abs.abs = T.abs := by
  rw [ContinuousLinearMap.abs_def, T.isPositive_abs.isSelfAdjoint.adjoint_eq]
  exact CFC.sqrt_mul_self ..

@[simp]
theorem adjoint_abs (T : E →L[ℂ] F) : T.abs† = T.abs := T.isPositive_abs.isSelfAdjoint

@[fun_prop]
protected theorem continuous_abs : Continuous (ContinuousLinearMap.abs : (E →L[ℂ] F) → E →L[ℂ] E) :=
  CFC.continuousOn_sqrt.comp_continuous (by fun_prop)
    fun T => T.isPositive_adjoint_comp_self.nonneg

theorem abs_eq_cfcAbs (T : E →L[ℂ] E) : T.abs = CFC.abs T := rfl

@[simp]
protected theorem abs_eq_zero {T : E →L[ℂ] F} : T.abs = 0 ↔ T = 0 := by
  simp [ContinuousLinearMap.abs_def,
    CFC.sqrt_eq_zero_iff _ T.isPositive_adjoint_comp_self.nonneg]

@[simp]
theorem abs_comp_abs (T : E →L[ℂ] F) : T.abs ∘L T.abs = T† ∘L T := by
  simp [ContinuousLinearMap.abs_def, ← mul_def,
    CFC.sqrt_mul_sqrt_self _ T.isPositive_adjoint_comp_self.nonneg]

@[simp]
theorem norm_abs_apply (T : E →L[ℂ] F) (x : E) : ‖T.abs x‖ = ‖T x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [apply_norm_sq_eq_inner_adjoint_left]

@[simp]
theorem ker_abs (T : E →L[ℂ] F) : T.abs.ker = T.ker := by
  simp [← ker_adjoint_comp_self]

@[simp]
protected theorem norm_abs (T : E →L[ℂ] F) : ‖T.abs‖ = ‖T‖ := by
  simp_rw [norm_def T.abs, norm_abs_apply, norm_def]

protected theorem abs_nnrpow_two (T : E →L[ℂ] F) : T.abs ^ (2 : ℝ≥0) = T† ∘L T := by
  rw [CFC.nnrpow_two .., mul_def]
  exact abs_comp_abs T

protected theorem abs_nnrpow_two_mul (T : E →L[ℂ] F) (x : ℝ≥0) :
    T.abs ^ (2 * x) = (T† ∘L T) ^ x := by
  rw [← CFC.nnrpow_nnrpow, ContinuousLinearMap.abs_nnrpow_two]

protected theorem abs_nnrpow (T : E →L[ℂ] F) (x : ℝ≥0) :
    T.abs ^ x = (T† ∘L T) ^ (x / 2) := by
  simp [← ContinuousLinearMap.abs_nnrpow_two_mul, mul_div_left_comm]

protected theorem abs_pow_two (T : E →L[ℂ] F) : T.abs ^ 2 = T† ∘L T := by
  rw [sq, mul_def, abs_comp_abs]

protected theorem abs_pow_two_mul (T : E →L[ℂ] F) (n : ℕ) :
    T.abs ^ (2 * n) = (T† ∘L T) ^ n := by
  rw [pow_mul, ContinuousLinearMap.abs_pow_two]

protected theorem IsPositive.abs_eq_self {S : E →L[ℂ] E} (hS : S.IsPositive) : S.abs = S := by
  rw [ContinuousLinearMap.abs_eq_cfcAbs]
  exact CFC.abs_of_nonneg ..

theorem IsPositive.abs_eq_neg_self {S : E →L[ℂ] E} (hS : (-S).IsPositive) : S.abs = -S := by
  rw [ContinuousLinearMap.abs_eq_cfcAbs]
  exact CFC.abs_of_nonpos _ (neg_nonneg.mp hS.nonneg)

@[simp]
theorem abs_adjoint_comp_self (T : E →L[ℂ] F) : (T† ∘L T).abs = T† ∘L T :=
  (isPositive_adjoint_comp_self T).abs_eq_self

@[simp]
theorem abs_self_comp_adjoint (T : E →L[ℂ] F) : (T ∘L T†).abs = T ∘L T† :=
  (isPositive_self_comp_adjoint T).abs_eq_self

protected theorem abs_eq_self {S : E →L[ℂ] E} : S.abs = S ↔ S.IsPositive :=
  ⟨fun h ↦ h ▸ S.isPositive_abs, fun h ↦ h.abs_eq_self⟩

protected theorem abs_eq_neg_self {S : E →L[ℂ] E} : S.abs = -S ↔ (-S).IsPositive :=
  ⟨fun h ↦ h ▸ S.isPositive_abs, fun h ↦ h.abs_eq_neg_self⟩

@[simp]
theorem abs_id : (ContinuousLinearMap.id ℂ E).abs = .id ℂ E :=
  isPositive_one.abs_eq_self

@[simp]
protected theorem abs_one : (1 : E →L[ℂ] E).abs = 1 :=
  isPositive_one.abs_eq_self

protected theorem abs_smul {𝕜 : Type*} [RCLike 𝕜] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
    [NormedAlgebra 𝕜 ℂ] [IsScalarTower 𝕜 ℂ F] (c : 𝕜) (T : E →L[ℂ] F) :
    (c • T).abs = ‖c‖ • T.abs := by
  rw [ContinuousLinearMap.abs_def, CFC.sqrt_eq_iff .., ← algebraMap_smul ℂ c T]
  simp [mul_def, ← smul_assoc, Complex.mul_conj', map_smulₛₗ, sq, -algebraMap_smul]
  norm_cast

@[simp]
theorem abs_linearIsometry_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (U : F →ₗᵢ[ℂ] G) (T : E →L[ℂ] F) :
    (U.toContinuousLinearMap ∘L T).abs = T.abs := by
  simp [ContinuousLinearMap.abs_def, comp_assoc, ← comp_assoc (U.toContinuousLinearMap†),
    (isometry_iff_adjoint_comp_self U.toContinuousLinearMap).mp U.isometry, one_def]

end Abs

end ContinuousLinearMap
