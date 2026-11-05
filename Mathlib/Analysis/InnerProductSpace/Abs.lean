/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Absolute value

This file defines the absolute value `|T| = √(T†∘T)` for continuous linear maps `T : E →L[ℂ] F`
between (potentially distinct) Hilbert spaces `E` and `F`.

## Implementation details

The absolute value `ContinuousLinearMap.abs T` is similar to `CFC.abs T` for a continuous linear
map `T : E →L[ℂ] E` acting on a Hilbert space `E`. They agree when `E = F`, see the theorem
`abs_eq_cfcAbs`. However, when `E ≠ F`, the adjoint is no longer a star operation and thus
`CFC.abs T` is no longer defined.

The absolute value `ContinuousLinearMap.abs T` is also known in the literature under the name
modulus. The name `ContinuousLinearMap.abs` has been chosen to be consistent with `CFC.abs` and
`Complex.abs`.

-/

public section

namespace ContinuousLinearMap

section Abs

open scoped NNReal InnerProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The abs `|T| = √(T†∘T)` of a continuous linear map `T : E →L[ℂ] F`. -/
@[expose]
protected noncomputable def abs (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T† ∘L T)

@[inherit_doc]
local notation "|" T "|" => ContinuousLinearMap.abs T

protected theorem abs_def (T : E →L[ℂ] F) : |T| = CFC.sqrt (T† ∘L T) := rfl

@[simp]
protected theorem abs_zero : |(0 : E →L[ℂ] F)| = 0 := by
  simp [ContinuousLinearMap.abs_def]

@[simp]
protected theorem abs_neg (T : E →L[ℂ] F) : |-T| = |T| := by
  simp [ContinuousLinearMap.abs_def]

protected theorem abs_sub_comm (S T : E →L[ℂ] F) : |S - T| = |T - S| := by
  rw [← neg_sub, ContinuousLinearMap.abs_neg]

@[simp]
protected theorem isPositive_abs (T : E →L[ℂ] F) : |T|.IsPositive := by
  simp [ContinuousLinearMap.abs_def, ← ContinuousLinearMap.nonneg_iff_isPositive]

@[simp]
protected theorem abs_abs (T : E →L[ℂ] F) : |(|T|)| = |T| := by
  rw [ContinuousLinearMap.abs_def, T.isPositive_abs.isSelfAdjoint.adjoint_eq]
  exact CFC.sqrt_mul_self ..

@[simp]
protected theorem adjoint_abs (T : E →L[ℂ] F) : |T|† = |T| := T.isPositive_abs.isSelfAdjoint

protected theorem continuous_abs : Continuous (ContinuousLinearMap.abs : (E →L[ℂ] F) → E →L[ℂ] E) :=
  CFC.continuousOn_sqrt.comp_continuous (by fun_prop)
    fun T => T.isPositive_adjoint_comp_self.nonneg

protected theorem abs_eq_cfcAbs (T : E →L[ℂ] E) : |T| = CFC.abs T := rfl

@[simp]
protected theorem abs_eq_zero {T : E →L[ℂ] F} : |T| = 0 ↔ T = 0 := by
  simp [ContinuousLinearMap.abs_def, CFC.sqrt_eq_zero_iff]

@[simp]
theorem abs_comp_abs (T : E →L[ℂ] F) : |T| ∘L |T| = T† ∘L T := by
  simp [ContinuousLinearMap.abs_def, ← mul_def, CFC.sqrt_mul_sqrt_self]

@[simp]
theorem norm_abs_apply (T : E →L[ℂ] F) (x : E) : ‖|T| x‖ = ‖T x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [apply_norm_sq_eq_inner_adjoint_left]

theorem ker_abs_eq_ker_adjoint_comp_self (T : E →L[ℂ] F) : |T|.ker = (T† ∘L T).ker := by
  simpa using (ker_adjoint_comp_self |T|).symm

@[simp]
theorem ker_abs_eq (T : E →L[ℂ] F) : |T|.ker = T.ker := by
  rw [ker_abs_eq_ker_adjoint_comp_self, ker_adjoint_comp_self]

@[simp]
protected theorem norm_abs (T : E →L[ℂ] F) : ‖|T|‖ = ‖T‖ := by
  simp_rw [norm_def |T|, norm_abs_apply, norm_def]

protected theorem abs_nnrpow_two (T : E →L[ℂ] F) : |T| ^ (2 : ℝ≥0) = T† ∘L T := by
  rw [CFC.nnrpow_two .., mul_def]
  exact abs_comp_abs T

protected theorem abs_nnrpow_two_mul (T : E →L[ℂ] F) (x : ℝ≥0) :
    |T| ^ (2 * x) = (T† ∘L T) ^ x := by
  rw [← CFC.nnrpow_nnrpow, ContinuousLinearMap.abs_nnrpow_two]

protected theorem abs_nnrpow (T : E →L[ℂ] F) (x : ℝ≥0) :
    |T| ^ x = (T† ∘L T) ^ (x / 2) := by
  simp [← ContinuousLinearMap.abs_nnrpow_two_mul, mul_div_left_comm]

theorem abs_of_isPositive {S : E →L[ℂ] E} (hS : S.IsPositive) : |S| = S := by
  rw [ContinuousLinearMap.abs_eq_cfcAbs]
  exact CFC.abs_of_nonneg ..

theorem abs_of_isPositive_neg {S : E →L[ℂ] E} (hS : (-S).IsPositive) : |S| = -S := by
  rw [ContinuousLinearMap.abs_eq_cfcAbs]
  exact CFC.abs_of_nonpos _ (neg_nonneg.mp hS.nonneg)

protected theorem abs_adjoint_comp_self (T : E →L[ℂ] F) : |T† ∘L T| = T† ∘L T :=
  abs_of_isPositive (isPositive_adjoint_comp_self T)

protected theorem abs_self_comp_adjoint (T : E →L[ℂ] F) : |T ∘L T†| = T ∘L T† :=
  abs_of_isPositive (isPositive_self_comp_adjoint T)

protected theorem abs_eq_self {S : E →L[ℂ] E} : |S| = S ↔ S.IsPositive :=
  ⟨fun h ↦ h ▸ S.isPositive_abs, fun h ↦ abs_of_isPositive h⟩

protected theorem abs_eq_self_neg {S : E →L[ℂ] E} : |S| = -S ↔ (-S).IsPositive :=
  ⟨fun h ↦ h ▸ S.isPositive_abs, fun h ↦ abs_of_isPositive_neg h⟩

@[simp]
protected theorem abs_id : |(.id ℂ E : E →L[ℂ] E)| = .id ℂ E :=
  abs_of_isPositive isPositive_one

@[simp]
protected theorem abs_one : |(1 : E →L[ℂ] E)| = 1 :=
  abs_of_isPositive isPositive_one

protected theorem abs_smul (c : ℂ) (T : E →L[ℂ] F) : |c • T| = ‖c‖ • |T| := by
  rw [ContinuousLinearMap.abs_def, CFC.sqrt_eq_iff _ _ (adjoint_comp_self_nonneg (c • T))]
  simp [mul_def, ← smul_assoc, Complex.mul_conj', map_smulₛₗ, sq]
  norm_cast

theorem abs_linearIsometry_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (U : F →ₗᵢ[ℂ] G) (T : E →L[ℂ] F) :
    |U.toContinuousLinearMap ∘L T| = |T| := by
  simp [ContinuousLinearMap.abs_def, comp_assoc, ← comp_assoc (U.toContinuousLinearMap†),
    (isometry_iff_adjoint_comp_self U.toContinuousLinearMap).mp U.isometry, one_def]

end Abs

end ContinuousLinearMap
