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
# Modulus

This file defines the modulus `|T| = √(T†∘T)` for continuous linear maps `T : E →L[ℂ] F` between
(potentially distinct) Hilbert spaces `E` and `F`.

## Implementation details
The modulus is similar to `CFC.abs T` for a continuous linear map
`T : E →L[ℂ] E` acting on a Hilbert space `E`. They agree when `E = F`, see the theorem
`modulus_eq_abs`. However, when `E ≠ F`, the adjoint is no longer a star operation and thus
`CFC.abs T` is no longer defined.

-/

public noncomputable section

namespace ContinuousLinearMap

section Modulus

open scoped ENNReal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The modulus `|T| = √(T†∘T)` of a continuous linear map `T : E →L[ℂ] F`. -/
def modulus (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T.adjoint ∘L T)

@[inherit_doc]
scoped notation "|" T "|" => modulus T

@[simp] theorem modulus_zero : |(0 : E →L[ℂ] F)| = 0 := by simp [modulus]
@[simp] theorem modulus_neg (T : E →L[ℂ] F) : |-T| = |T| := by simp [modulus]
@[simp] theorem modulus_nonneg (T : E →L[ℂ] F) : 0 ≤ |T| := by simp [modulus]
@[simp] theorem modulus_modulus (T : E →L[ℂ] F) : |(|T|)| = |T| := by
  rw [modulus, T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  exact CFC.sqrt_mul_self |T|

theorem modulus_eq_abs (T : E →L[ℂ] E) : |T| = CFC.abs T := by rfl

theorem modulus_eq_zero (T : E →L[ℂ] F) : |T| = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simp only [modulus] at h
  rw [CFC.sqrt_eq_zero_iff (adjoint T ∘SL T)
    (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))] at h
  exact adjoint_comp_self_eq_zero_iff.mp h

theorem modulus_comp_modulus (T : E →L[ℂ] F) :
    |T| ∘L |T| = T.adjoint ∘L T := by
  simpa [modulus, ← ContinuousLinearMap.mul_def] using
    CFC.sqrt_mul_sqrt_self (adjoint T ∘L T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))

theorem norm_modulus_apply (T : E →L[ℂ] F) (x : E) : ‖|T| x‖ = ‖T x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp_rw [apply_norm_sq_eq_inner_adjoint_left, ContinuousLinearMap.comp_apply]
  rw [T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  simp [modulus, ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self (adjoint T ∘SL T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T)),
    ContinuousLinearMap.comp_apply]

theorem ker_modulus_eq (T : E →L[ℂ] F) : |T|.ker = T.ker := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero (a := T.toLinearMap x),
    ← norm_eq_zero (a := |T|.toLinearMap x)]
  simp [norm_modulus_apply]

end Modulus

end ContinuousLinearMap
