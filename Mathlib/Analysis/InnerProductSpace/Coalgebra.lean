/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Finite-dimensional inner product space with a (co)algebra structure

This file proves that a finite-dimensional inner product space has an algebra
structure if it has a coalgebra structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`,
`(1 : A) = (adjoint counit) (1 : 𝕜)` and `algebraMap = adjoint counit`.

## TODO:

* When `NormedAddCommGroup` becomes unbundled
  (so that we can have `Ring` along with a `NormedAddCommGroup`),
  prove that a finite-dimensional inner product space with an algebra structure gives rise
  to a coalgebra, where `comul = adjoint (mul' 𝕜 A)` and `counit = adjoint (Algebra.linearMap 𝕜 A)`.
-/

variable {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  [FiniteDimensional 𝕜 A]

open TensorProduct LinearMap

theorem LinearIsometryEquiv.adjoint_toLinearMap_eq_symm {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [FiniteDimensional 𝕜 K] (e : A ≃ₗᵢ[𝕜] K) :
    adjoint e.toLinearMap = e.symm.toLinearMap := by
  have := FiniteDimensional.complete 𝕜 A
  have := FiniteDimensional.complete 𝕜 K
  calc adjoint e.toLinearMap = (ContinuousLinearMap.adjoint ↑e).toLinearMap := rfl
    _ = (e.symm).toLinearMap := congr($e.adjoint_eq_symm)

namespace Coalgebra
variable [Coalgebra 𝕜 A]

/-- A finite-dimensional inner product space with a coalgebra structure induces a ring structure,
where multiplication is given by `x * y = (adjoint comul) (x ⊗ₜ y)` and
`1 = (adjoint counit) (1 : 𝕜)`. -/
noncomputable def ringOfFiniteDimensionalInnerProductSpace :
    Ring A where
  mul x y := adjoint (comul (R := 𝕜) (A := A)) (x ⊗ₜ y)
  left_distrib x y z := by simp [HMul.hMul, tmul_add]
  right_distrib x y z := by simp [HMul.hMul, add_tmul]
  zero_mul x := by simp [HMul.hMul]
  mul_zero x := by simp [HMul.hMul]
  mul_assoc x y z := by
    dsimp [HMul.hMul]
    simp_rw [← rTensor_tmul, ← comp_apply, ← adjoint_rTensor, ← adjoint_comp,
      ← coassoc_symm, adjoint_comp, adjoint_lTensor, comp_apply]
    rw [(by rfl : (_root_.TensorProduct.assoc 𝕜 A A A).symm.toLinearMap
        = (assocIsometry 𝕜 A A A).symm.toLinearMap),
      LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    rfl
  one := adjoint (counit (R := 𝕜) (A := A)) (1 : 𝕜)
  one_mul x := by
    dsimp [HMul.hMul, OfNat.ofNat]
    rw [← rTensor_tmul, ← comp_apply, ← adjoint_rTensor, ← adjoint_comp, rTensor_counit_comp_comul]
    change adjoint ((lidIsometry 𝕜 A).symm.toLinearMap) _ = _
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    exact one_smul _ _
  mul_one x := by
    simp_rw [OfNat.ofNat, HMul.hMul]
    rw [← lTensor_tmul, ← comp_apply, ← adjoint_lTensor, ← adjoint_comp, lTensor_counit_comp_comul]
    change adjoint ((lidIsometry 𝕜 A).symm.trans (commIsometry 𝕜 𝕜 A)).toLinearMap _ = _
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    exact one_smul _ _

attribute [local instance] Coalgebra.ringOfFiniteDimensionalInnerProductSpace

lemma ringOfFiniteDimensionalInnerProductSpace_mul_def (x y : A) :
    x * y = adjoint (comul (R := 𝕜) (A := A)) (x ⊗ₜ y) := rfl

/-- A finite-dimensional inner product space with a coalgebra structure induces an algebra
structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`, `1 = (adjoint counit) 1` and
`algebraMap = adjoint counit`. -/
noncomputable def algebraOfFiniteDimensionalInnerProductSpace : Algebra 𝕜 A where
  algebraMap :=
  { toFun := adjoint (Coalgebra.counit (R := 𝕜) (A := A))
    map_one' := rfl
    map_mul' x y := by
      simp_rw [ringOfFiniteDimensionalInnerProductSpace_mul_def, ← map_tmul, ← adjoint_map,
        ← comp_apply, ← adjoint_comp, ← lTensor_comp_rTensor, comp_assoc,
        rTensor_counit_comp_comul, adjoint_comp]
      change _ = ((adjoint ((lidIsometry 𝕜 A).symm.toLinearMap)) ∘ₗ _) _
      rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
      simp only [LinearIsometryEquiv.symm_symm, toLinearEquiv_lidIsometry, adjoint_lTensor,
        coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_tmul, lid_tmul]
      rw [← smul_eq_mul, ← map_smul]
    map_zero' := map_zero _
    map_add' := map_add _ }
  commutes' r x := by
    dsimp
    simp_rw [ringOfFiniteDimensionalInnerProductSpace_mul_def, ← rTensor_tmul, ← lTensor_tmul,
      ← adjoint_lTensor, ← adjoint_rTensor, ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul,
      lTensor_counit_comp_comul]
    change adjoint (lidIsometry 𝕜 A).symm.toLinearMap _ =
      adjoint ((lidIsometry 𝕜 A).symm.trans (commIsometry 𝕜 𝕜 A)).toLinearMap _
    simp_rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    rfl
  smul_def' r x := by
    dsimp
    simp_rw [ringOfFiniteDimensionalInnerProductSpace_mul_def, ← rTensor_tmul, ← adjoint_rTensor,
      ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul]
    change _ = adjoint (lidIsometry 𝕜 A).symm.toLinearMap _
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    rfl

end Coalgebra
