/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of a continuous linear map.
-/


namespace ContinuousLinearMap

/-- The determinant of a continuous linear map, mainly as a convenience device to be able to
write `A.det` instead of `(A : M →ₗ[R] M).det`. -/
noncomputable abbrev det {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M →L[R] M) : R :=
  LinearMap.det (A : M →ₗ[R] M)

theorem det_pi {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M]
    [TopologicalSpace M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : ι → M →L[R] M) :
    (pi (fun i ↦ (f i).comp (proj i))).det = ∏ i, (f i).det :=
  LinearMap.det_pi _

theorem det_one_smulRight {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜] (v : 𝕜) :
    ((1 : 𝕜 →L[𝕜] 𝕜).smulRight v).det = v := by
  nontriviality 𝕜
  have : (1 : 𝕜 →L[𝕜] 𝕜).smulRight v = v • (1 : 𝕜 →L[𝕜] 𝕜) := by
    ext1
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      Algebra.id.smul_eq_mul, one_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply, mul_one]
  rw [this, ContinuousLinearMap.det, ContinuousLinearMap.coe_smul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id, LinearMap.det_smul,
    Module.finrank_self, LinearMap.det_id, pow_one, mul_one]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

@[simp]
theorem det_coe_symm {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ≃L[R] M) : (A.symm : M →L[R] M).det = (A : M →L[R] M).det⁻¹ :=
  LinearEquiv.det_coe_symm A.toLinearEquiv

end ContinuousLinearEquiv
