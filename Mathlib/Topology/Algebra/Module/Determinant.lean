/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Determinant

#align_import topology.algebra.module.determinant from "leanprover-community/mathlib"@"4b262b8463002087e407be07080b91d213361e64"

/-!
# The determinant of a continuous linear map.
-/


namespace ContinuousLinearMap

/-- The determinant of a continuous linear map, mainly as a convenience device to be able to
write `A.det` instead of `(A : M →ₗ[R] M).det`. -/
noncomputable abbrev det {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M →L[R] M) : R :=
  LinearMap.det (A : M →ₗ[R] M)
#align continuous_linear_map.det ContinuousLinearMap.det

end ContinuousLinearMap

namespace ContinuousLinearEquiv

@[simp]
theorem det_coe_symm {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ≃L[R] M) : (A.symm : M →L[R] M).det = (A : M →L[R] M).det⁻¹ :=
  LinearEquiv.det_coe_symm A.toLinearEquiv
#align continuous_linear_equiv.det_coe_symm ContinuousLinearEquiv.det_coe_symm

end ContinuousLinearEquiv
