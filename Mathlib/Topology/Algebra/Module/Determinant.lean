/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The determinant of a continuous linear map.
-/

public section


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

theorem det_smulRight {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (f : 𝕜 →L[𝕜] 𝕜) (v : 𝕜) : (smulRight f v).det = f 1 * v := by simp

theorem det_toSpanSingleton {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (v : 𝕜) : (toSpanSingleton 𝕜 v).det = v := by rw [← smulRight_id, det_smulRight]; simp

@[deprecated (since := "2025-12-18")] alias det_one_smulRight := det_toSpanSingleton

end ContinuousLinearMap

namespace ContinuousLinearEquiv

@[simp]
theorem det_coe_symm {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ≃L[R] M) : (A.symm : M →L[R] M).det = (A : M →L[R] M).det⁻¹ :=
  LinearEquiv.det_coe_symm A.toLinearEquiv

end ContinuousLinearEquiv
