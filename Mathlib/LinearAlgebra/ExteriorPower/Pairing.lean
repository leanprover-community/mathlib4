/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Sophie Morel
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorPower.Pairing
import Mathlib.LinearAlgebra.Determinant

/-!
# The pairing between the exterior power of the dual and the exterior power

We construct the pairing
`exteriorPower.pairingDual : ⋀[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⋀[R]^n M))`.

-/

namespace exteriorPower

open TensorProduct PiTensorProduct

variable (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)

/-- The linear map from the `n`th exterior power to the `n`th tensor power obtained by
`MultilinearMap.alternarization`. -/
noncomputable def toTensorPower : ⋀[R]^n M →ₗ[R] ⨂[R]^n M :=
  alternatingMapLinearEquiv (MultilinearMap.alternatization (PiTensorProduct.tprod R))

variable {M n} in
open Equiv in
@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) :
    toTensorPower R M n (ιMulti R n v) =
      ∑ σ : Perm (Fin n), Perm.sign σ • PiTensorProduct.tprod R (fun i ↦ v (σ i)) := by
  dsimp [toTensorPower]
  simp only [alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

/-- The canonical `n`-alternating map from the dual of the `R`-module `M`
to the dual of `⨂[R]^n M`. -/
noncomputable def alternatingMapToDual :
    AlternatingMap R (Module.Dual R M) (Module.Dual R (⋀[R]^n M)) (Fin n) where
  toMultilinearMap := (toTensorPower R M n).dualMap.compMultilinearMap
    (TensorPower.multilinearMapToDual R M n)
  map_eq_zero_of_eq' f i j hf hij := by
    ext v
    suffices Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) = 0 by
      simpa [Matrix.det_apply] using this
    exact Matrix.det_zero_of_column_eq hij (by simp [hf])

variable {R M n} in
open Equiv in
@[simp]
theorem alternatingMapToDual_apply_ιMulti (f : (_ : Fin n) → Module.Dual R M) (v : Fin n → M) :
    alternatingMapToDual R M n f (ιMulti _ _ v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) := by
  simp [alternatingMapToDual, Matrix.det_apply]

/-- The linear map from the exterior power of the dual to the dual of the exterior power. -/
noncomputable def pairingDual :
    ⋀[R]^n (Module.Dual R M) →ₗ[R] Module.Dual R (⋀[R]^n M) :=
  alternatingMapLinearEquiv (alternatingMapToDual R M n)

variable {R M n} in
open Equiv in
@[simp]
lemma pairingDual_ιMulti_ιMulti (f : (_ : Fin n) → Module.Dual R M) (v : Fin n → M) :
    pairingDual R M n (ιMulti _ _ f) (ιMulti _ _ v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) := by
  simp [pairingDual]

end exteriorPower
