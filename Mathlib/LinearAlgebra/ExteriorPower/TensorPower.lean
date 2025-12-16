/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Interactions of exterior powers and tensor powers.
-/

@[expose] public section

open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ) {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace exteriorPower

/-! Map to the tensor power. -/

variable (M) in
/-- The linear map from the `n`th exterior power to the `n`th tensor power induced by
`MultilinearMap.alternarization`. -/
noncomputable def toTensorPower : ⋀[R]^n M →ₗ[R] (⨂[R]^n) M :=
    alternatingMapLinearEquiv <|
    MultilinearMap.alternatization (PiTensorProduct.tprod R)

open Equiv in
@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) :
    toTensorPower R n M (ιMulti R n v) =
      ∑ σ : Perm (Fin n), Perm.sign σ • PiTensorProduct.tprod R (fun i => v (σ i)) := by
  simp [toTensorPower, MultilinearMap.alternatization_apply]

/-! Linear form on the exterior power induced by a family of linear forms on the module. -/

open PiTensorProduct in
/-- A family `f` indexed by `Fin n` of linear forms on `M` defines a linear form on the `n`th
exterior power of `M`, by composing the map `exteriorPower.toTensorPower` to the `n`th tensor
power and then applying `(dualDistrib.compMultilinearMap (tprod R)) f`. -/
noncomputable def linearForm (f : Fin n → Module.Dual R M) :
    Module.Dual R (⋀[R]^n M) :=
  (dualDistrib.compMultilinearMap (tprod R)) f ∘ₗ toTensorPower R n M

@[simp]
lemma linearForm_apply (f : Fin n → Module.Dual R M) (x : ⋀[R]^n M) :
    linearForm R n f x = (PiTensorProduct.dualDistrib.compMultilinearMap
    (PiTensorProduct.tprod R)) f (toTensorPower R n M x) :=
  rfl

lemma linearForm_apply_ιMulti (f : Fin n → Module.Dual R M) (m : Fin n → M) :
    linearForm R n f (ιMulti R n m) =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, f i (m (σ i)) := by
  simp

/-- If `f` is a family of linear forms on `M` (index by `Fin n`) and `p` is a linear map
from `N` to `M`, then the composition of `exteriorPower.linearForm R n f` and
of `exteriorPower.map p` is equal to the linear form induced by the family
`fun i ↦ (f i).comp p`. -/
lemma linearForm_comp_map (f : Fin n → Module.Dual R M) (p : N →ₗ[R] M) :
    (linearForm R n f).comp (map n p) =
    linearForm R n (fun (i : Fin n) => (f i).comp p) := by
  apply LinearMap.ext_on (ιMulti_span R n (M := N))
  rintro x ⟨y, h⟩
  simp [← h]

lemma linearForm_comp_map_apply (f : Fin n → Module.Dual R M)
    (p : N →ₗ[R] M) (x : ⋀[R]^n N) :
    (linearForm R n f) (map n p x) =
    linearForm R n (fun (i : Fin n) => (f i).comp p) x := by
  rw [← LinearMap.comp_apply, linearForm_comp_map]

/-- A family `f` of linear forms on `M` indexed by `Fin n` defines an `n`-fold alternating form
on `M`, by composing the linear form on `⋀[R]^n M` indeuced by `f` (defined in
`exteriorPower.linearForm`) with the canonical `n`-fold alternating map from `M` to its
`n`th exterior power. -/
noncomputable def altForm (f : Fin n → Module.Dual R M) :
    M [⋀^Fin n]→ₗ[R] R :=
  (linearForm R n f).compAlternatingMap (ιMulti R n)

@[simp]
lemma altForm_apply (f : Fin n → Module.Dual R M) (m : Fin n → M) :
    altForm R n f m = linearForm R n f (ιMulti R n m) :=
  rfl

end exteriorPower
