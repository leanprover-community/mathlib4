/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Pi

/-!

# Tensor product and products

In this file we examine the behaviour of the tensor product with arbitrary and finite products.

Let `S` be an `R`-algebra, `N` an `S`-module and `ι` an index type. We then have a natural map

`TensorProduct.piScalarRightHom`: `N ⊗[R] (ι → R) →ₗ[S] (ι → N)`

In general, this is not an isomorphism, but if `ι` is finite, then it is
and it is packaged as `TensorProduct.piScalarRight`.

## Notes

See `Mathlib.LinearAlgebra.TensorProduct.Prod` for binary products.

-/

variable (R : Type*) [CommSemiring R]
variable (S : Type*) [CommSemiring S] [Algebra R S]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (ι : Type*)

open LinearMap

namespace TensorProduct

private def piScalarRightHomBil : N →ₗ[S] (ι → R) →ₗ[R] (ι → N) where
  toFun n := LinearMap.compLeft (toSpanSingleton R N n) ι
  map_add' x y := by
    ext i j
    simp
  map_smul' s x := by
    ext i j
    dsimp only [coe_comp, coe_single, Function.comp_apply, compLeft_apply, toSpanSingleton_apply,
      RingHom.id_apply, smul_apply, Pi.smul_apply]
    rw [← IsScalarTower.smul_assoc, _root_.Algebra.smul_def, mul_comm, mul_smul]
    simp

/-- For any `R`-module `N` and index type `ι`, there is a natural
linear map `N ⊗[R] (ι → R) →ₗ (ι → N)`. This map is an isomorphism if `ι` is finite. -/
noncomputable def piScalarRightHom : N ⊗[R] (ι → R) →ₗ[S] (ι → N) :=
  AlgebraTensorModule.lift <| piScalarRightHomBil R S N ι

@[simp]
lemma piScalarRightHom_tmul (x : N) (f : ι → R) :
    piScalarRightHom R S N ι (x ⊗ₜ f) = (fun j ↦ f j • x) := by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

variable [Fintype ι] [DecidableEq ι]

private noncomputable
def piScalarRightInv : (ι → N) →ₗ[S] N ⊗[R] (ι → R) :=
  LinearMap.lsum S (fun _ ↦ N) S <| fun i ↦ {
    toFun := fun n ↦ n ⊗ₜ Pi.single i 1
    map_add' := fun x y ↦ by simp [add_tmul]
    map_smul' := fun _ _ ↦ rfl
  }

@[simp]
private lemma piScalarRightInv_single (x : N) (i : ι) :
    piScalarRightInv R S N ι (Pi.single i x) = x ⊗ₜ Pi.single i 1 := by
  simp [piScalarRightInv, Pi.single_apply, TensorProduct.ite_tmul]

/-- For any `R`-module `N` and finite index type `ι`, `N ⊗[R] (ι → R)` is canonically
isomorphic to `ι → N`. -/
noncomputable def piScalarRight : N ⊗[R] (ι → R) ≃ₗ[S] (ι → N) :=
  LinearEquiv.ofLinear
    (piScalarRightHom R S N ι)
    (piScalarRightInv R S N ι)
    (by ext i x j; simp [Pi.single_apply])
    (by ext x i; simp [Pi.single_apply_smul])

@[simp]
lemma piScalarRight_apply (x : N ⊗[R] (ι → R)) :
    piScalarRight R S N ι x = piScalarRightHom R S N ι x := by
  rfl

@[simp]
lemma piScalarRight_symm_single (x : N) (i : ι) :
    (piScalarRight R S N ι).symm (Pi.single i x) = x ⊗ₜ Pi.single i 1 := by
  simp [piScalarRight]

end TensorProduct
