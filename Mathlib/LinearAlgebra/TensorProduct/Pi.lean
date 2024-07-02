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

-/

variable (R : Type*) [CommRing R]
variable (S : Type*) [CommRing S] [Algebra R S]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (ι : Type*)

open LinearMap TensorProduct

private def TensorProduct.piScalarRightHomBil : N →ₗ[S] (ι → R) →ₗ[R] (ι → N) where
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
noncomputable def TensorProduct.piScalarRightHom : N ⊗[R] (ι → R) →ₗ[S] (ι → N) :=
  AlgebraTensorModule.lift <| piScalarRightHomBil R S N ι

@[simp]
lemma TensorProduct.piScalarRightHom_tmul (x : N) (f : ι → R) :
    piScalarRightHom R S N ι (x ⊗ₜ f) = (fun j ↦ f j • x) := by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

variable [Fintype ι] [DecidableEq ι]

private noncomputable
def TensorProduct.piScalarRightInv : (ι → N) →ₗ[S] N ⊗[R] (ι → R) :=
  LinearMap.lsum S (fun _ ↦ N) S <| fun i ↦ {
    toFun := fun n ↦ n ⊗ₜ Pi.single i 1
    map_add' := fun x y ↦ by simp [add_tmul]
    map_smul' := fun s x ↦ rfl
  }

@[simp]
private lemma TensorProduct.piScalarRightInv_single (x : N) (i : ι) :
    piScalarRightInv R S N ι (Pi.single i x) = x ⊗ₜ Pi.single i 1 := by
  simp [piScalarRightInv, Pi.single_apply, TensorProduct.ite_tmul]

@[simp]
lemma Pi.single_apply_smul (x : N) (i j : ι) :
    (Pi.single i 1 : ι → R) j • x = (Pi.single i x : ι → N) j := by
  simp [Pi.single_apply]

/-- For any `R`-module `N` and finite index type `ι`, `N ⊗[R] (ι → R)` is canonically
isomorphic to `ι → N`. -/
noncomputable def TensorProduct.piScalarRight : N ⊗[R] (ι → R) ≃ₗ[S] (ι → N) :=
  LinearEquiv.ofLinear
    (piScalarRightHom R S N (ι := ι))
    (piScalarRightInv R S N (ι := ι))
    (by ext i x j; simp [Pi.single_apply])
    (by ext x i; simp)

@[simp]
lemma TensorProduct.piScalarRight_tmul (x : N) (f : ι → R) :
    piScalarRight R S N ι (x ⊗ₜ f) = (fun j ↦ f j • x) := by
  simp [piScalarRight]
