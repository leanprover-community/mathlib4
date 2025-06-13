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

Let `S` be an `R`-algebra, `N` an `S`-module, `ι` an index type and `Mᵢ` a family of `R`-modules.
We then have a natural map

`TensorProduct.piRightHom`: `N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i`

In general, this is not an isomorphism, but if `ι` is finite, then it is
and it is packaged as `TensorProduct.piRight`. Also a special case for when `Mᵢ = R` is given.

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Prod.lean` for binary products.

-/

variable (R : Type*) [CommSemiring R]
variable (S : Type*) [CommSemiring S] [Algebra R S]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (ι : Type*)

open LinearMap

namespace TensorProduct

section

variable {ι} (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

private noncomputable def piRightHomBil : N →ₗ[S] (∀ i, M i) →ₗ[R] ∀ i, N ⊗[R] M i where
  toFun n := LinearMap.pi (fun i ↦ mk R N (M i) n ∘ₗ LinearMap.proj i)
  map_add' _ _ := by
    ext
    simp [add_tmul]
  map_smul' _ _ := rfl

/-- For any `R`-module `N`, index type `ι` and family of `R`-modules `Mᵢ`, there is a natural
linear map `N ⊗[R] (∀ i, M i) →ₗ ∀ i, N ⊗[R] M i`. This map is an isomorphism if `ι` is finite. -/
noncomputable def piRightHom : N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i :=
  AlgebraTensorModule.lift <| piRightHomBil R S N M

@[simp]
lemma piRightHom_tmul (x : N) (f : ∀ i, M i) :
    piRightHom R S N M (x ⊗ₜ f) = (fun j ↦ x ⊗ₜ f j) :=
  rfl

variable [Fintype ι] [DecidableEq ι]

private noncomputable
def piRightInv : (∀ i, N ⊗[R] M i) →ₗ[S] N ⊗[R] ∀ i, M i :=
  LinearMap.lsum S (fun i ↦ N ⊗[R] M i) S <| fun i ↦
    AlgebraTensorModule.map LinearMap.id (single R M i)

@[simp]
private lemma piRightInv_apply (x : N) (m : ∀ i, M i) :
    piRightInv R S N M (fun i ↦ x ⊗ₜ m i) = x ⊗ₜ m := by
  simp only [piRightInv, lsum_apply, coeFn_sum, coe_comp, coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, AlgebraTensorModule.map_tmul, id_coe, id_eq, coe_single]
  rw [← tmul_sum]
  congr
  ext j
  simp

@[simp]
private lemma piRightInv_single (x : N) (i : ι) (m : M i) :
    piRightInv R S N M (Pi.single i (x ⊗ₜ m)) = x ⊗ₜ Pi.single i m := by
  have : Pi.single i (x ⊗ₜ m) = fun j ↦ x ⊗ₜ[R] (Pi.single i m j) := by
    ext j
    rw [← tmul_single]
  rw [this]
  simp

/-- Tensor product commutes with finite products on the right. -/
noncomputable def piRight : N ⊗[R] (∀ i, M i) ≃ₗ[S] ∀ i, N ⊗[R] M i :=
  LinearEquiv.ofLinear
    (piRightHom R S N M)
    (piRightInv R S N M)
    (by ext i x m j; simp [tmul_single])
    (by ext x j m; simp)

@[simp]
lemma piRight_apply (x : N ⊗[R] (∀ i, M i)) :
    piRight R S N M x = piRightHom R S N M x := by
  rfl

@[simp]
lemma piRight_symm_apply (x : N) (m : ∀ i, M i) :
    (piRight R S N M).symm (fun i ↦ x ⊗ₜ m i) = x ⊗ₜ m := by
  simp [piRight]

@[simp]
lemma piRight_symm_single (x : N) (i : ι) (m : M i) :
    (piRight R S N M).symm (Pi.single i (x ⊗ₜ m)) = x ⊗ₜ Pi.single i m := by
  simp [piRight]

end

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
