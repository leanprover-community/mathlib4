/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!

# Tensor product and products

In this file we examine the behaviour of the tensor product with arbitrary and finite products.

Let `S` be an `R`-algebra, `N` an `S`-module and `ι` an index type. We then have a natural map

`TensorProduct.piScalarRightHom`: `N ⊗[R] (ι → R) →ₗ[S] (ι → N)`

In general, this is not an isomorphism, but if `ι` is a `Fintype`, then it is
and it is packaged as `TensorProduct.piScalarRight`.

This file also contains variants of some results in `Mathlib/LinearAlgebra/DirectSum/Finsupp.lean`
where `n →₀ R` in that file is replaced by `n → R` in this, under the hypothesis `[Finite n]`.

## Main definitions

* `TensorProduct.piScalarRight` : if `ι` is a fintype then `N ⊗[R] (ι → R) ≃ₗ[S] (ι → N)`.
* `TensorProduct.finiteLeft R M N n` : If `n` is a finite type, `Mⁿ ⊗[R] N ≃ₗ[R] (M ⊗[R] N)ⁿ`.
* `TensorProduct.finiteRight R M N n` : If `n` is a finite type, `M ⊗[R] Nⁿ ≃ₗ[R] (M ⊗[R] N)ⁿ`.
* `TensorProduct.finiteScalarLeft R N n` : If `n` is a finite type, `Rⁿ ⊗[R] N ≃ₗ[R] Nⁿ`.
* `TensorProduct.finiteScalarRight R M n` : If `n` is a finite type, `M ⊗[R] Rⁿ ≃ₗ[R] Mⁿ`.
* `TensorProduct.finiteTensorPiLid R N n m` : if `n` is a finite type, `Rⁿ ⊗[R] Nᵐ ≃ₗ[R] Nⁿˣᵐ`.
* `TensorProduct.piTensorFiniteRid R M m n` : if `n` is a finite type, `Mᵐ ⊗[R] Rⁿ ≃ₗ[R] Mᵐˣⁿ`.

## Notes

See `Mathlib.LinearAlgebra.TensorProduct.Prod` for binary products.

-/

variable (R : Type*) [CommSemiring R]
variable (S : Type*) [CommSemiring S] [Algebra R S]

open LinearMap

namespace TensorProduct

variable (M : Type*) [AddCommMonoid M] [Module R M]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (ι : Type*)

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
linear map `N ⊗[R] (ι → R) →ₗ (ι → N)`. This map is an isomorphism if `ι` is finite:
see `TensorProduct.piScalarRight`. -/
noncomputable def piScalarRightHom : N ⊗[R] (ι → R) →ₗ[S] (ι → N) :=
  AlgebraTensorModule.lift <| piScalarRightHomBil R S N ι

@[simp]
lemma piScalarRightHom_tmul (x : N) (f : ι → R) :
    piScalarRightHom R S N ι (x ⊗ₜ f) = (fun j ↦ f j • x) := by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

section Fintype

variable [Fintype ι] [DecidableEq ι]

private noncomputable
def piScalarRightInv : (ι → N) →ₗ[S] N ⊗[R] (ι → R) :=
  LinearMap.lsum S (fun _ ↦ N) S <| fun i ↦ {
    toFun := fun n ↦ n ⊗ₜ Pi.single i 1
    map_add' := fun x y ↦ by simp [add_tmul]
    map_smul' := fun s x ↦ rfl
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

end Fintype

section Finite

variable [Finite ι]

open scoped Classical in
/-- `finiteLeft R M N n` is the natural `R`-module isomorphism `Mⁿ ⊗[R] N = (M ⊗[R] N)ⁿ`
when `n` is a finite type. -/
noncomputable def finiteLeft : (ι → M) ⊗[R] N ≃ₗ[R] ι → M ⊗[R] N :=
  (LinearEquiv.rTensor N (Finsupp.linearEquivFunOnFinite R M ι).symm :
    (ι → M) ⊗[R] N ≃ₗ[R] ((ι →₀ M) ⊗[R] N)) ≪≫ₗ
  (TensorProduct.finsuppLeft R M N ι :
    (ι →₀ M) ⊗[R] N ≃ₗ[R] ι →₀ (M ⊗[R] N)) ≪≫ₗ
  (Finsupp.linearEquivFunOnFinite R (M ⊗[R] N) ι :
    (ι →₀ M ⊗[R] N) ≃ₗ[R] ι → M ⊗[R] N)

variable {R M N ι}

@[simp]
lemma finiteLeft_apply_tmul_apply (p : ι → M) (n : N) (i : ι) :
    finiteLeft R M N ι (p ⊗ₜ[R] n) i = p i ⊗ₜ[R] n := by
  simp [finiteLeft]

theorem finiteLeft_apply (t : (ι → M) ⊗[R] N) (i : ι) :
    finiteLeft R M N ι t i = LinearMap.rTensor N (LinearMap.proj i) t := by
  induction t with
  | zero => simp
  | tmul m f => simp [finiteLeft]
  | add x y hx hy => simp [map_add, hx, hy]

variable (R M N ι)

open scoped Classical in
/-- `finiteRight R M N n` is the natural `R`-module isomorphism `M ⊗[R] Nⁿ = (M ⊗[R] N)ⁿ`
when `n` is a finite type. -/
noncomputable def finiteRight : M ⊗[R] (ι → N) ≃ₗ[R] ι → M ⊗[R] N :=
  (LinearEquiv.lTensor M (Finsupp.linearEquivFunOnFinite R N ι).symm :
    M ⊗[R] (ι → N) ≃ₗ[R] M ⊗[R] (ι →₀ N)) ≪≫ₗ
  (TensorProduct.finsuppRight R M N ι :
    M ⊗[R] (ι →₀ N) ≃ₗ[R] ι →₀ (M ⊗[R] N)) ≪≫ₗ
  (Finsupp.linearEquivFunOnFinite R (M ⊗[R] N) ι :
    (ι →₀ M ⊗[R] N) ≃ₗ[R] ι → M ⊗[R] N)

variable {R M N ι}

@[simp]
lemma finiteRight_apply_tmul_apply (m : M) (p : ι → N) (i : ι) :
    finiteRight R M N ι (m ⊗ₜ[R] p) i = m ⊗ₜ[R] p i := by
  simp [finiteRight]

theorem finiteRight_apply (t : M ⊗[R] (ι → N)) (i : ι) :
    finiteRight R M N ι t i = LinearMap.lTensor M (LinearMap.proj i) t := by
  induction t with
  | zero => simp
  | tmul m f => simp [finiteRight]
  | add x y hx hy => simp [map_add, hx, hy]

variable (R N ι)

/-- If `ι` is finite then `finiteScalarLeft R N ι` is the natural isomorphism
`(ι → R) ⊗[R] N ≃ₗ[R] ι → N`. -/
noncomputable def finiteScalarLeft :
    (ι → R) ⊗[R] N ≃ₗ[R] ι → N :=
  (finiteLeft R R N ι :  (ι → R) ⊗[R] N ≃ₗ[R] ι → R ⊗[R] N) ≪≫ₗ
  (LinearEquiv.piCongrRight (fun _ ↦ TensorProduct.lid R N) :
    (ι → R ⊗[R] N) ≃ₗ[R] ι → N)

variable {R N ι}

@[simp]
lemma finiteScalarLeft_apply_tmul_apply (p : ι → R) (n : N) (i : ι) :
    finiteScalarLeft R N ι (p ⊗ₜ[R] n) i = p i • n := by
  simp [finiteScalarLeft]

lemma finiteScalarLeft_apply (pn : (ι → R) ⊗[R] N) (i : ι) :
    finiteScalarLeft R N ι pn i = TensorProduct.lid R N ((LinearMap.proj i).rTensor N pn) := by
  induction pn with
  | zero => simp
  | tmul m f => simp
  | add x y hx hy => simp [map_add, hx, hy]

variable (R M ι)

/-- If `ι` is finite then `finiteScalarLeft R M ι` is the natural isomorphism
`M ⊗[R] (ι → R) ≃ₗ[R] ι → M`. -/
noncomputable def finiteScalarRight :
    M ⊗[R] (ι → R) ≃ₗ[R] ι → M :=
  (finiteRight R M R ι : M ⊗[R] (ι → R) ≃ₗ[R] ι → (M ⊗[R] R)) ≪≫ₗ
  (LinearEquiv.piCongrRight (fun _ ↦ TensorProduct.rid R M) :
    (ι → (M ⊗[R] R)) ≃ₗ[R] ι → M)

variable {R M ι}

@[simp]
lemma finiteScalarRight_apply_tmul_apply (m : M) (p : ι → R) (i : ι) :
    finiteScalarRight R M ι (m ⊗ₜ[R] p) i = p i • m := by
  simp [finiteScalarRight, finiteRight]

lemma finiteScalarRight_apply (t : M ⊗[R] (ι → R)) (i : ι) :
    finiteScalarRight R M ι t i = TensorProduct.rid R M ((LinearMap.proj i).lTensor M t) := by
  induction t with
  | zero => simp
  | tmul m f => simp
  | add x y hx hy => simp [map_add, hx, hy]

variable (κ : Type*)

variable (R N ι)
/-- If `ι` is finite then `finiteTensorPiLid R N ι κ` is the natural isomorphism
`(ι → R) ⊗[R] (κ → N) ≃ₗ[R] ι × κ → N`. -/
noncomputable def finiteTensorPiLid : (ι → R) ⊗[R] (κ → N) ≃ₗ[R] ι × κ → N :=
  (finiteScalarLeft R (κ → N) ι :
    (ι → R) ⊗[R] (κ → N) ≃ₗ[R] (ι → κ → N)) ≪≫ₗ
  ((LinearEquiv.curry R N ι κ).symm :
    (ι → κ → N) ≃ₗ[R] (ι × κ → N))

variable {R N ι κ}

@[simp]
theorem finiteTensorPiLid_apply_apply (f : ι → R) (g : κ → N) (a : ι) (b : κ) :
    finiteTensorPiLid R N ι κ (f ⊗ₜ[R] g) (a, b) = f a • g b := by
  simp [finiteTensorPiLid]

variable (R M)

/-- If `ι` is finite then `piTensorFiniteRid R M κ ι` is the natural isomorphism
`(κ → M) ⊗[R] (ι → R) ≃ₗ[R] κ × ι → M`. -/
noncomputable def piTensorFiniteRid (κ ι : Type*) [Finite ι] :
    (κ → M) ⊗[R] (ι → R) ≃ₗ[R] κ × ι → M :=
  (finiteScalarRight R (κ → M) ι :
    (κ → M) ⊗[R] (ι → R) ≃ₗ[R] (ι → κ → M)) ≪≫ₗ
  ((LinearEquiv.curry R M ι κ).symm :
    (ι → κ → M) ≃ₗ[R] ι × κ → M) ≪≫ₗ
  (LinearEquiv.funCongrLeft R M (Equiv.prodComm κ ι) :
    (ι × κ → M) ≃ₗ[R] κ × ι → M)

variable {R M}

@[simp]
theorem piTensorFiniteRid_apply_apply (f : κ → M) (g : ι → R) (a : κ) (b : ι) :
    piTensorFiniteRid R M κ ι (f ⊗ₜ[R] g) (a, b) = g b • f a := by
  simp [piTensorFiniteRid]

end Finite

end TensorProduct
