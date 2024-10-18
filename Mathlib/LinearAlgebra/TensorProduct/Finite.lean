/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!

# Tensor products with finite free modules

We prove various results about tensoring over `R` with `Rⁿ`, if `n` is a finite type.

This file contains variants of some results in `Mathlib/LinearAlgebra/DirectSum/Finsupp.lean`
where `n →₀ R` in that file is replaced by `n → R` in this, under the hypothesis `[Finite n]`.

## Main definitions

* `TensorProduct.finiteLeft R M N n` : If `n` is a finite type, `Mⁿ ⊗[R] N ≃ₗ[R] (M ⊗[R] N)ⁿ`.
* `TensorProduct.finiteRight R M N n` : If `n` is a finite type, `M ⊗[R] Nⁿ ≃ₗ[R] (M ⊗[R] N)ⁿ`.
* `TensorProduct.finiteScalarLeft R N n` : If `n` is a finite type, `Rⁿ ⊗[R] N ≃ₗ[R] Nⁿ`.
* `TensorProduct.finiteScalarRight R M n` : If `n` is a finite type, `M ⊗[R] Rⁿ ≃ₗ[R] Mⁿ`.
* `TensorProduct.finiteTensorPiLid R N n m` : if `n` is a finite type, `Rⁿ ⊗[R] Nᵐ ≃ₗ[R] Nⁿˣᵐ`.
* `TensorProduct.piTensorFiniteRid R M m n` : if `n` is a finite type, `Mᵐ ⊗[R] Rⁿ ≃ₗ[R] Mᵐˣⁿ`.

Note that in the last two results, the type `m` is arbitrary and does not have to be finite.
-/

namespace TensorProduct

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] (ι : Type*) [Finite ι]

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

end TensorProduct
