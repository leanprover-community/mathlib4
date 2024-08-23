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
where `m →₀ R` is replaced by `m → R` under the hypothesis `[Finite m]`.

## Main results

**TODO name** If `n` is a finite type, then `Rⁿ ⊗[R] M` is naturally isomorphic to `Mⁿ`.
If `n` is a finite type, then `Rⁿ ⊗[R] Rᵐ` is naturally isomorphic to `Rᵃˣᵐ`.
If `m` is a finite type, then `Rⁿ ⊗[R] Rᵐ` is naturally isomorphic to `Rᵃˣᵐ`.

-/

namespace TensorProduct

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] (ι : Type*) [DecidableEq ι] [Finite ι]

/-- `finiteLeft R M N n` is the natural R-module isomorphism `Mⁿ ⊗[R] N = (M ⊗[R] N)ⁿ`
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

/-- `finiteRight R M N n` is the natural R-module isomorphism `M ⊗[R] Nⁿ = (M ⊗[R] N)ⁿ`
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

/-- If `ι` is finite then the tensor product of `ι → R` and `N` is linearly equivalent
to `ι → N`. -/
noncomputable def finiteScalarLeft :
    (ι → R) ⊗[R] N ≃ₗ[R] ι → N :=
  finiteLeft R R N ι ≪≫ₗ (LinearEquiv.piCongrRight (fun _ ↦ TensorProduct.lid R N))

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

/-- The tensor product of `M` and `ι → R` is linearly equivalent to `ι → M` -/
noncomputable def finiteScalarRight :
    M ⊗[R] (ι → R) ≃ₗ[R] ι → M :=
  finiteRight R M R ι ≪≫ₗ LinearEquiv.piCongrRight (fun _ ↦ TensorProduct.rid R M)

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


noncomputable def isom'' {R : Type*} [CommRing R] {m n : Type*} [Finite m] [DecidableEq m] :
    (m → R) ⊗[R] (n → R) ≃ₗ[R] (m × n → R) :=
  (LinearEquiv.rTensor (n → R) (Finsupp.linearEquivFunOnFinite R R m).symm :
    (m → R) ⊗[R] (n → R) ≃ₗ[R] ((m →₀ R) ⊗[R] (n → R))) ≪≫ₗ
  (TensorProduct.finsuppScalarLeft R (n → R) m :
    (m →₀ R) ⊗[R] (n → R) ≃ₗ[R] (m →₀ (n → R))) ≪≫ₗ
  ((Finsupp.linearEquivFunOnFinite R (n → R) m :
    (m →₀ (n → R)) ≃ₗ[R] m → n → R)) ≪≫ₗ
  ((LinearEquiv.curry R m n).symm :
    (m → n → R) ≃ₗ[R] (m × n → R))
