/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct

#align_import linear_algebra.tensor_product_basis from "leanprover-community/mathlib"@"f784cc6142443d9ee623a20788c282112c322081"

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `LinearAlgebra.TensorProduct` since they depend on
`LinearAlgebra.FinsuppVectorSpace` which in turn imports `LinearAlgebra.TensorProduct`.
-/


noncomputable section

open Set LinearMap Submodule

section CommSemiring

variable {R : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`. -/
def Basis.tensorProduct (b : Basis ι R M) (c : Basis κ R N) :
    Basis (ι × κ) R (TensorProduct R M N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R R)).symm
#align basis.tensor_product Basis.tensorProduct

@[simp]
theorem Basis.tensorProduct_apply (b : Basis ι R M) (c : Basis κ R N) (i : ι) (j : κ) :
    Basis.tensorProduct b c (i, j) = b i ⊗ₜ c j := by
  simp [Basis.tensorProduct]
#align basis.tensor_product_apply Basis.tensorProduct_apply

theorem Basis.tensorProduct_apply' (b : Basis ι R M) (c : Basis κ R N) (i : ι × κ) :
    Basis.tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by
  simp [Basis.tensorProduct]
#align basis.tensor_product_apply' Basis.tensorProduct_apply'

@[simp]
theorem Basis.tensorProduct_repr_tmul_apply (b : Basis ι R M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (Basis.tensorProduct b c).repr (m ⊗ₜ n) (i, j) = b.repr m i * c.repr n j := by
  simp [Basis.tensorProduct]
#align basis.tensor_product_repr_tmul_apply Basis.tensorProduct_repr_tmul_apply

end CommSemiring

section PiTensorProduct

open PiTensorProduct BigOperators

attribute [local ext] PiTensorProduct.ext

open LinearMap

open scoped TensorProduct

variable {ι R : Type*} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {κ : ι → Type*}

variable [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)] [(x : R) → Decidable (x ≠ 0)]

/-- Let `ι` be a `Fintype` and `M` be a family of modules indexed by `ι`. If `b i : κ i → M i`
is a basis for every `i` in `ι`, then `fun (p : Π i, κ i) ↦ ⨂ₜ[R] i, b i (p i)` is a basis
of `⨂[R] i, M i`.
-/
def Basis.piTensorProduct (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i ↦ (b i).repr)).trans <|
        (finsuppPiTensorProduct R _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R)).symm

end PiTensorProduct

end
