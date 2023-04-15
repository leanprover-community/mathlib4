/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

! This file was ported from Lean 3 source module linear_algebra.tensor_product_basis
! leanprover-community/mathlib commit 4977fd9da637b6e0a805c1cf460c3a6b8df3f556
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FinsuppVectorSpace

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `LinearAlgebra.TensorProduct` since they depend on
`LinearAlgebra.FinsuppVectorSpace` which in turn imports `LinearAlgebra.TensorProduct`.

-/


noncomputable section

open Set LinearMap Submodule

section CommRing

variable {R : Type _} {M : Type _} {N : Type _} {ι : Type _} {κ : Type _}

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- Porting note: cannot synth RingHomCompTriple
set_option synthInstance.etaExperiment true in
/-- If b : ι → M and c : κ → N are bases then so is λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N. -/
def Basis.tensorProduct (b : Basis ι R M) (c : Basis κ R N) :
    Basis (ι × κ) R (TensorProduct R M N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R R)).symm
#align basis.tensor_product Basis.tensorProduct

-- Porting note: resolved diamond
set_option synthInstance.etaExperiment true in
@[simp]
theorem Basis.tensorProduct_apply (b : Basis ι R M) (c : Basis κ R N) (i : ι) (j : κ) :
    Basis.tensorProduct b c (i, j) = b i ⊗ₜ c j := by simp [Basis.tensorProduct]
#align basis.tensor_product_apply Basis.tensorProduct_apply

-- Porting note: resolved diamond
set_option synthInstance.etaExperiment true in
theorem Basis.tensorProduct_apply' (b : Basis ι R M) (c : Basis κ R N) (i : ι × κ) :
    Basis.tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by simp [Basis.tensorProduct]
#align basis.tensor_product_apply' Basis.tensorProduct_apply'

end CommRing

