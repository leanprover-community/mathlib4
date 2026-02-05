/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensor product with free modules.

This file contains lemmas about tensoring with free modules.
-/

@[expose] public section

open TensorProduct

variable {R : Type*} (A : Type*) {V : Type*}
    [CommSemiring A] [CommSemiring R] [Algebra R A]
    [AddCommGroup V] [Module R V]
    {ι : Type*} (b : Module.Basis ι R V)

/--
The `A`-algebra isomorphism `A ⊗[R] V ≃ₗ[A] (ι → A)` coming from an
`ι`-indexed basis of a finite free `R`-module `V`.
-/
@[simps! apply symm_apply]
noncomputable def Algebra.TensorProduct.equivPiOfFiniteBasis [Finite ι] :
    (A ⊗[R] V) ≃ₗ[A] (ι → A) :=
  open Classical in
  have : Fintype ι := .ofFinite _
  (b.equivFun.baseChange R A _ _) ≪≫ₗ TensorProduct.piScalarRight R A A ι

/--
The `A`-algebra isomorphism `A ⊗[R] V ≃ₗ[A] (ι →₀ A)` coming from an
`ι`-indexed basis of a free `R`-module `V`.
-/
@[simps! apply symm_apply]
noncomputable def Algebra.TensorProduct.equivFinsuppOfBasis :
    (A ⊗[R] V) ≃ₗ[A] (ι →₀ A) :=
  open Classical in
  (b.repr.baseChange R A _ _) ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι
