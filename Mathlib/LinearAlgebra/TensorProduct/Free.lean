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

/--
The `M`-algebra isomorphism `M ⊗[R] V ≃ₗ[M] (ι → M)` coming from the canonical
`ι`-indexed basis of a finite free `R`-module `V`.
-/
@[simps! apply symm_apply]
noncomputable def LinearEquiv.chooseBasis_piScalarRight
    (R : Type*) (M : Type*) (V : Type*)
    [CommSemiring M] [CommSemiring R] [Algebra R M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] :
    (M ⊗[R] V) ≃ₗ[M] (Module.Free.ChooseBasisIndex R V → M) :=
  (LinearEquiv.baseChange R M _ _ (Module.Free.chooseBasis R V).equivFun) ≪≫ₗ
    TensorProduct.piScalarRight R M M (Module.Free.ChooseBasisIndex R V)

/--
The `M`-algebra isomorphism `M ⊗[R] V ≃ₗ[M] (ι →₀ M)` coming from the canonical
`ι`-indexed basis of a free `R`-module `V`.
-/
@[simps! apply symm_apply]
noncomputable def LinearEquiv.chooseBasis_finsuppScalarRight (R : Type*) (M : Type*) (V : Type*)
    [CommSemiring M] [CommSemiring R] [Algebra R M]
    [AddCommGroup V] [Module R V] [Module.Free R V] :
    (M ⊗[R] V) ≃ₗ[M] (Module.Free.ChooseBasisIndex R V →₀ M) :=
  (LinearEquiv.baseChange R M _ _ (Module.Free.chooseBasis R V).repr) ≪≫ₗ
    TensorProduct.finsuppScalarRight R M M (Module.Free.ChooseBasisIndex R V)
