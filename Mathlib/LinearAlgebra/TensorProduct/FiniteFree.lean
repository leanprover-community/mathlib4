/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section

open TensorProduct

/--
The M-algebra isomorphism `M ⊗[R] V ≃ₗ[M] (ι → M)` coming from the canonical
`ι`-indexed basis of a finite free `R`-module `V`.
-/
noncomputable def LinearEquiv.chooseBasis_piScalarRight (R : Type*) (M : Type*) (V : Type*)
    [CommSemiring M] [CommSemiring R] [Algebra R M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] :
    (M ⊗[R] V) ≃ₗ[M] (Module.Free.ChooseBasisIndex R V → M) :=
  (LinearEquiv.baseChange R M _ _ (Module.Free.chooseBasis R V).equivFun) ≪≫ₗ
    TensorProduct.piScalarRight R M M (Module.Free.ChooseBasisIndex R V)
