/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Primitive

/-!
# Hopf algebra structure on `TensorAlgebra R M`

The bialgebra structure is `TensorAlgebra.instBialgebra`. The antipode is the unique
anti-algebra map induced by `fun x => op (-ι R x)`; since each `ι R x` is primitive, the Hopf
structure follows from `HopfAlgebra.ofPrimitives`.
-/

@[expose] public section

namespace TensorAlgebra

open HopfAlgebra LinearMap MulOpposite
open scoped TensorProduct

variable (R : Type*) [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]

noncomputable instance instHopfAlgebra : HopfAlgebra R (TensorAlgebra R M) :=
  ofPrimitives (lift R <| (opLinearEquiv R).toLinearMap ∘ₗ (-ι R))
    (s := Set.range (ι R))
    adjoin_range_ι
    (by rintro _ ⟨m, rfl⟩; exact ⟨by simp, by simp⟩)
    (by rintro _ ⟨m, rfl⟩; simp)

end TensorAlgebra
