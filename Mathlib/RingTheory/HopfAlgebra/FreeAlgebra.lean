/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.FreeAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Generators

/-!
# Hopf algebra structure on `FreeAlgebra R X`

The generators `ι R x` of the free algebra are primitive, so `HopfAlgebra.ofPrimitives`
upgrades the bialgebra structure with the antipode extending `x ↦ -ι R x` anti-multiplicatively.
-/

@[expose] public section

namespace FreeAlgebra

open MulOpposite

variable (R : Type*) [CommRing R] {X : Type*}

/-- The generators of the free algebra are primitive. -/
lemma isPrimitiveElem_ι (x : X) : Bialgebra.IsPrimitiveElem R (ι R x) where
  counit_eq_zero := counit_ι R X x
  comul_eq_tmul_add_tmul := by rw [comul_ι, add_comm]

noncomputable instance instHopfAlgebra : HopfAlgebra R (FreeAlgebra R X) :=
  .ofPrimitives (lift R fun x ↦ op (-ι R x)) (adjoin_range_ι R X)
    (Set.forall_mem_range.2 (isPrimitiveElem_ι R)) (Set.forall_mem_range.2 fun x ↦ by simp)

@[simp]
lemma antipode_ι (x : X) : HopfAlgebra.antipode R (ι R x) = -ι R x := by
  exact (isPrimitiveElem_ι R x).antipode_eq_neg

end FreeAlgebra
