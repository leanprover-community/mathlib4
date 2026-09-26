/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia, Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Generators

/-!
# Hopf algebra structure on `TensorAlgebra R M`

The generators `ι R m` of the tensor algebra are primitive, so `HopfAlgebra.ofPrimitives`
upgrades the bialgebra structure with the antipode extending `m ↦ -ι R m` anti-multiplicatively.
-/

@[expose] public section

namespace TensorAlgebra

open MulOpposite

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The generators of the tensor algebra are primitive. -/
lemma isPrimitiveElem_ι (m : M) : Bialgebra.IsPrimitiveElem R (ι R m) where
  counit_eq_zero := counit_ι m
  comul_eq_tmul_add_tmul := by rw [comul_ι, add_comm]

noncomputable instance instHopfAlgebra : HopfAlgebra R (TensorAlgebra R M) :=
  .ofPrimitives (lift R ((opLinearEquiv R).toLinearMap ∘ₗ (-ι R))) adjoin_range_ι
    (Set.forall_mem_range.2 (isPrimitiveElem_ι R)) (Set.forall_mem_range.2 fun m ↦ by simp)

@[simp]
lemma antipode_ι (m : M) : HopfAlgebra.antipode R (ι R m) = -ι R m := by
  exact (isPrimitiveElem_ι R m).antipode_eq_neg

end TensorAlgebra
