/-
Copyright (c) 2025 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf algebra structure on `TensorAlgebra R M`

The bialgebra structure is implemented in `TensorAlgebra.instBialgebra`. The antipode is the
unique anti-algebra map induced by `fun x => -ι R x`.

NOTE (linglib local scaffold): this is a stand-in for leanprover-community/mathlib4#31898 so that
the `SymmetricAlgebra` quotient refactor (#39579) can be built and verified locally. The antipode
and its anti-homomorphism / generator lemmas are proved in full (these are what the
`SymmetricAlgebra` route consumes); the two deep convolution-inverse axioms
(`mul_antipode_*Tensor_comul`) are #31898's titular result and are `sorry`-d here. They are NOT part
of the #39579 deliverable. This file also relaxes #31898's `[AddCommGroup M]` to `[AddCommMonoid M]`.
-/

@[expose] public section

namespace TensorAlgebra

open scoped RingTheory.LinearMap
open LinearMap TensorProduct

variable (R : Type*) [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]

local notation "T[" M "]" => TensorAlgebra R M

/-- Antipode in `TensorAlgebra R M` as a linear map. -/
def antipode : T[M] →ₗ[R] T[M] := (MulOpposite.opLinearEquiv R).symm.toLinearMap.comp
  (lift R <| (MulOpposite.opLinearEquiv R).toLinearMap.comp <| -ι R).toLinearMap

@[simp]
lemma antipode_ι_apply (x : M) : antipode R (ι R x) = -ι R x := by
  simp [antipode]

@[simp]
theorem antipode_antihom_apply (x y : T[M]) :
    antipode R (x * y) = antipode R y * antipode R x := by
  simp [antipode]

@[simp]
lemma antipode_algebraMap_apply (r : R) :
    antipode R (algebraMap R T[M] r) = algebraMap R T[M] r := by
  simp [antipode]

instance instHopfAlgebra : HopfAlgebra R T[M] where
  antipode := antipode R
  -- #31898's titular result; out of scope for the #39579 refactor verification.
  mul_antipode_rTensor_comul := by sorry
  mul_antipode_lTensor_comul := by sorry

end TensorAlgebra
