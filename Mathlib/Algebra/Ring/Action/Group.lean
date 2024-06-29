/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Algebra.Ring.Equiv

/-!
# If a group acts multiplicatively on a semiring, each group element acts by a ring automorphism.

This result is split out from `Mathlib.Algebra.Ring.Action.Basic`
to avoid needing the import of `Mathlib.GroupTheory.GroupAction.Group`.
-/

section Semiring

variable (G : Type*) [Group G]
variable (R : Type*) [Semiring R]

/-- Each element of the group defines a semiring isomorphism. -/
@[simps!]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
#align mul_semiring_action.to_ring_equiv MulSemiringAction.toRingEquiv
#align mul_semiring_action.to_ring_equiv_symm_apply MulSemiringAction.toRingEquiv_symm_apply
#align mul_semiring_action.to_ring_equiv_apply MulSemiringAction.toRingEquiv_apply

end Semiring
