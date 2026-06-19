/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Ring.Equiv

/-!
# If a group acts multiplicatively on a semiring, each group element acts by a ring automorphism.

This result is split out from `Mathlib/Algebra/Ring/Action/Basic.lean`
to avoid needing the import of `Mathlib/Algebra/GroupWithZero/Action/Basic.lean`.
-/

@[expose] public section

section Semiring

variable (G : Type*) [Group G]
variable (R : Type*) [Semiring R]

/-- Each element of the group defines a semiring isomorphism. -/
@[simps!]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] : G →* (R ≃+* R) where
  toFun x := { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

instance : MulSemiringAction (R ≃+* R) R where
  smul := (· ·)
  mul_smul _ _ _ := rfl
  one_smul _ := rfl
  smul_zero := map_zero
  smul_one := map_one
  smul_add := map_add
  smul_mul := map_mul

end Semiring
