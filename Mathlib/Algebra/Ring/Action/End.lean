/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Aut

/-!
# Ring automorphisms

This file defines the automorphism group structure on `RingAut R := RingEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

This file is kept separate from `Mathlib/Algebra/Ring/Equiv.lean` so that
`Mathlib/GroupTheory/Perm.lean` is free to use equivalences (and other files that use them) before
the group structure is defined.

## Tags

ring aut
-/

namespace RingAut
variable {G R : Type*} [Group G] [Semiring R]

/-- The tautological action by the group of automorphism of a ring `R` on `R`. -/
instance applyMulSemiringAction :
    MulSemiringAction (RingAut R) R where
  smul := (· <| ·)
  smul_zero := RingEquiv.map_zero
  smul_add := RingEquiv.map_add
  smul_one := RingEquiv.map_one
  smul_mul := RingEquiv.map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem smul_def (f : RingAut R) (r : R) : f • r = f r :=
  rfl

instance apply_faithfulSMul : FaithfulSMul (RingAut R) R :=
  ⟨RingEquiv.ext⟩

variable (G R)

/-- Each element of the group defines a ring automorphism.

This is a stronger version of `DistribMulAction.toAddAut` and
`MulDistribMulAction.toMulAut`. -/
@[simps]
def _root_.MulSemiringAction.toRingAut [MulSemiringAction G R] :
    G →* RingAut R where
  toFun := MulSemiringAction.toRingEquiv G R
  map_mul' g h := RingEquiv.ext <| mul_smul g h
  map_one' := RingEquiv.ext <| one_smul _

end RingAut
