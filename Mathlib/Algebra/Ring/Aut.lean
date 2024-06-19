/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Equiv

#align_import algebra.ring.aut from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Ring automorphisms

This file defines the automorphism group structure on `RingAut R := RingEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

This file is kept separate from `Data/Equiv/Ring` so that `GroupTheory.Perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

RingAut
-/


/-- The group of ring automorphisms. -/
abbrev RingAut (R : Type*) [Mul R] [Add R] :=
  RingEquiv R R
#align ring_aut RingAut

namespace RingAut

section mul_add

variable (R : Type*) [Mul R] [Add R]

/-- The group operation on automorphisms of a ring is defined by
`fun g h => RingEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Group (RingAut R) where
  mul g h := RingEquiv.trans h g
  one := RingEquiv.refl R
  inv := RingEquiv.symm
  mul_assoc := by intros; rfl
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  mul_left_inv := RingEquiv.self_trans_symm
/- Porting note: was by
  refine_struct
    { mul := fun g h => RingEquiv.trans h g
      one := RingEquiv.refl R
      inv := RingEquiv.symm
      div := _
      npow := @npowRec _ ⟨RingEquiv.refl R⟩ ⟨fun g h => RingEquiv.trans h g⟩
      zpow :=
        @zpowRec _ ⟨RingEquiv.refl R⟩ ⟨fun g h => RingEquiv.trans h g⟩
          ⟨RingEquiv.symm⟩ } <;>
    intros <;>
    ext <;>
    try rfl <;>
    apply Equiv.left_inv
 -/

instance : Inhabited (RingAut R) :=
  ⟨1⟩

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
def toAddAut : RingAut R →* AddAut R := by
  refine'
  { toFun := RingEquiv.toAddEquiv
    .. } <;> (intros; rfl)
#align ring_aut.to_add_aut RingAut.toAddAut

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
def toMulAut : RingAut R →* MulAut R := by
  refine'
  { toFun := RingEquiv.toMulEquiv
    .. } <;> (intros; rfl)
#align ring_aut.to_mul_aut RingAut.toMulAut

/-- Monoid homomorphism from ring automorphisms to permutations. -/
def toPerm : RingAut R →* Equiv.Perm R := by
  refine'
  { toFun := RingEquiv.toEquiv
    .. } <;> (intros; rfl)
#align ring_aut.to_perm RingAut.toPerm

end mul_add

section Semiring

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
#align ring_aut.apply_mul_semiring_action RingAut.applyMulSemiringAction

@[simp]
protected theorem smul_def (f : RingAut R) (r : R) : f • r = f r :=
  rfl
#align ring_aut.smul_def RingAut.smul_def

instance apply_faithfulSMul : FaithfulSMul (RingAut R) R :=
  ⟨RingEquiv.ext⟩
#align ring_aut.apply_has_faithful_smul RingAut.apply_faithfulSMul

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
#align mul_semiring_action.to_ring_aut MulSemiringAction.toRingAut
#align mul_semiring_action.to_ring_aut_apply MulSemiringAction.toRingAut_apply

end Semiring

end RingAut
