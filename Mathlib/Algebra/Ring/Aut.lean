/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.ring.aut
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.Algebra.Hom.Aut
import Mathbin.Algebra.Ring.Equiv

/-!
# Ring automorphisms

This file defines the automorphism group structure on `ring_aut R := ring_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/ring` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

ring_aut
-/


/-- The group of ring automorphisms. -/
@[reducible]
def RingAut (R : Type _) [Mul R] [Add R] :=
  RingEquiv R R
#align ring_aut RingAut

namespace RingAut

section mul_add

variable (R : Type _) [Mul R] [Add R]

/-- The group operation on automorphisms of a ring is defined by
`λ g h, ring_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Group (RingAut R) := by
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

instance : Inhabited (RingAut R) :=
  ⟨1⟩

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
def toAddAut : RingAut R →* AddAut R := by
  refine_struct { toFun := RingEquiv.toAddEquiv } <;> intros <;> rfl
#align ring_aut.to_add_aut RingAut.toAddAut

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
def toMulAut : RingAut R →* MulAut R := by
  refine_struct { toFun := RingEquiv.toMulEquiv } <;> intros <;> rfl
#align ring_aut.to_mul_aut RingAut.toMulAut

/-- Monoid homomorphism from ring automorphisms to permutations. -/
def toPerm : RingAut R →* Equiv.Perm R := by
  refine_struct { toFun := RingEquiv.toEquiv } <;> intros <;> rfl
#align ring_aut.to_perm RingAut.toPerm

end mul_add

section Semiring

variable {G R : Type _} [Group G] [Semiring R]

/-- The tautological action by the group of automorphism of a ring `R` on `R`.-/
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

instance apply_has_faithful_smul : FaithfulSMul (RingAut R) R :=
  ⟨fun _ _ => RingEquiv.ext⟩
#align ring_aut.apply_has_faithful_smul RingAut.apply_has_faithful_smul

variable (G R)

/-- Each element of the group defines a ring automorphism.

This is a stronger version of `distrib_mul_action.to_add_aut` and
`mul_distrib_mul_action.to_mul_aut`. -/
@[simps]
def MulSemiringAction.toRingAut [MulSemiringAction G R] :
    G →* RingAut R where
  toFun := MulSemiringAction.toRingEquiv G R
  map_mul' g h := RingEquiv.ext <| mul_smul g h
  map_one' := RingEquiv.ext <| one_smul _
#align mul_semiring_action.to_ring_aut MulSemiringAction.toRingAut

end Semiring

end RingAut
