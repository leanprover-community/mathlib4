/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Ring.Basic

/-!
# Instances on PUnit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

namespace PUnit

@[to_additive]
instance commGroup : CommGroup PUnit where
  mul _ _ := unit
  one := unit
  inv _ := unit
  div _ _ := unit
  npow _ _ := unit
  zpow _ _ := unit
  mul_assoc := by intros; rfl
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  inv_mul_cancel := by intros; rfl
  mul_comm := by intros; rfl

-- shortcut instances
@[to_additive] instance : One PUnit where one := ()
@[to_additive] instance : Mul PUnit where mul _ _ := ()
@[to_additive] instance : Div PUnit where div _ _ := ()
@[to_additive] instance : Inv PUnit where inv _ := ()

-- dsimp loops when applying this lemma to its LHS,
-- probably https://github.com/leanprover/lean4/pull/2867
@[to_additive (attr := simp, nolint simpNF)]
theorem one_eq : (1 : PUnit) = unit :=
  rfl

-- note simp can prove this when the Boolean ring structure is introduced
@[to_additive]
theorem mul_eq {x y : PUnit} : x * y = unit :=
  rfl

@[to_additive (attr := simp)]
theorem div_eq {x y : PUnit} : x / y = unit :=
  rfl

@[to_additive (attr := simp)]
theorem inv_eq {x : PUnit} : x⁻¹ = unit :=
  rfl

instance commRing : CommRing PUnit where
  __ := PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  natCast _ := unit

instance cancelCommMonoidWithZero : CancelCommMonoidWithZero PUnit where

end PUnit
