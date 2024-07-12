/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GCDMonoid.Basic

#align_import algebra.punit_instances from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

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
  mul_left_inv := by intros; rfl
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
#align punit.one_eq PUnit.one_eq
#align punit.zero_eq PUnit.zero_eq

-- note simp can prove this when the Boolean ring structure is introduced
@[to_additive]
theorem mul_eq {x y : PUnit} : x * y = unit :=
  rfl
#align punit.mul_eq PUnit.mul_eq
#align punit.add_eq PUnit.add_eq

@[to_additive (attr := simp)]
theorem div_eq {x y : PUnit} : x / y = unit :=
  rfl
#align punit.div_eq PUnit.div_eq
#align punit.sub_eq PUnit.sub_eq

@[to_additive (attr := simp)]
theorem inv_eq {x : PUnit} : x⁻¹ = unit :=
  rfl
#align punit.inv_eq PUnit.inv_eq
#align punit.neg_eq PUnit.neg_eq

instance commRing : CommRing PUnit where
  __ := PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  natCast _ := unit

instance cancelCommMonoidWithZero : CancelCommMonoidWithZero PUnit where

-- This is too high-powered and should be split off also
instance normalizedGCDMonoid : NormalizedGCDMonoid PUnit where
  gcd _ _ := unit
  lcm _ _ := unit
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by intros; rfl
  normUnit_coe_units := by intros; rfl
  gcd_dvd_left _ _ := ⟨unit, by subsingleton⟩
  gcd_dvd_right _ _ := ⟨unit, by subsingleton⟩
  dvd_gcd {_ _} _ _ _ := ⟨unit, by subsingleton⟩
  gcd_mul_lcm _ _ := ⟨1, by subsingleton⟩
  lcm_zero_left := by intros; rfl
  lcm_zero_right := by intros; rfl
  normalize_gcd := by intros; rfl
  normalize_lcm := by intros; rfl

-- Porting note (#10618): simpNF lint: simp can prove this @[simp]
theorem gcd_eq {x y : PUnit} : gcd x y = unit :=
  rfl
#align punit.gcd_eq PUnit.gcd_eq

-- Porting note (#10618): simpNF lint: simp can prove this @[simp]
theorem lcm_eq {x y : PUnit} : lcm x y = unit :=
  rfl
#align punit.lcm_eq PUnit.lcm_eq

@[simp]
theorem norm_unit_eq {x : PUnit} : normUnit x = 1 :=
  rfl
#align punit.norm_unit_eq PUnit.norm_unit_eq

end PUnit
