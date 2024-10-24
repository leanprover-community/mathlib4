/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.PUnitInstances.Algebra

/-!
# Instances on PUnit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

namespace PUnit

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

@[simp]
theorem gcd_eq {x y : PUnit} : gcd x y = unit :=
  rfl

@[simp]
theorem lcm_eq {x y : PUnit} : lcm x y = unit :=
  rfl

@[simp]
theorem norm_unit_eq {x : PUnit} : normUnit x = 1 :=
  rfl

end PUnit
