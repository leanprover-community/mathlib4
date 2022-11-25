/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Std.Data.Rat
import Mathlib.Algebra.Ring.Basic

/-!
# Stub port for `linarith`.
-/

set_option warningAsError false

instance : AddCommGroup Rat where
  add_comm := sorry
  add_assoc := sorry
  add_zero := sorry
  zero_add := sorry
  sub_eq_add_neg := sorry
  add_left_neg := sorry

instance : CommRing Rat where
  left_distrib := sorry
  right_distrib := sorry
  sub_eq_add_neg := sorry
  zero_mul := sorry
  mul_zero := sorry
  natCast := (·)
  natCast_zero := sorry
  natCast_succ := sorry
  add_left_neg := sorry
  intCast := (·)
  intCast_ofNat := sorry
  intCast_negSucc := sorry
  mul_assoc := sorry
  mul_one := sorry
  one_mul := sorry
  mul_comm := sorry
