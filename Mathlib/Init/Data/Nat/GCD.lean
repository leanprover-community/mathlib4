/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

-/

import Batteries.Data.Nat.Gcd
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Mathport.Rename

#align_import init.data.nat.gcd from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-!
# Definitions and properties of gcd, lcm, and coprime
-/


open WellFounded

namespace Nat

/-! gcd -/

#align nat.gcd Nat.gcd
#align nat.gcd_zero_left Nat.gcd_zero_left
#align nat.gcd_succ Nat.gcd_succ
#align nat.gcd_one_left Nat.gcd_one_left
#align nat.gcd_self Nat.gcd_self
#align nat.gcd_zero_right Nat.gcd_zero_right
#align nat.gcd_rec Nat.gcd_rec
#align nat.gcd.induction Nat.gcd.induction
#align nat.lcm Nat.lcm

theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [Nat.gcd_succ]
#align nat.gcd_def Nat.gcd_def

#align nat.coprime Nat.Coprime

end Nat

#align nat.gcd_dvd Nat.gcd_dvd
#align nat.gcd_dvd_left Nat.gcd_dvd_left
#align nat.gcd_dvd_right Nat.gcd_dvd_right
#align nat.gcd_le_left Nat.gcd_le_left
#align nat.gcd_le_right Nat.gcd_le_right
#align nat.dvd_gcd Nat.dvd_gcd
#align nat.dvd_gcd_iff Nat.dvd_gcd_iff
#align nat.gcd_comm Nat.gcd_comm
#align nat.gcd_eq_left_iff_dvd Nat.gcd_eq_left_iff_dvd
#align nat.gcd_eq_right_iff_dvd Nat.gcd_eq_right_iff_dvd
#align nat.gcd_assoc Nat.gcd_assoc
#align nat.gcd_one_right Nat.gcd_one_right
#align nat.gcd_mul_left Nat.gcd_mul_left
#align nat.gcd_mul_right Nat.gcd_mul_right
#align nat.gcd_pos_of_pos_left Nat.gcd_pos_of_pos_left
#align nat.gcd_pos_of_pos_right Nat.gcd_pos_of_pos_right
#align nat.eq_zero_of_gcd_eq_zero_left Nat.eq_zero_of_gcd_eq_zero_left
#align nat.eq_zero_of_gcd_eq_zero_right Nat.eq_zero_of_gcd_eq_zero_right
#align nat.gcd_div Nat.gcd_div
#align nat.gcd_dvd_gcd_of_dvd_left Nat.gcd_dvd_gcd_of_dvd_left
#align nat.gcd_dvd_gcd_of_dvd_right Nat.gcd_dvd_gcd_of_dvd_right
#align nat.gcd_dvd_gcd_mul_left Nat.gcd_dvd_gcd_mul_left
#align nat.gcd_dvd_gcd_mul_right Nat.gcd_dvd_gcd_mul_right
#align nat.gcd_dvd_gcd_mul_left_right Nat.gcd_dvd_gcd_mul_left_right
#align nat.gcd_dvd_gcd_mul_right_right Nat.gcd_dvd_gcd_mul_right_right
#align nat.gcd_eq_left Nat.gcd_eq_left
#align nat.gcd_eq_right Nat.gcd_eq_right
#align nat.gcd_mul_left_left Nat.gcd_mul_left_left
#align nat.gcd_mul_left_right Nat.gcd_mul_left_right
#align nat.gcd_mul_right_left Nat.gcd_mul_right_left
#align nat.gcd_mul_right_right Nat.gcd_mul_right_right
#align nat.gcd_gcd_self_right_left Nat.gcd_gcd_self_right_left
#align nat.gcd_gcd_self_right_right Nat.gcd_gcd_self_right_right
#align nat.gcd_gcd_self_left_right Nat.gcd_gcd_self_left_right
#align nat.gcd_gcd_self_left_left Nat.gcd_gcd_self_left_left
#align nat.gcd_eq_zero_iff Nat.gcd_eq_zero_iff
#align nat.lcm_comm Nat.lcm_comm
#align nat.lcm_zero_left Nat.lcm_zero_left
#align nat.lcm_zero_right Nat.lcm_zero_right
#align nat.lcm_one_left Nat.lcm_one_left
#align nat.lcm_one_right Nat.lcm_one_right
#align nat.lcm_self Nat.lcm_self
#align nat.dvd_lcm_left Nat.dvd_lcm_left
#align nat.dvd_lcm_right Nat.dvd_lcm_right
#align nat.gcd_mul_lcm Nat.gcd_mul_lcm
#align nat.lcm_dvd Nat.lcm_dvd
#align nat.lcm_assoc Nat.lcm_assoc
#align nat.lcm_ne_zero Nat.lcm_ne_zero
#align nat.coprime_iff_gcd_eq_one Nat.coprime_iff_gcd_eq_one
#align nat.coprime.gcd_eq_one Nat.Coprime.gcd_eq_one
#align nat.coprime.symm Nat.Coprime.symm
#align nat.coprime_comm Nat.coprime_comm
#align nat.coprime.dvd_of_dvd_mul_right Nat.Coprime.dvd_of_dvd_mul_right
#align nat.coprime.dvd_of_dvd_mul_left Nat.Coprime.dvd_of_dvd_mul_left
#align nat.coprime.gcd_mul_left_cancel Nat.Coprime.gcd_mul_left_cancel
#align nat.coprime.gcd_mul_right_cancel Nat.Coprime.gcd_mul_right_cancel
#align nat.coprime.gcd_mul_left_cancel_right Nat.Coprime.gcd_mul_left_cancel_right
#align nat.coprime.gcd_mul_right_cancel_right Nat.Coprime.gcd_mul_right_cancel_right
#align nat.coprime_div_gcd_div_gcd Nat.coprime_div_gcd_div_gcd
#align nat.not_coprime_of_dvd_of_dvd Nat.not_coprime_of_dvd_of_dvd
#align nat.exists_coprime Nat.exists_coprime
#align nat.exists_coprime' Nat.exists_coprime'
#align nat.coprime.mul Nat.Coprime.mul
#align nat.coprime.mul_right Nat.Coprime.mul_right
#align nat.coprime.coprime_dvd_left Nat.Coprime.coprime_dvd_left
#align nat.coprime.coprime_dvd_right Nat.Coprime.coprime_dvd_right
#align nat.coprime.coprime_mul_left Nat.Coprime.coprime_mul_left
#align nat.coprime.coprime_mul_right Nat.Coprime.coprime_mul_right
#align nat.coprime.coprime_mul_left_right Nat.Coprime.coprime_mul_left_right
#align nat.coprime.coprime_mul_right_right Nat.Coprime.coprime_mul_right_right
#align nat.coprime.coprime_div_left Nat.Coprime.coprime_div_left
#align nat.coprime.coprime_div_right Nat.Coprime.coprime_div_right
#align nat.coprime_mul_iff_left Nat.coprime_mul_iff_left
#align nat.coprime_mul_iff_right Nat.coprime_mul_iff_right
#align nat.coprime.gcd_left Nat.Coprime.gcd_left
#align nat.coprime.gcd_right Nat.Coprime.gcd_right
#align nat.coprime.gcd_both Nat.Coprime.gcd_both
#align nat.coprime.mul_dvd_of_dvd_of_dvd Nat.Coprime.mul_dvd_of_dvd_of_dvd
#align nat.coprime_zero_left Nat.coprime_zero_left
#align nat.coprime_zero_right Nat.coprime_zero_right
#align nat.coprime_one_left Nat.coprime_one_left
#align nat.coprime_one_right Nat.coprime_one_right
#align nat.coprime_self Nat.coprime_self
#align nat.coprime.pow_left Nat.Coprime.pow_left
#align nat.coprime.pow_right Nat.Coprime.pow_right
#align nat.coprime.pow Nat.Coprime.pow
#align nat.coprime.eq_one_of_dvd Nat.Coprime.eq_one_of_dvd
#align nat.gcd_mul_dvd_mul_gcd Nat.gcd_mul_dvd_mul_gcd
#align nat.coprime.gcd_mul Nat.Coprime.gcd_mul
#align nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul
