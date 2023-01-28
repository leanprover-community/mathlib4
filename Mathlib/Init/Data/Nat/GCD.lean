/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro


! This file was ported from Lean 3 source module init.data.nat.gcd
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Meta.WellFoundedTactics

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

#align nat.coprime Nat.coprime

end Nat
