/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens

! This file was ported from Lean 3 source module data.nat.choose.dvd
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime

/-!
# Divisibility properties of binomial coefficients
-/


namespace Nat

open Nat

namespace Prime

variable {p a b k : ℕ}

theorem dvd_choose_add (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p ≤ a + b) :
    p ∣ choose (a + b) a := by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  rw [← add_choose_mul_factorial_mul_factorial, ← choose_symm_add, hp.dvd_mul, hp.dvd_mul,
    hp.dvd_factorial, hp.dvd_factorial] at h₁
  exact (h₁.resolve_right hbp.not_le).resolve_right hap.not_le
#align nat.prime.dvd_choose_add Nat.Prime.dvd_choose_add

lemma dvd_choose (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p ≤ b) : p ∣ choose b a :=
  have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)
#align nat.prime.dvd_choose Nat.Prime.dvd_choose

lemma dvd_choose_self (hp : Prime p) (hk : k ≠ 0) (hkp : k < p) : p ∣ choose p k :=
  hp.dvd_choose hkp (sub_lt ((zero_le _).trans_lt hkp) hk.bot_lt) le_rfl
#align nat.prime.dvd_choose_self Nat.Prime.dvd_choose_self

end Prime

end Nat
