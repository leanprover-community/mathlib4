/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.zmod.parity
! leanprover-community/mathlib commit 048240e809f04e2bde02482ab44bc230744cc6c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Basic

/-!
# Relating parity to natural numbers mod 2

This module provides lemmas relating `ZMod 2` to `Even` and `Odd`.

## Tags

parity, zmod, even, odd
-/


namespace ZMod

theorem eq_zero_iff_even {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.cast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm
#align zmod.eq_zero_iff_even ZMod.eq_zero_iff_even

theorem eq_one_iff_odd {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← @Nat.cast_one (ZMod 2), ZMod.eq_iff_modEq_nat, Nat.odd_iff, Nat.ModEq]
  norm_num
#align zmod.eq_one_iff_odd ZMod.eq_one_iff_odd

theorem ne_zero_iff_odd {n : ℕ} : (n : ZMod 2) ≠ 0 ↔ Odd n := by
  constructor <;>
    · contrapose
      simp [eq_zero_iff_even]
#align zmod.ne_zero_iff_odd ZMod.ne_zero_iff_odd

end ZMod

