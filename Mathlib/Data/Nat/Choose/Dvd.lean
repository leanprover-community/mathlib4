/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens

! This file was ported from Lean 3 source module data.nat.choose.dvd
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.Nat.Prime

/-!
# Divisibility properties of binomial coefficients
-/


namespace Nat

open Nat

namespace Prime

theorem dvd_choose_add {p a b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b) (hp : Prime p) :
    p ∣ choose (a + b) a := by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  have h₂ : ¬p ∣ a ! := mt hp.dvd_factorial.1 (not_le_of_gt hap)
  have h₃ : ¬p ∣ b ! := mt hp.dvd_factorial.1 (not_le_of_gt hbp)
  rw [← choose_mul_factorial_mul_factorial (le.intro rfl), mul_assoc, hp.dvd_mul, hp.dvd_mul,
      add_tsub_cancel_left a b] at h₁ <;>
    exact h₁.resolve_right (not_or.2 ⟨h₂, h₃⟩)
#align nat.prime.dvd_choose_add Nat.Prime.dvd_choose_add

theorem dvd_choose_self {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : Prime p) : p ∣ choose p k := by
  have r : k + (p - k) = p := by
    rw [← add_tsub_assoc_of_le (Nat.le_of_lt hkp) k, add_tsub_cancel_left]
  have e : p ∣ choose (k + (p - k)) k :=
    dvd_choose_add hkp (Nat.sub_lt (hk.trans hkp) hk) (by rw [r]) hp
  rwa [r] at e
#align nat.prime.dvd_choose_self Nat.Prime.dvd_choose_self

end Prime

end Nat

