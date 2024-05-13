/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

#align_import data.zmod.coprime from "leanprover-community/mathlib"@"4b4975cf92a1ffe2ddfeff6ff91b0c46a9162bf5"

/-!
# Coprimality and vanishing

We show that for prime `p`, the image of an integer `a` in `ZMod p` vanishes if and only if
`a` and `p` are not coprime.
-/


namespace ZMod

/-- If `p` is a prime and `a` is an integer, then `a : ZMod p` is zero if and only if
`gcd a p ≠ 1`. -/
theorem eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] :
    (a : ZMod p) = 0 ↔ a.gcd p ≠ 1 := by
  rw [Ne, Int.gcd_comm, Int.gcd_eq_one_iff_coprime,
    (Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, Classical.not_not,
    intCast_zmod_eq_zero_iff_dvd]
#align zmod.eq_zero_iff_gcd_ne_one ZMod.eq_zero_iff_gcd_ne_one

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : ZMod p` is nonzero. -/
theorem ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p = 1) : (a : ZMod p) ≠ 0 :=
  mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)
#align zmod.ne_zero_of_gcd_eq_one ZMod.ne_zero_of_gcd_eq_one

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : ZMod p` is zero. -/
theorem eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p ≠ 1) : (a : ZMod p) = 0 :=
  (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h
#align zmod.eq_zero_of_gcd_ne_one ZMod.eq_zero_of_gcd_ne_one

end ZMod
