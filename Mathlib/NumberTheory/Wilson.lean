/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol, Haobo Ma, Wenlin Zhang
-/
module

public import Mathlib.Data.ZMod.Factorial
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## Main results

* `ZMod.wilsons_lemma`: the value of `(p - 1)!` modulo a prime `p`.
* `Nat.prime_iff_fac_equiv_neg_one`: that value characterises primality.
* `ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq` expresses `(p - 1)!` using the square of
  the half-factorial when `p` is odd.
* `ZMod.half_factorial_sq_eq_neg_one` gives the half-factorial as an explicit square root of `-1`
  modulo a prime not congruent to three modulo four.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Give `wilsons_lemma` a descriptive name.
-/

public section

assert_not_exists legendreSym.quadratic_reciprocity

open Finset Nat FiniteField ZMod

open scoped Nat

namespace ZMod

/-- If `p` is odd, pairing each factor above `(p - 1) / 2` with its negative gives
`(p - 1)! = (-1) ^ ((p - 1) / 2) * (((p - 1) / 2)!) ^ 2` in `ZMod p`. -/
theorem factorial_eq_neg_one_pow_mul_half_factorial_sq {p : ℕ} (hp : Odd p) :
    ((p - 1)! : ZMod p) = (-1) ^ ((p - 1) / 2) * (((p - 1) / 2)! : ZMod p) ^ 2 := by
  rw [pow_two, ← Nat.factorial_mul_descFactorial (show (p - 1) / 2 ≤ p - 1 by lia),
    show p - 1 - (p - 1) / 2 = (p - 1) / 2 by grind, Nat.cast_mul,
    cast_descFactorial (by lia), mul_rotate']

variable (p : ℕ) [Fact p.Prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp]
theorem wilsons_lemma : ((p - 1)! : ZMod p) = -1 := by
  refine
    calc
      ((p - 1)! : ZMod p) = ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial, prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)),
          prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  symm
  refine prod_bij (fun a _ => (a : ZMod p).val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_Ico, ← Nat.succ_sub hp, Nat.add_one_sub_one]
    constructor
    · apply Nat.pos_of_ne_zero; rw [← @val_zero p]
      intro h; apply Units.ne_zero a (val_injective p h)
    · exact val_lt _
  · intro _ _ _ _ h; rw [Units.ext_iff]; exact val_injective p h
  · intro b hb
    rw [mem_Ico, Nat.succ_le_iff, ← succ_sub hp, Nat.add_one_sub_one, pos_iff_ne_zero] at hb
    refine ⟨Units.mk0 b ?_, Finset.mem_univ _, ?_⟩
    · intro h; apply hb.1; apply_fun val at h
      simpa only [val_cast_of_lt hb.right, val_zero] using h
    · simp only [val_cast_of_lt hb.right, Units.val_mk0]
  · rintro a -; simp only [cast_id, natCast_val]

variable {p} in
/-- Let `p` be prime with `p % 4 ≠ 3`. Then `((p - 1) / 2)!` is a specified square root of `-1`
in `ZMod p`. -/
theorem half_factorial_sq_eq_neg_one (hp : p % 4 ≠ 3) :
    (((p - 1) / 2)! : ZMod p) ^ 2 = -1 := by
  rcases (Fact.out (p := p.Prime)).eq_two_or_odd' with rfl | hodd
  · decide +revert
  have hp_mod_two : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hm : Even ((p - 1) / 2) := Nat.even_iff.mpr (by lia)
  rw [← wilsons_lemma p, factorial_eq_neg_one_pow_mul_half_factorial_sq hodd,
    hm.neg_one_pow, one_mul]

@[simp]
theorem prod_Ico_one_prime : ∏ x ∈ Ico 1 p, (x : ZMod p) = -1 := by
  -- Porting note: was `conv in Ico 1 p =>`
  conv =>
    congr
    congr
    rw [← Nat.add_one_sub_one p, succ_sub (Fact.out (p := p.Prime)).pos]
  rw [← prod_natCast, Finset.prod_Ico_id_eq_factorial, wilsons_lemma]

end ZMod

namespace Nat

variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
theorem prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n ≠ 1) : Prime n := by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  refine hm2.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hm).mp (hm1.trans ?_)))
  rw [← ZMod.natCast_eq_zero_iff, cast_add, cast_one, h, neg_add_cancel]

/-- **Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. -/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Prime n ↔ ((n - 1)! : ZMod n) = -1 := by
  refine ⟨fun h1 => ?_, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  have := Fact.mk h1
  exact ZMod.wilsons_lemma n

end Nat
