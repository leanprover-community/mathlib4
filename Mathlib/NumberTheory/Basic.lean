import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/

public section


section

open Ideal Ideal.Quotient

theorem dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} {a b : R} (h : (p : R) ∣ a - b)
    (k : ℕ) : (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k := by
  induction k with
  | zero => rwa [pow_one, pow_zero, pow_one, pow_one]
  | succ k ih =>
    rw [pow_succ p k, pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ']
    refine mul_dvd_mul ?_ ih
    let f : R →+* R ⧸ span {(p : R)} := mk (span {(p : R)})
    have hf : ∀ r : R, (p : R) ∣ r ↔ f r = 0 := fun r ↦ by rw [eq_zero_iff_mem, mem_span_singleton]
    rw [hf, map_sub, sub_eq_zero] at h
    rw [hf, RingHom.map_geom_sum₂, map_pow, map_pow, h, geom_sum₂_self, mul_eq_zero_of_left]
    rw [← map_natCast f, eq_zero_iff_mem, mem_span_singleton]

end
