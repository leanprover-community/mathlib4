/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau

! This file was ported from Lean 3 source module number_theory.basic
! leanprover-community/mathlib commit 168ad7fc5d8173ad38be9767a22d50b8ecf1cd00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.Ideal.Quotient

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/


section

open Ideal Ideal.Quotient

theorem dvd_sub_pow_of_dvd_sub {R : Type _} [CommRing R] {p : ℕ} {a b : R} (h : (p : R) ∣ a - b)
    (k : ℕ) : (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k := by
  induction' k with k ih
  · rwa [pow_one, pow_zero, pow_one, pow_one]
  rw [pow_succ' p k, pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ, Nat.cast_mul]
  refine' mul_dvd_mul _ ih
  let I : Ideal R := span {↑p}
  let f : R →+* R ⧸ I := mk I
  have hp : (p : R ⧸ I) = 0 := by rw [← map_natCast f, eq_zero_iff_mem, mem_span_singleton]
  rw [← mem_span_singleton, ← Ideal.Quotient.eq] at h
  rw [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, RingHom.map_pow,
    RingHom.map_pow, h, geom_sum₂_self, hp, zero_mul]
#align dvd_sub_pow_of_dvd_sub dvd_sub_pow_of_dvd_sub

end
