/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.Ideal.Quotient

#align_import number_theory.basic from "leanprover-community/mathlib"@"168ad7fc5d8173ad38be9767a22d50b8ecf1cd00"

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

theorem dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} {a b : R} (h : (p : R) ∣ a - b)
    (k : ℕ) : (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k := by
  induction' k with k ih
  -- ⊢ ↑(p ^ (Nat.zero + 1)) ∣ a ^ p ^ Nat.zero - b ^ p ^ Nat.zero
  · rwa [pow_one, pow_zero, pow_one, pow_one]
    -- 🎉 no goals
  rw [pow_succ' p k, pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ, Nat.cast_mul]
  -- ⊢ ↑p * ↑(p ^ (k + 1)) ∣ (Finset.sum (Finset.range p) fun i => (a ^ p ^ k) ^ i  …
  refine' mul_dvd_mul _ ih
  -- ⊢ ↑p ∣ Finset.sum (Finset.range p) fun i => (a ^ p ^ k) ^ i * (b ^ p ^ k) ^ (p …
  let f : R →+* R ⧸ span {(p : R)} := mk (span {(p : R)})
  -- ⊢ ↑p ∣ Finset.sum (Finset.range p) fun i => (a ^ p ^ k) ^ i * (b ^ p ^ k) ^ (p …
  have hf : ∀ r : R, (p : R) ∣ r ↔ f r = 0 := fun r ↦ by rw [eq_zero_iff_mem, mem_span_singleton]
  -- ⊢ ↑p ∣ Finset.sum (Finset.range p) fun i => (a ^ p ^ k) ^ i * (b ^ p ^ k) ^ (p …
  rw [hf, map_sub, sub_eq_zero] at h
  -- ⊢ ↑p ∣ Finset.sum (Finset.range p) fun i => (a ^ p ^ k) ^ i * (b ^ p ^ k) ^ (p …
  rw [hf, RingHom.map_geom_sum₂, map_pow, map_pow, h, geom_sum₂_self, mul_eq_zero_of_left]
  -- ⊢ ↑p = 0
  rw [← map_natCast f, eq_zero_iff_mem, mem_span_singleton]
  -- 🎉 no goals
#align dvd_sub_pow_of_dvd_sub dvd_sub_pow_of_dvd_sub

end
