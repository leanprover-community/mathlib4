/-
Copyright (c) 2026 Haoming Ning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoming Ning
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Primality via localization away from an element

This file proves a criterion for primality in localization.

## Main results

* `IsLocalization.Away.prime_of_prime_in_localization`: If `p` is prime, `x` is irreducible, and
  `algebraMap R (Away p) x` is prime, then `x` is prime. Also known as Nagata's criterion.

## References

See <https://stacks.math.columbia.edu/tag/0afu> for reference for
`IsLocalization.Away.prime_of_prime_in_localization`.
-/

@[expose] public section

open Localization Ideal

variable {R : Type*} [CommRing R] [IsDomain R]

namespace IsLocalization.Away

/-- If `p` is prime, `p ∤ x`, and the image of `c` in `R[1/p]` lies in the span of the image
of `x`, then `x ∣ c`. -/
lemma dvd_of_mem_span_singleton_localization
    {p : R} (hp_prime : Prime p) {x : R} (hpx : ¬(p ∣ x))
    {c : R} (hc : algebraMap R (Away p) c ∈ Ideal.span {algebraMap R (Away p) x}) :
    x ∣ c := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hc
  obtain ⟨n, y, hqpn⟩ := IsLocalization.Away.surj p q
  have hcy : c * p ^ n = x * y := IsLocalization.injective (Away p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hp_prime.ne_zero)
    (by simp only [map_mul, map_pow]; rw [← hq, ← hqpn]; ring)
  obtain ⟨z, rfl⟩ := hp_prime.pow_dvd_of_dvd_mul_left (n := n) hpx
    ⟨c, by simpa only [mul_comm] using hcy.symm⟩
  simp only [mul_comm, ← mul_assoc] at hcy
  exact ⟨z, mul_right_cancel₀ (pow_ne_zero n hp_prime.ne_zero) hcy⟩

/-- Nagata's criterion: If `p` is prime, `x` is irreducible, and the image of `x` in `R[1/p]`
is prime, then `x` is prime. -/
theorem prime_of_prime_in_localization
    (p : R) (hp_prime : Prime p) (x : R) (hx_irred : Irreducible x)
    (hax_prime : Prime (algebraMap R (Away p) x)) : Prime x := by
  have hxp_ne := hax_prime.ne_zero
  have hx_ne : x ≠ 0 := fun hx => hxp_ne (by simp [hx])
  refine ⟨hx_ne, hx_irred.not_isUnit, fun a b h => ?_⟩
  have habp : algebraMap R (Away p) (a * b) ∈ Ideal.span {algebraMap R (Away p) x} := by
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton.mpr h)
  rw [map_mul] at habp
  rw [← Ideal.span_singleton_prime hxp_ne] at hax_prime
  by_cases hpx : (p ∣ x)
  · exact (hp_prime.irreducible.associated_of_dvd hx_irred hpx).prime_iff.mp
      hp_prime |>.2.2 a b h
  exact (hax_prime.mem_or_mem habp).elim
    (Or.inl <| dvd_of_mem_span_singleton_localization hp_prime hpx ·)
    (Or.inr <| dvd_of_mem_span_singleton_localization hp_prime hpx ·)

end IsLocalization.Away
