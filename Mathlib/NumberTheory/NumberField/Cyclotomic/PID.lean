/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Sqrt
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-!
# Cyclotomic fields whose ring of integers is a PID.

We prove that `ℤ [ζₚ]` is a PID for specific values of `p`. The result holds for `p ≤ 19`,
but the proof is more and more involved.

## Main results

* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
* `floor_minkowskiNormBound_seven`: If `IsCyclotomicExtension {7} ℚ K` then the integral part of
  the Minkowski bound of `K` is `4`.
* `seven_pid`: If `IsCyclotomicExtension {7} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Nat Real NumberField.RingOfIntegers Ideal

variable (K : Type u) [Field K] [NumberField K]

/-- If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have : 3 < π := pi_gt_three
  apply isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3, finrank 3, nrComplexPlaces_eq_totient_div_two 3, totient_prime prime_three]
  norm_num
  field_simp
  dyadic_interval

/-- If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem five_pid [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have : Fact (Nat.Prime 5) := ⟨prime_five⟩
  have : 3 < π := pi_gt_three
  apply isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 5, finrank 5, nrComplexPlaces_eq_totient_div_two 5, totient_prime prime_five]
  norm_num
  field_simp
  dyadic_interval

/-- If `IsCyclotomicExtension {7} ℚ K` then the integral part of the Minkowski bound of `K`
is `4`. -/
theorem floor_minkowskiNormBound_seven [IsCyclotomicExtension {7} ℚ K] :
    ⌊minkowskiNormBound K⌋₊ = 4 := by
  have : Fact (Nat.Prime 7) := ⟨prime_seven⟩
  have : π ∈ Set.Ioo 3 3.15 := ⟨pi_gt_three, pi_lt_d2⟩
  rw [minkowskiNormBound, floor_eq_iff (by positivity), discr_prime 7, finrank 7,
    nrComplexPlaces_eq_totient_div_two 7, totient_prime Nat.prime_seven]
  norm_num
  field_simp
  dyadic_interval [prec := 5]

/-- If `IsCyclotomicExtension {7} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem seven_pid [IsCyclotomicExtension {7} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := isGalois {7} ℚ K
  refine isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    fun p hp hprime ↦ ?_
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨P⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, P.prop, .inl ?_⟩
  rw [floor_minkowskiNormBound_seven K] at hp ⊢
  obtain ⟨hpl, hpu⟩ := Finset.mem_Icc.mp hp
  interval_cases p <;> try exact absurd hprime (by decide)
  · rw [inertiaDeg_eq_of_not_dvd (m := 7) 2 K P (by decide),
      (orderOf_eq_iff (n := 3) (by decide)).mpr (by decide)]
    decide
  · rw [inertiaDeg_eq_of_not_dvd (m := 7) 3 K P (by decide),
      (orderOf_eq_iff (n := 6) (by decide)).mpr (by decide)]
    decide

end IsCyclotomicExtension.Rat
