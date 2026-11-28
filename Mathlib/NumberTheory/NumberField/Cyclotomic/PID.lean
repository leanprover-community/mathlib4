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

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Cyclotomic fields whose ring of integers is a PID.

We prove that `ℤ [ζₚ]` is a PID for `p = 3, 5, 7, 11`. The result holds for `p ≤ 19`, but the
proof is more and more involved.

## Main results

* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
* `floor_minkowskiNormBound_seven`: If `IsCyclotomicExtension {7} ℚ K` then the integral part of
  the Minkowski bound of `K` is `4`.
* `seven_pid`: If `IsCyclotomicExtension {7} ℚ K` then `𝓞 K` is a principal ideal domain.
* `floor_minkowskiNormBound_eleven`: If `IsCyclotomicExtension {11} ℚ K` then the integral part of
  the Minkowski bound of `K` is `58`.
* `eleven_pid`: If `IsCyclotomicExtension {11} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Nat Real NumberField.RingOfIntegers Ideal Polynomial

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

section eleven

/-- `6` is a primitive `11`-th root of unity modulo `23`. -/
private lemma isPrimitiveRoot_six_zmod23 : IsPrimitiveRoot (6 : ZMod 23) 11 :=
  have : Fact (Nat.Prime 11) := ⟨prime_eleven⟩
  IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (by decide) (by decide))

/-- If `IsCyclotomicExtension {11} ℚ K` then the integral part of the Minkowski bound of `K` is
`58`. -/
theorem floor_minkowskiNormBound_eleven [IsCyclotomicExtension {11} ℚ K] :
    ⌊minkowskiNormBound K⌋₊ = 58 := by
  have : Fact (Nat.Prime 11) := ⟨prime_eleven⟩
  have : π ∈ Set.Ioo 3.1415 3.1416 := ⟨pi_gt_d4, pi_lt_d4⟩
  rw [minkowskiNormBound, floor_eq_iff (by positivity), discr_prime 11, finrank 11,
    nrComplexPlaces_eq_totient_div_two 11, totient_prime prime_eleven]
  norm_num
  field_simp
  dyadic_interval [prec := 15]

/-- For every prime `p` different from `11` and `23`, the order of `p` modulo `11` is large
enough to ensure that `58 < p ^ f`, where `f` is the inertia degree of `p` in `ℚ(ζ₁₁)`. -/
private lemma lt_pow_orderOf_eleven {p : ℕ} (hp : p.Prime) (h11 : p ≠ 11) (h23 : p ≠ 23) :
    58 < p ^ orderOf (p : ZMod 11) := by
  obtain h58 | h58 := lt_or_ge 58 p
  · -- For `58 < p` there is nothing to do, since the order is positive.
    refine h58.trans_le (Nat.le_self_pow (orderOf_pos_iff.mpr ?_).ne' p)
    exact isOfFinOrder_iff_isUnit.mpr <| (ZMod.isUnit_iff_coprime p 11).mpr <|
      (Nat.coprime_primes hp prime_eleven).mpr h11
  -- We discard the non-primes, `11` and `23`: in the other cases the order is `2`, `5` or `10`.
  interval_cases p <;> first
    | exact absurd hp (by decide)
    | contradiction
    | rw [(orderOf_eq_iff (n := 2) (by decide)).mpr (by decide)]; decide
    | rw [(orderOf_eq_iff (n := 5) (by decide)).mpr (by decide)]; decide
    | rw [(orderOf_eq_iff (n := 10) (by decide)).mpr (by decide)]; decide

variable [IsCyclotomicExtension {11} ℚ K]

/-- For a prime `p` different from `23`, there is a prime over `p` that is either principal
(this only happens for `p = 11`) or has large enough inertia degree. -/
private lemma exists_primesOver_lt_or_isPrincipal_of_ne_twentythree {p : ℕ} (hp : p.Prime)
    (h23 : p ≠ 23) : ∃ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
      ⌊minkowskiNormBound K⌋₊ < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, P.prop, ?_⟩
  obtain rfl | h11 := eq_or_ne p 11
  · -- `11` is the only ramified prime, and its prime ideal is generated by `ζ - 1`.
    exact .inr ⟨_, eq_span_zeta_sub_one_of_liesOver' 11 K (zeta_spec 11 ℚ K) P⟩
  · rw [floor_minkowskiNormBound_eleven K, inertiaDeg_eq_of_not_dvd (m := 11) p K P
      (mt (Nat.prime_dvd_prime_iff_eq hp prime_eleven).mp h11)]
    exact .inl (lt_pow_orderOf_eleven hp h11 h23)

/-- The prime ideal `(23, ζ - 6)` of `𝓞 K` over `23` is principal, generated by
`1 + ζ ^ 2 + ζ ^ 3`. -/
private lemma exists_primesOver_isPrincipal_twentythree :
    ∃ P ∈ primesOver (span {(23 : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  set θ := (zeta_spec 11 ℚ K).toInteger
  have hsum : 1 + θ + θ ^ 2 + θ ^ 3 + θ ^ 4 + θ ^ 5 + θ ^ 6 + θ ^ 7 + θ ^ 8 + θ ^ 9 +
      θ ^ 10 = 0 := by simpa [Finset.sum_range_succ] using
        (zeta_spec 11 ℚ K).toInteger_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  have hspan : span {23, θ - 6} = span {1 + θ ^ 2 + θ ^ 3} := by
    refine le_antisymm (span_le.mpr (Set.pair_subset ?_ ?_)) ((span_singleton_le_iff_mem _).mpr ?_)
    -- `1 + θ ^ 2 + θ ^ 3` divides both `23` and `θ - 6`, modulo the relation `hsum`.
    · exact mem_span_singleton.mpr ⟨9 - θ + 5 * θ ^ 2 + 6 * θ ^ 3 + 10 * θ ^ 4 + 3 * θ ^ 5 -
        2 * θ ^ 6 + θ ^ 7 + 13 * θ ^ 8 + 15 * θ ^ 9, by grind⟩
    · exact mem_span_singleton.mpr ⟨-(3 + 2 * θ ^ 2 + 2 * θ ^ 3 + 3 * θ ^ 4 + θ ^ 5 + θ ^ 7 +
        4 * θ ^ 8 + 4 * θ ^ 9), by grind⟩
    -- Conversely, `1 + X ^ 2 + X ^ 3` takes the value `253 = 11 * 23` at `6`.
    · have h := mem_span_pair_sub_of_dvd_eval θ (n := (23 : ℤ)) (a := 6)
        (g := 1 + X ^ 2 + X ^ 3) (by norm_num)
      simpa using h
  -- `6` is a primitive `11`-th root of unity mod `23`, hence a root of `Φ₁₁` mod `23`.
  have h6 : ((minpoly ℤ θ).map (Int.castRingHom (ZMod 23))).IsRoot (6 : ℤ) := by
    rw [(zeta_spec 11 ℚ K).minpoly_toInteger, map_cyclotomic_int]
    exact_mod_cast isPrimitiveRoot_six_zmod23.isRoot_cyclotomic (by norm_num)
  -- By Kummer-Dedekind, `span {23, θ - 6}` is therefore a prime ideal over `23`.
  refine ⟨_, span_sub_intCast_mem_primesOver
    ((zeta_spec 11 ℚ K).not_dvd_exponent_toInteger 23) h6, ?_⟩
  rw [Nat.cast_ofNat, Int.cast_ofNat, hspan]
  infer_instance

/-- If `IsCyclotomicExtension {11} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem eleven_pid : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := isGalois {11} ℚ K
  refine isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    fun p _ hprime ↦ ?_
  obtain rfl | h23 := eq_or_ne p 23
  · exact (exists_primesOver_isPrincipal_twentythree K).imp fun P hP ↦ ⟨hP.1, .inr hP.2⟩
  · exact exists_primesOver_lt_or_isPrincipal_of_ne_twentythree K hprime h23

end eleven

end IsCyclotomicExtension.Rat
