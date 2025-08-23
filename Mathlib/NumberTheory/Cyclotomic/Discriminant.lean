/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Discriminant of cyclotomic fields
We compute the discriminant of a `p ^ n`-th cyclotomic extension.

## Main results
* `IsCyclotomicExtension.discr_odd_prime` : if `p` is an odd prime such that
  `IsCyclotomicExtension {p} K L` and `Irreducible (cyclotomic p K)`, then
  `discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` for any
  `hζ : IsPrimitiveRoot ζ p`.

-/


universe u v

open Algebra Polynomial Nat IsPrimitiveRoot PowerBasis

open scoped Polynomial Cyclotomic

namespace IsPrimitiveRoot

variable {n : ℕ} [NeZero n] {K : Type u} [Field K] [CharZero K] {ζ : K}
variable [ce : IsCyclotomicExtension {n} ℚ K]

/-- The discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`. -/
theorem discr_zeta_eq_discr_zeta_sub_one (hζ : IsPrimitiveRoot ζ n) :
    discr ℚ (hζ.powerBasis ℚ).basis = discr ℚ (hζ.subOnePowerBasis ℚ).basis := by
  haveI : NumberField K := @NumberField.mk _ _ _ (IsCyclotomicExtension.finiteDimensional {n} ℚ K)
  have H₁ : (aeval (hζ.powerBasis ℚ).gen) (X - 1 : ℤ[X]) = (hζ.subOnePowerBasis ℚ).gen := by simp
  have H₂ : (aeval (hζ.subOnePowerBasis ℚ).gen) (X + 1 : ℤ[X]) = (hζ.powerBasis ℚ).gen := by simp
  refine discr_eq_discr_of_toMatrix_coeff_isIntegral _ (fun i j => toMatrix_isIntegral H₁ ?_ ?_ _ _)
    fun i j => toMatrix_isIntegral H₂ ?_ ?_ _ _
  · exact hζ.isIntegral (NeZero.pos _)
  · refine minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) (hζ.isIntegral (NeZero.pos _))
  · exact (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one
  · refine minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) ?_
    exact (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {p : ℕ} {k : ℕ} {K : Type u} {L : Type v} {ζ : L} [Field K] [Field L]
variable [Algebra K L]

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ (k + 1).totient) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
theorem discr_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K))
    (hk : p ^ (k + 1) ≠ 2) : discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  haveI hne := IsCyclotomicExtension.neZero' (p ^ (k + 1)) K L
  haveI mf : Module.Finite K L := finiteDimensional {p ^ (k + 1)} K L
  haveI se : Algebra.IsSeparable K L := isSeparable {p ^ (k + 1)} K L
  rw [discr_powerBasis_eq_norm, finrank L hirr, hζ.powerBasis_gen _,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, totient_prime_pow hp.out (succ_pos k),
    Nat.add_one_sub_one]
  have hp2 : p = 2 → k ≠ 0 := by
    rintro rfl rfl
    exact absurd rfl hk
  congr 1
  · rcases eq_or_ne p 2 with (rfl | hp2)
    · rcases Nat.exists_eq_succ_of_ne_zero (hp2 rfl) with ⟨k, rfl⟩
      rw [succ_sub_succ_eq_sub, tsub_zero, mul_one]; simp only [_root_.pow_succ']
      rw [mul_assoc, Nat.mul_div_cancel_left _ zero_lt_two, Nat.mul_div_cancel_left _ zero_lt_two]
      cases k
      · simp
      · simp_rw [_root_.pow_succ', (even_two.mul_right _).neg_one_pow,
          ((even_two.mul_right _).mul_right _).neg_one_pow]
    · have hpo : Odd p := hp.out.odd_of_ne_two hp2
      obtain ⟨a, ha⟩ := (hp.out.even_sub_one hp2).two_dvd
      rw [ha, mul_left_comm, mul_assoc, Nat.mul_div_cancel_left _ two_pos,
        Nat.mul_div_cancel_left _ two_pos, mul_right_comm, pow_mul, (hpo.pow.mul _).neg_one_pow,
        pow_mul, hpo.pow.neg_one_pow]
      refine Nat.Even.sub_odd ?_ (even_two_mul _) odd_one
      rw [mul_left_comm, ← ha]
      exact one_le_mul (one_le_pow _ _ hp.1.pos) (succ_le_iff.2 <| tsub_pos_of_lt hp.1.one_lt)
  · have H := congr_arg (@derivative K _) (cyclotomic_prime_pow_mul_X_pow_sub_one K p k)
    rw [derivative_mul, derivative_sub, derivative_one, sub_zero, derivative_X_pow, C_eq_natCast,
      derivative_sub, derivative_one, sub_zero, derivative_X_pow, C_eq_natCast,
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H
    replace H := congr_arg (fun P => aeval ζ P) H
    simp only [aeval_add, aeval_mul, minpoly.aeval, zero_mul, add_zero, aeval_natCast,
      map_sub, aeval_one, aeval_X_pow] at H
    replace H := congr_arg (Algebra.norm K) H
    have hnorm : (norm K) (ζ ^ p ^ k - 1) = (p : K) ^ p ^ k := by
      by_cases hp : p = 2
      · exact mod_cast hζ.norm_pow_sub_one_eq_prime_pow_of_ne_zero hirr le_rfl (hp2 hp)
      · exact mod_cast hζ.norm_pow_sub_one_of_prime_ne_two hirr le_rfl hp
    rw [MonoidHom.map_mul, hnorm, MonoidHom.map_mul, ← map_natCast (algebraMap K L),
      Algebra.norm_algebraMap, finrank L hirr, ← succ_eq_add_one,
      totient_prime_pow hp.out (succ_pos k), Nat.sub_one, Nat.pred_succ] at H
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_pow, hζ.norm_eq_one hk hirr, one_pow,
      mul_one, cast_pow, ← pow_mul, ← mul_assoc, mul_comm (k + 1), mul_assoc] at H
    have := mul_pos (succ_pos k) (tsub_pos_of_lt hp.out.one_lt)
    rw [← succ_pred_eq_of_pos this, mul_succ, pow_add _ _ (p ^ k)] at H
    replace H := (mul_left_inj' fun h => ?_).1 H
    · simp only [H, mul_comm _ (k + 1)]; norm_cast
    · have := hne.1
      rw [Nat.cast_pow, Ne, pow_eq_zero_iff (by omega)] at this
      exact absurd (pow_eq_zero h) this

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K))
    (hk : p ^ (k + 1) ≠ 2) : discr K (hζ.powerBasis K).basis =
      (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow_ne_two hζ hirr hk

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1))`
if `Irreducible (cyclotomic (p ^ k) K))`. Beware that in the cases `p ^ k = 1` and `p ^ k = 2`
the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform result.
See also `IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow`. -/
theorem discr_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hirr : Irreducible (cyclotomic (p ^ k) K)) :
    discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  rcases k with - | k
  · simp only [coe_basis, _root_.pow_zero, powerBasis_gen _ hζ, totient_one, mul_zero,
      show 1 / 2 = 0 by rfl, discr, traceMatrix]
    have hζone : ζ = 1 := by simpa using hζ
    rw [hζ.powerBasis_dim _, hζone, ← (algebraMap K L).map_one,
      minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective, natDegree_X_sub_C]
    simp only [map_one, one_pow, Matrix.det_unique, traceForm_apply, mul_one]
    rw [← (algebraMap K L).map_one, trace_algebraMap, finrank _ hirr]
    norm_num
  · by_cases hk : p ^ (k + 1) = 2
    · obtain rfl : p = 2 := by
        rw [← pow_one 2] at hk
        exact eq_of_prime_pow_eq (prime_iff.1 hp.out) (prime_iff.1 Nat.prime_two) (succ_pos _) hk
      nth_rw 2 [← pow_one 2] at hk
      replace hk := Nat.pow_right_injective rfl.le hk
      rw [add_eq_right] at hk
      subst hk
      rw [pow_one] at hζ hcycl
      have : natDegree (minpoly K ζ) = 1 := by
        rw [hζ.eq_neg_one_of_two_right, show (-1 : L) = algebraMap K L (-1) by simp,
          minpoly.eq_X_sub_C_of_algebraMap_inj _ (FaithfulSMul.algebraMap_injective K L)]
        exact natDegree_X_sub_C (-1)
      rcases Fin.equiv_iff_eq.2 this with ⟨e⟩
      rw [← Algebra.discr_reindex K (hζ.powerBasis K).basis e, coe_basis, powerBasis_gen]; norm_num
      simp_rw [hζ.eq_neg_one_of_two_right, show (-1 : L) = algebraMap K L (-1) by simp]
      convert_to (discr K fun i : Fin 1 ↦ (algebraMap K L) (-1) ^ ↑i) = _
      · congr 1
        ext i
        simp only [map_neg, map_one, Function.comp_apply, Fin.val_eq_zero, _root_.pow_zero]
        suffices (e.symm i : ℕ) = 0 by simp [this]
        rw [← Nat.lt_one_iff]
        convert (e.symm i).2
        rw [this]
      · simp only [discr, traceMatrix_apply, Matrix.det_unique, Fin.default_eq_zero, Fin.val_zero,
          _root_.pow_zero, traceForm_apply, mul_one]
        rw [← (algebraMap K L).map_one, trace_algebraMap, finrank _ hirr]; norm_num
    · exact discr_prime_pow_ne_two hζ hirr hk

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of `hζ.powerBasis K` is `u * p ^ n`. Often this is enough and
less cumbersome to use than `IsCyclotomicExtension.discr_prime_pow`. -/
theorem discr_prime_pow_eq_unit_mul_pow [IsCyclotomicExtension {p ^ k} K L]
    [hp : Fact p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ k))
    (hirr : Irreducible (cyclotomic (p ^ k) K)) :
    ∃ (u : ℤˣ) (n : ℕ), discr K (hζ.powerBasis K).basis = u * p ^ n := by
  rw [discr_prime_pow hζ hirr]
  by_cases heven : Even ((p ^ k).totient / 2)
  · exact ⟨1, p ^ (k - 1) * ((p - 1) * k - 1), by rw [heven.neg_one_pow]; norm_num⟩
  · exact ⟨-1, p ^ (k - 1) * ((p - 1) * k - 1), by
      rw [(not_even_iff_odd.1 heven).neg_one_pow]; norm_num⟩

/-- If `p` is an odd prime and `IsCyclotomicExtension {p} K L`, then
`discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` if
`Irreducible (cyclotomic p K)`. -/
theorem discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
    discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by
    rw [zero_add, pow_one]
    infer_instance
  have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  convert discr_prime_pow_ne_two hζ' (by simpa [hirr]) (by simp [hodd]) using 2
  · rw [zero_add, pow_one, totient_prime hp.out]
  · rw [_root_.pow_zero, one_mul, zero_add, mul_one, Nat.sub_sub]

end IsCyclotomicExtension
