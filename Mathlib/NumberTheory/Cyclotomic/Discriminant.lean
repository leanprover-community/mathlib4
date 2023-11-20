/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Discriminant

#align_import number_theory.cyclotomic.discriminant from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

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

variable {n : ℕ+} {K : Type u} [Field K] [CharZero K] {ζ : K}

variable [ce : IsCyclotomicExtension {n} ℚ K]

/-- The discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`. -/
theorem discr_zeta_eq_discr_zeta_sub_one (hζ : IsPrimitiveRoot ζ n) :
    discr ℚ (hζ.powerBasis ℚ).basis = discr ℚ (hζ.subOnePowerBasis ℚ).basis := by
  haveI : NumberField K := @NumberField.mk _ _ _ (IsCyclotomicExtension.finiteDimensional {n} ℚ K)
  have H₁ : (aeval (hζ.powerBasis ℚ).gen) (X - 1 : ℤ[X]) = (hζ.subOnePowerBasis ℚ).gen := by simp
  have H₂ : (aeval (hζ.subOnePowerBasis ℚ).gen) (X + 1 : ℤ[X]) = (hζ.powerBasis ℚ).gen := by simp
  refine' discr_eq_discr_of_toMatrix_coeff_isIntegral _ (fun i j => toMatrix_isIntegral H₁ _ _ _ _)
    fun i j => toMatrix_isIntegral H₂ _ _ _ _
  · exact hζ.isIntegral n.pos
  · refine' minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) (hζ.isIntegral n.pos)
  · exact (hζ.isIntegral n.pos).sub isIntegral_one
  · refine' minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) _
    exact (hζ.isIntegral n.pos).sub isIntegral_one
#align is_primitive_root.discr_zeta_eq_discr_zeta_sub_one IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {p : ℕ+} {k : ℕ} {K : Type u} {L : Type v} {ζ : L} [Field K] [Field L]

variable [Algebra K L]

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ (k + 1).totient) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
theorem discr_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
    (hk : p ^ (k + 1) ≠ 2) : discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p ^ (k + 1) : ℕ).totient / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) := by
  haveI hne := IsCyclotomicExtension.neZero' (p ^ (k + 1)) K L
  -- Porting note: these two instances are not automatically synthesised and must be constructed
  haveI mf : Module.Finite K L := finiteDimensional {p ^ (k + 1)} K L
  haveI se : IsSeparable K L := (isGalois (p ^ (k + 1)) K L).to_isSeparable
  rw [discr_powerBasis_eq_norm, finrank L hirr, hζ.powerBasis_gen _, ←
    hζ.minpoly_eq_cyclotomic_of_irreducible hirr, PNat.pow_coe,
    totient_prime_pow hp.out (succ_pos k), succ_sub_one]
  have coe_two : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hp2 : p = 2 → k ≠ 0 := by
    rintro rfl rfl
    exact absurd rfl hk
  congr 1
  · rcases eq_or_ne p 2 with (rfl | hp2)
    · rcases Nat.exists_eq_succ_of_ne_zero (hp2 rfl) with ⟨k, rfl⟩
      rw [coe_two, succ_sub_succ_eq_sub, tsub_zero, mul_one]; simp only [_root_.pow_succ]
      rw [mul_assoc, Nat.mul_div_cancel_left _ zero_lt_two, Nat.mul_div_cancel_left _ zero_lt_two]
      cases k
      · simp
      · norm_num; simp_rw [_root_.pow_succ, (even_two.mul_right _).neg_one_pow,
          ((even_two.mul_right _).mul_right _).neg_one_pow]
    · replace hp2 : (p : ℕ) ≠ 2
      · rwa [Ne.def, ← coe_two, PNat.coe_inj]
      have hpo : Odd (p : ℕ) := hp.out.odd_of_ne_two hp2
      obtain ⟨a, ha⟩ := (hp.out.even_sub_one hp2).two_dvd
      rw [ha, mul_left_comm, mul_assoc, Nat.mul_div_cancel_left _ two_pos,
        Nat.mul_div_cancel_left _ two_pos, mul_right_comm, pow_mul, (hpo.pow.mul _).neg_one_pow,
        pow_mul, hpo.pow.neg_one_pow]
      refine' Nat.Even.sub_odd _ (even_two_mul _) odd_one
      rw [mul_left_comm, ← ha]
      exact one_le_mul (one_le_pow _ _ hp.1.pos) (succ_le_iff.2 <| tsub_pos_of_lt hp.1.one_lt)
  · have H := congr_arg (@derivative K _) (cyclotomic_prime_pow_mul_X_pow_sub_one K p k)
    rw [derivative_mul, derivative_sub, derivative_one, sub_zero, derivative_X_pow, C_eq_nat_cast,
      derivative_sub, derivative_one, sub_zero, derivative_X_pow, C_eq_nat_cast, ← PNat.pow_coe,
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H
    replace H := congr_arg (fun P => aeval ζ P) H
    simp only [aeval_add, aeval_mul, minpoly.aeval, zero_mul, add_zero, aeval_nat_cast,
      _root_.map_sub, aeval_one, aeval_X_pow] at H
    replace H := congr_arg (Algebra.norm K) H
    have hnorm : (norm K) (ζ ^ (p : ℕ) ^ k - 1) = (p : K) ^ (p : ℕ) ^ k := by
      by_cases hp : p = 2
      · exact mod_cast hζ.pow_sub_one_norm_prime_pow_of_ne_zero hirr le_rfl (hp2 hp)
      · exact mod_cast hζ.pow_sub_one_norm_prime_ne_two hirr le_rfl hp
    rw [MonoidHom.map_mul, hnorm, MonoidHom.map_mul, ← map_natCast (algebraMap K L),
      Algebra.norm_algebraMap, finrank L hirr] at H
    conv_rhs at H => -- Porting note: need to drill down to successfully rewrite the totient
      enter [1, 2]
      rw [PNat.pow_coe, ← succ_eq_add_one, totient_prime_pow hp.out (succ_pos k), Nat.sub_one,
        Nat.pred_succ]
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_pow, hζ.norm_eq_one hk hirr, one_pow,
      mul_one, PNat.pow_coe, cast_pow, ← pow_mul, ← mul_assoc, mul_comm (k + 1), mul_assoc] at H
    have := mul_pos (succ_pos k) (tsub_pos_of_lt hp.out.one_lt)
    rw [← succ_pred_eq_of_pos this, mul_succ, pow_add _ _ ((p : ℕ) ^ k)] at H
    replace H := (mul_left_inj' fun h => ?_).1 H
    · simp only [H, mul_comm _ (k + 1)]; norm_cast
    · -- Porting note: was `replace h := pow_eq_zero h; rw [coe_coe] at h; simpa using hne.1`
      have := hne.1
      rw [PNat.pow_coe, Nat.cast_pow, Ne.def, pow_eq_zero_iff (by linarith)] at this
      exact absurd (pow_eq_zero h) this
#align is_cyclotomic_extension.discr_prime_pow_ne_two IsCyclotomicExtension.discr_prime_pow_ne_two

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
    (hk : p ^ (k + 1) ≠ 2) : discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p : ℕ) ^ k * (p - 1) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
  by simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow_ne_two hζ hirr hk
#align is_cyclotomic_extension.discr_prime_pow_ne_two' IsCyclotomicExtension.discr_prime_pow_ne_two'

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1))`
if `Irreducible (cyclotomic (p ^ k) K))`. Beware that in the cases `p ^ k = 1` and `p ^ k = 2`
the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform result.
See also `IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow`. -/
theorem discr_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ k)) (hirr : Irreducible (cyclotomic (↑(p ^ k) : ℕ) K)) :
    discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p ^ k : ℕ).totient / 2) * p ^ ((p : ℕ) ^ (k - 1) * ((p - 1) * k - 1)) := by
  cases' k with k k
  · simp only [coe_basis, _root_.pow_zero, powerBasis_gen _ hζ, totient_one, mul_zero, mul_one,
      show 1 / 2 = 0 by rfl, discr, traceMatrix]
    have hζone : ζ = 1 := by simpa using hζ
    rw [hζ.powerBasis_dim _, hζone, ← (algebraMap K L).map_one,
      minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective, natDegree_X_sub_C]
    simp only [traceMatrix, map_one, one_pow, Matrix.det_unique, traceForm_apply, mul_one]
    rw [← (algebraMap K L).map_one, trace_algebraMap, finrank _ hirr]
    norm_num
  · by_cases hk : p ^ (k + 1) = 2
    · have coe_two : 2 = ((2 : ℕ+) : ℕ) := rfl
      have hp : p = 2 := by
        rw [← PNat.coe_inj, PNat.pow_coe, ← pow_one 2] at hk
        replace hk :=
          eq_of_prime_pow_eq (prime_iff.1 hp.out) (prime_iff.1 Nat.prime_two) (succ_pos _) hk
        rwa [coe_two, PNat.coe_inj] at hk
      rw [hp, ← PNat.coe_inj, PNat.pow_coe] at hk
      nth_rw 2 [← pow_one 2] at hk
      replace hk := Nat.pow_right_injective rfl.le hk
      rw [add_left_eq_self] at hk
      rw [hp, hk] at hζ; norm_num at hζ; rw [← coe_two] at hζ
      rw [coe_basis, powerBasis_gen]; simp only [hp, hk]; norm_num
      -- Porting note: the goal at this point is `(discr K fun i ↦ ζ ^ ↑i) = 1`.
      -- This `simp_rw` is needed so the next `rw` can rewrite the type of `i` from
      -- `Fin (natDegree (minpoly K ζ))` to `Fin 1`
      simp_rw [hζ.eq_neg_one_of_two_right, show (-1 : L) = algebraMap K L (-1) by simp]
      rw [hζ.eq_neg_one_of_two_right, show (-1 : L) = algebraMap K L (-1) by simp,
        minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective, natDegree_X_sub_C]
      simp only [discr, traceMatrix_apply, Matrix.det_unique, Fin.default_eq_zero, Fin.val_zero,
        _root_.pow_zero, traceForm_apply, mul_one]
      rw [← (algebraMap K L).map_one, trace_algebraMap, finrank _ hirr, hp, hk]; norm_num
      simp [← coe_two, Even.neg_pow (by decide : Even (1 / 2))]
    · exact discr_prime_pow_ne_two hζ hirr hk
#align is_cyclotomic_extension.discr_prime_pow IsCyclotomicExtension.discr_prime_pow

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of `hζ.powerBasis K` is `u * p ^ n`. Often this is enough and
less cumbersome to use than `IsCyclotomicExtension.discr_prime_pow`. -/
theorem discr_prime_pow_eq_unit_mul_pow [IsCyclotomicExtension {p ^ k} K L]
    [hp : Fact (p : ℕ).Prime] (hζ : IsPrimitiveRoot ζ ↑(p ^ k))
    (hirr : Irreducible (cyclotomic (↑(p ^ k) : ℕ) K)) :
    ∃ (u : ℤˣ) (n : ℕ), discr K (hζ.powerBasis K).basis = u * p ^ n := by
  rw [discr_prime_pow hζ hirr]
  by_cases heven : Even ((p ^ k : ℕ).totient / 2)
  · refine' ⟨1, (p : ℕ) ^ (k - 1) * ((p - 1) * k - 1), by rw [heven.neg_one_pow]; norm_num⟩
  · exact ⟨-1, (p : ℕ) ^ (k - 1) * ((p - 1) * k - 1), by
      rw [(odd_iff_not_even.2 heven).neg_one_pow]; norm_num⟩
#align is_cyclotomic_extension.discr_prime_pow_eq_unit_mul_pow IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow

/-- If `p` is an odd prime and `IsCyclotomicExtension {p} K L`, then
`discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` if
`Irreducible (cyclotomic p K)`. -/
theorem discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact (p : ℕ).Prime]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
    discr K (hζ.powerBasis K).basis = (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by
    rw [zero_add, pow_one]
    infer_instance
  have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1) :) := by simpa using hζ
  convert discr_prime_pow_ne_two hζ' (by simpa [hirr]) (by simp [hodd]) using 2
  · rw [zero_add, pow_one, totient_prime hp.out]
  · rw [_root_.pow_zero, one_mul, zero_add, mul_one, Nat.sub_sub]
#align is_cyclotomic_extension.discr_odd_prime IsCyclotomicExtension.discr_odd_prime

end IsCyclotomicExtension
