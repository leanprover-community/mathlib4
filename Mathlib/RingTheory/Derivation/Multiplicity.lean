/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Valuation.PrimeMultiplicity
import Mathlib.Algebra.Squarefree.Basic

/-!
# Multiplicity and derivations

--/

variable {M : Type*} [CommSemiring M] {F : Type*} [CommRing F] [Algebra M F]
variable [IsDomain F] [UniqueFactorizationMonoid F] (D : Derivation M F F) [Algebra ℚ F]

open Differential IsFractionRing

open AddValuation (adicValuation adicValuation_coe adicValuation_neg_iff adicValuation_pos_iff)

lemma multiplicity_deriv (p : F) (hp : Prime p) (hp2 : ¬p ∣ D p) (a : F) (h : p ∣ a) :
    emultiplicity p (D a) + 1 = emultiplicity p a := by
  by_cases ha : a = 0
  · simp [ha]
  have mf : multiplicity.Finite p a := multiplicity.finite_prime_left hp ha
  rw [mf.emultiplicity_eq_multiplicity]
  have mne0 : multiplicity p a ≠ 0 := multiplicity_ne_zero.mpr h
  obtain ⟨c, h1, h2⟩ := mf.exists_eq_pow_mul_and_not_dvd
  nth_rw 1 [h1]
  simp only [Derivation.leibniz, smul_eq_mul, nsmul_eq_mul]
  have : emultiplicity p (c * D (p ^ multiplicity p a)) = multiplicity p a - 1 := by
    simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, hp, emultiplicity_mul, h2,
      not_false_eq_true, emultiplicity_eq_zero.mpr, emultiplicity_pow_self_of_prime, ENat.coe_sub,
      Nat.cast_one, hp2, add_zero, zero_add]
    rw [emultiplicity_eq_zero.mpr, zero_add]
    refine fun nh ↦ hp.not_unit (isUnit_of_dvd_unit nh ?_)
    rw [← map_natCast (algebraMap ℚ F)]
    exact IsUnit.map _ (.mk0 _ <| mod_cast mne0)
  rw [emultiplicity_add_of_gt, this]
  · norm_cast; omega
  rw [this]
  simp only [hp, emultiplicity_mul, emultiplicity_pow_self_of_prime]
  norm_cast
  cases emultiplicity p (D c)
  · simp only [add_top, ENat.coe_lt_top]
  · norm_cast
    omega

variable [Differential F] {K : Type*} [Field K] [Algebra F K] [IsFractionRing F K]
variable [Differential K] [DifferentialAlgebra F K]

omit [Algebra ℚ F] in
lemma adicValuation_deriv_nonneg_of_nonneg (p : F) [Fact (Prime p)] (a : K)
    (ha : 0 ≤ adicValuation p a) : 0 ≤ adicValuation p a′ := by
  rw [← mk'_num_den' F a]
  simp only [Derivation.leibniz_div, inv_pow, smul_eq_mul, AddValuation.map_mul,
    AddValuation.map_inv, AddValuation.map_pow, adicValuation_coe]
  rw [← not_lt, adicValuation_neg_iff] at ha
  simp only [emultiplicity_eq_zero.mpr ha, ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero,
    smul_zero, neg_zero, zero_add, ge_iff_le]
  simp [deriv_algebraMap, ← map_mul, ← map_sub]

lemma adicValuation_deriv_lt_neg_one_of_neg (p : F) [Fact (Prime p)] (hp : ¬p ∣ p′) (a : K)
    (ha : adicValuation p a < 0) : adicValuation p a′ < -1 := by
  rw [← mk'_num_den' F a]
  simp only [Derivation.leibniz_div, inv_pow, smul_eq_mul, AddValuation.map_mul,
    AddValuation.map_inv, AddValuation.map_pow, adicValuation_coe]
  rw [adicValuation_neg_iff] at ha
  have ha2 : ¬ p ∣ num F a := Prime.not_unit Fact.out ∘ (num_den_reduced _ _).symm ha
  simp only [deriv_algebraMap, ← map_mul, ← map_sub, adicValuation_coe, gt_iff_lt]
  rw [← emultiplicity_eq_zero] at ha2
  have md := multiplicity_deriv _ p Fact.out hp _ ha
  replace mf : multiplicity.Finite p (den F a)′ := finite_iff_emultiplicity_ne_top.mpr (fun h ↦
    (multiplicity.finite_prime_left Fact.out (by simp)).emultiplicity_ne_top (h ▸ md).symm)
  rw [emultiplicity_sub_of_gt]
  · simp only [← md, mf.emultiplicity_eq_multiplicity, two_smul, neg_add_rev,
    emultiplicity_mul Fact.out, ha2, zero_add, ENat.map_coe, WithTop.coe_natCast, gt_iff_lt]
    apply WithTop.coe_strictMono
    dsimp
    omega
  · simp only [emultiplicity_mul Fact.out, ha2, zero_add, ← md]
    exact (ENat.lt_add_one_iff mf.emultiplicity_ne_top).mpr le_rfl |>.trans_le le_self_add

lemma adicValuation_deriv_ne_neg_one (p : F) [Fact (Prime p)] (hp : ¬p ∣ p′) (a : K) :
    adicValuation p a′ ≠ -1 := by
  rcases lt_or_le (adicValuation p a) 0 with ha | ha
  · exact (adicValuation_deriv_lt_neg_one_of_neg p hp a ha).ne
  · exact (by decide : ¬ 0 ≤ (-1 : WithTop ℤ)) ∘ (· ▸ adicValuation_deriv_nonneg_of_nonneg p a ha)
