/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Uthaiwat, Oliver Nash
-/
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Nilpotency in polynomial rings.

This file is a place for results related to nilpotency in (single-variable) polynomial rings.

## Main results:
 * `Polynomial.isNilpotent_iff`
 * `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`

-/

namespace Polynomial

variable {R : Type _} {r : R}

section Semiring

variable [Semiring R] {P : R[X]}

lemma isNilpotent_C_mul_pow_X_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := by
  refine' Commute.isNilpotent_mul_left (commute_X_pow _ _).symm _
  -- ⊢ IsNilpotent (↑C r)
  obtain ⟨m, hm⟩ := hnil
  -- ⊢ IsNilpotent (↑C r)
  refine' ⟨m, _⟩
  -- ⊢ ↑C r ^ m = 0
  rw [← C_pow, hm, C_0]
  -- 🎉 no goals

lemma isNilpotent_pow_X_mul_C_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent (X ^ n * (C r)) := by
  rw [commute_X_pow]
  -- ⊢ IsNilpotent (↑C r * X ^ n)
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil
  -- 🎉 no goals

@[simp] lemma isNilpotent_monomial_iff {n : ℕ} :
    IsNilpotent (monomial (R := R) n r) ↔ IsNilpotent r :=
  exists_congr fun k ↦ by simp
                          -- 🎉 no goals

@[simp] lemma isNilpotent_C_iff :
    IsNilpotent (C r) ↔ IsNilpotent r :=
  exists_congr fun k ↦ by simpa only [← C_pow] using C_eq_zero
                          -- 🎉 no goals

@[simp] lemma isNilpotent_X_mul_iff :
    IsNilpotent (X * P) ↔ IsNilpotent P := by
  refine' ⟨fun h ↦ _, _⟩
  -- ⊢ IsNilpotent P
  · rwa [Commute.isNilpotent_mul_right_iff (commute_X P) (by simp)] at h
    -- 🎉 no goals
  · rintro ⟨k, hk⟩
    -- ⊢ IsNilpotent (X * P)
    exact ⟨k, by simp [(commute_X P).mul_pow, hk]⟩
    -- 🎉 no goals

@[simp] lemma isNilpotent_mul_X_iff :
    IsNilpotent (P * X) ↔ IsNilpotent P := by
  rw [← commute_X P]
  -- ⊢ IsNilpotent (X * P) ↔ IsNilpotent P
  exact isNilpotent_X_mul_iff
  -- 🎉 no goals

end Semiring

section CommRing

variable [CommRing R] {P : R[X]}

protected lemma isNilpotent_iff :
    IsNilpotent P ↔ ∀ i, IsNilpotent (coeff P i) := by
  refine' ⟨P.recOnHorner (by simp) (fun p r hp₀ _ hp hpr i ↦ _) (fun p _ hnp hpX i ↦ _), fun h ↦ _⟩
  · rw [← sum_monomial_eq P]
    -- ⊢ IsNilpotent (sum P fun n a => ↑(monomial n) a)
    exact isNilpotent_sum (fun i _ ↦ by simpa only [isNilpotent_monomial_iff] using h i)
    -- 🎉 no goals
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hpr
      replace hp : eval 0 p = 0 := by rwa [coeff_zero_eq_aeval_zero] at hp₀
      refine' isNilpotent_C_iff.mpr ⟨k, _⟩
      simpa [coeff_zero_eq_aeval_zero, hp] using congr_arg (fun q ↦ coeff q 0) hk
    cases' i with i; simpa [hp₀] using hr
    -- ⊢ IsNilpotent (coeff (p + ↑C r) Nat.zero)
                     -- ⊢ IsNilpotent (coeff (p + ↑C r) (Nat.succ i))
    simp only [coeff_add, coeff_C_succ, add_zero]
    -- ⊢ IsNilpotent (coeff p (Nat.succ i))
    apply hp
    -- ⊢ IsNilpotent p
    simpa using Commute.isNilpotent_sub (Commute.all _ _) hpr hr
    -- 🎉 no goals
  · cases' i with i; simp
    -- ⊢ IsNilpotent (coeff (p * X) Nat.zero)
                     -- ⊢ IsNilpotent (coeff (p * X) (Nat.succ i))
    simpa using hnp (isNilpotent_mul_X_iff.mp hpX) i
    -- 🎉 no goals

@[simp] lemma isNilpotent_reverse_iff :
    IsNilpotent P.reverse ↔ IsNilpotent P := by
  simp only [Polynomial.isNilpotent_iff, coeff_reverse]
  -- ⊢ (∀ (i : ℕ), IsNilpotent (coeff P (↑(revAt (natDegree P)) i))) ↔ ∀ (i : ℕ), I …
  refine' ⟨fun h i ↦ _, fun h i ↦ _⟩ <;> cases' le_or_lt i P.natDegree with hi hi
  -- ⊢ IsNilpotent (coeff P i)
                                         -- ⊢ IsNilpotent (coeff P i)
                                         -- ⊢ IsNilpotent (coeff P (↑(revAt (natDegree P)) i))
  · simpa [tsub_tsub_cancel_of_le hi] using h (P.natDegree - i)
    -- 🎉 no goals
  · simp [coeff_eq_zero_of_natDegree_lt hi]
    -- 🎉 no goals
  · simpa only [hi, revAt_le] using h (P.natDegree - i)
    -- 🎉 no goals
  · simpa only [revAt_eq_self_of_lt hi] using h i
    -- 🎉 no goals

/-- Let `P` be a polynomial over `R`. If its constant term is a unit and its other coefficients are
nilpotent, then `P` is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. -/
theorem isUnit_of_coeff_isUnit_isNilpotent (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) : IsUnit P := by
  induction' h : P.natDegree using Nat.strong_induction_on with k hind generalizing P
  -- ⊢ IsUnit P
  by_cases hdeg : P.natDegree = 0
  -- ⊢ IsUnit P
  { rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C }
  set P₁ := P.eraseLead with hP₁
  -- ⊢ IsUnit P
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P, ← C_mul_X_pow_eq_monomial]
    obtain ⟨Q, hQ⟩ := this
    rw [← hP₁, ← hQ]
    refine' Commute.IsNilpotent.add_isUnit (isNilpotent_C_mul_pow_X_of_isNilpotent _ (hnil _ hdeg))
      ((Commute.all _ _).mul_left (Commute.all _ _))
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine' hind P₁.natDegree _ _ (fun i hi => _) rfl
  · simp_rw [← h, hdeg₂]
    -- 🎉 no goals
  · simp_rw [eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
    -- 🎉 no goals
  · by_cases H : i ≤ P₁.natDegree
    -- ⊢ IsNilpotent (coeff P₁ i)
    simp_rw [eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    -- ⊢ IsNilpotent (coeff P₁ i)
    simp_rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge H), IsNilpotent.zero]
    -- 🎉 no goals

/-- Let `P` be a polynomial over `R`. If `P` is a unit, then all its coefficients are nilpotent,
except its constant term which is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. -/
theorem coeff_isUnit_isNilpotent_of_isUnit (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  -- ⊢ IsUnit (coeff P 0) ∧ ∀ (i : ℕ), i ≠ 0 → IsNilpotent (coeff P i)
  constructor
  -- ⊢ IsUnit (coeff P 0)
  · refine' isUnit_of_mul_eq_one _ (Q.coeff 0) _
    -- ⊢ coeff P 0 * coeff Q 0 = 1
    have h := (mul_coeff_zero P Q).symm
    -- ⊢ coeff P 0 * coeff Q 0 = 1
    rwa [hQ, coeff_one_zero] at h
    -- 🎉 no goals
  · intros n hn
    -- ⊢ IsNilpotent (coeff P n)
    rw [nilpotent_iff_mem_prime]
    -- ⊢ ∀ (J : Ideal R), Ideal.IsPrime J → coeff P n ∈ J
    intros I hI
    -- ⊢ coeff P n ∈ I
    let f := mapRingHom (Ideal.Quotient.mk I)
    -- ⊢ coeff P n ∈ I
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff, ← degree_mul, ← _root_.map_mul, hQ, map_one, degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine' coeff_eq_zero_of_degree_lt _
      rw [hPQ.1]
      exact (@WithBot.coe_pos _ _ _ n).2 (Ne.bot_lt hn)
    rw [coe_mapRingHom, coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at hcoeff
    -- ⊢ coeff P n ∈ I
    exact hcoeff
    -- 🎉 no goals

/-- Let `P` be a polynomial over `R`. `P` is a unit if and only if all its coefficients are
nilpotent, except its constant term which is a unit.

See also `Polynomial.isUnit_iff'`. -/
theorem isUnit_iff_coeff_isUnit_isNilpotent :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) :=
  ⟨coeff_isUnit_isNilpotent_of_isUnit, fun H => isUnit_of_coeff_isUnit_isNilpotent H.1 H.2⟩

@[simp] lemma isUnit_C_add_X_mul_iff :
    IsUnit (C r + X * P) ↔ IsUnit r ∧ IsNilpotent P := by
  have : ∀ i, coeff (C r + X * P) (i + 1) = coeff P i := by simp
  -- ⊢ IsUnit (↑C r + X * P) ↔ IsUnit r ∧ IsNilpotent P
  simp_rw [isUnit_iff_coeff_isUnit_isNilpotent, Nat.forall_ne_zero_iff, this]
  -- ⊢ (IsUnit (coeff (↑C r + X * P) 0) ∧ ∀ (i : ℕ), IsNilpotent (coeff P i)) ↔ IsU …
  simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
    and_congr_right_iff, ← Polynomial.isNilpotent_iff]

lemma isUnit_iff' :
    IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X)  := by
  suffices : P = C (eval 0 P) + X * (P /ₘ X)
  -- ⊢ IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X)
  · conv_lhs => rw [this]; simp
    -- 🎉 no goals
  conv_lhs => rw [← modByMonic_add_div P monic_X]
  -- ⊢ P %ₘ X + X * (P /ₘ X) = ↑C (eval 0 P) + X * (P /ₘ X)
  simp [modByMonic_X]
  -- 🎉 no goals

end CommRing

end Polynomial
