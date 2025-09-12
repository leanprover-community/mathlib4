/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Uthaiwat, Oliver Nash
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotency in polynomial rings.

This file is a place for results related to nilpotency in (single-variable) polynomial rings.

## Main results:
* `Polynomial.isNilpotent_iff`
* `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`

-/

namespace Polynomial

variable {R : Type*} {r : R}

section Semiring

variable [Semiring R] {P : R[X]}

lemma isNilpotent_C_mul_pow_X_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := by
  refine Commute.isNilpotent_mul_right (commute_X_pow _ _).symm ?_
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, ?_⟩
  rw [← C_pow, hm, C_0]

lemma isNilpotent_pow_X_mul_C_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent (X ^ n * (C r)) := by
  rw [commute_X_pow]
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil

@[simp] lemma isNilpotent_monomial_iff {n : ℕ} :
    IsNilpotent (monomial (R := R) n r) ↔ IsNilpotent r :=
  exists_congr fun k ↦ by simp

@[simp] lemma isNilpotent_C_iff :
    IsNilpotent (C r) ↔ IsNilpotent r :=
  exists_congr fun k ↦ by simpa only [← C_pow] using C_eq_zero

@[simp] lemma isNilpotent_X_mul_iff :
    IsNilpotent (X * P) ↔ IsNilpotent P := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rwa [Commute.isNilpotent_mul_left_iff (commute_X P) (by simp)] at h
  · rintro ⟨k, hk⟩
    exact ⟨k, by simp [(commute_X P).mul_pow, hk]⟩

@[simp] lemma isNilpotent_mul_X_iff :
    IsNilpotent (P * X) ↔ IsNilpotent P := by
  rw [← commute_X P]
  exact isNilpotent_X_mul_iff

end Semiring

section CommRing

variable [CommRing R] {P : R[X]}

protected lemma isNilpotent_iff :
    IsNilpotent P ↔ ∀ i, IsNilpotent (coeff P i) := by
  refine
    ⟨P.recOnHorner (by simp) (fun p r hp₀ _ hp hpr i ↦ ?_) (fun p _ hnp hpX i ↦ ?_), fun h ↦ ?_⟩
  · rw [← sum_monomial_eq P]
    exact isNilpotent_sum (fun i _ ↦ by simpa only [isNilpotent_monomial_iff] using h i)
  · have hr : IsNilpotent (C r) := by
      obtain ⟨k, hk⟩ := hpr
      replace hp : eval 0 p = 0 := by rwa [coeff_zero_eq_aeval_zero] at hp₀
      refine isNilpotent_C_iff.mpr ⟨k, ?_⟩
      simpa [coeff_zero_eq_aeval_zero, hp] using congr_arg (fun q ↦ coeff q 0) hk
    rcases i with - | i
    · simpa [hp₀] using hr
    simp only [coeff_add, coeff_C_succ, add_zero]
    apply hp
    simpa using Commute.isNilpotent_sub (Commute.all _ _) hpr hr
  · rcases i with - | i
    · simp
    simpa using hnp (isNilpotent_mul_X_iff.mp hpX) i

@[simp] lemma isNilpotent_reflect_iff {P : R[X]} {N : ℕ} (hN : P.natDegree ≤ N) :
    IsNilpotent (reflect N P) ↔ IsNilpotent P := by
  simp only [Polynomial.isNilpotent_iff]
  refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩ <;> rcases le_or_gt i N with hi | hi
  · simpa [tsub_tsub_cancel_of_le hi] using h (N - i)
  · simp [coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt hN hi]
  · simpa [hi, revAt_le] using h (N - i)
  · simpa [revAt_eq_self_of_lt hi] using h i

@[simp] lemma isNilpotent_reverse_iff :
    IsNilpotent P.reverse ↔ IsNilpotent P :=
  isNilpotent_reflect_iff (le_refl _)

/-- Let `P` be a polynomial over `R`. If its constant term is a unit and its other coefficients are
nilpotent, then `P` is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. -/
theorem isUnit_of_coeff_isUnit_isNilpotent (hunit : IsUnit (P.coeff 0))
    (hnil : ∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) : IsUnit P := by
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with | _ k hind
  by_cases hdeg : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    exact hunit.map C
  set P₁ := P.eraseLead with hP₁
  suffices IsUnit P₁ by
    rw [← eraseLead_add_monomial_natDegree_leadingCoeff P, ← C_mul_X_pow_eq_monomial, ← hP₁]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact isNilpotent_C_mul_pow_X_of_isNilpotent _ (hnil _ hdeg)
  have hdeg₂ := lt_of_le_of_lt P.eraseLead_natDegree_le (Nat.sub_lt
    (Nat.pos_of_ne_zero hdeg) zero_lt_one)
  refine hind P₁.natDegree ?_ ?_ (fun i hi => ?_) rfl
  · simp_rw [P₁, ← h, hdeg₂]
  · simp_rw [P₁, eraseLead_coeff_of_ne _ (Ne.symm hdeg), hunit]
  · by_cases H : i ≤ P₁.natDegree
    · simp_rw [P₁, eraseLead_coeff_of_ne _ (ne_of_lt (lt_of_le_of_lt H hdeg₂)), hnil i hi]
    · simp_rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge H), IsNilpotent.zero]

/-- Let `P` be a polynomial over `R`. If `P` is a unit, then all its coefficients are nilpotent,
except its constant term which is a unit.

See also `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`. -/
theorem coeff_isUnit_isNilpotent_of_isUnit (hunit : IsUnit P) :
    IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) := by
  obtain ⟨Q, hQ⟩ := IsUnit.exists_right_inv hunit
  constructor
  · refine isUnit_of_mul_eq_one _ (Q.coeff 0) ?_
    have h := (mul_coeff_zero P Q).symm
    rwa [hQ, coeff_one_zero] at h
  · intro n hn
    rw [nilpotent_iff_mem_prime]
    intro I hI
    let f := mapRingHom (Ideal.Quotient.mk I)
    have hPQ : degree (f P) = 0 ∧ degree (f Q) = 0 := by
      rw [← Nat.WithBot.add_eq_zero_iff, ← degree_mul, ← map_mul, hQ, map_one, degree_one]
    have hcoeff : (f P).coeff n = 0 := by
      refine coeff_eq_zero_of_degree_lt ?_
      rw [hPQ.1]
      exact WithBot.coe_pos.2 hn.bot_lt
    rw [coe_mapRingHom, coeff_map, ← RingHom.mem_ker, Ideal.mk_ker] at hcoeff
    exact hcoeff

/-- Let `P` be a polynomial over `R`. `P` is a unit if and only if all its coefficients are
nilpotent, except its constant term which is a unit.

See also `Polynomial.isUnit_iff'`. -/
theorem isUnit_iff_coeff_isUnit_isNilpotent :
    IsUnit P ↔ IsUnit (P.coeff 0) ∧ (∀ i, i ≠ 0 → IsNilpotent (P.coeff i)) :=
  ⟨coeff_isUnit_isNilpotent_of_isUnit, fun H => isUnit_of_coeff_isUnit_isNilpotent H.1 H.2⟩

@[simp] lemma isUnit_C_add_X_mul_iff :
    IsUnit (C r + X * P) ↔ IsUnit r ∧ IsNilpotent P := by
  have : ∀ i, coeff (C r + X * P) (i + 1) = coeff P i := by simp
  simp_rw [isUnit_iff_coeff_isUnit_isNilpotent, Nat.forall_ne_zero_iff, this]
  simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero,
    ← Polynomial.isNilpotent_iff]

lemma isUnit_iff' :
    IsUnit P ↔ IsUnit (eval 0 P) ∧ IsNilpotent (P /ₘ X)  := by
  suffices P = C (eval 0 P) + X * (P /ₘ X) by
    conv_lhs => rw [this]; simp
  conv_lhs => rw [← modByMonic_add_div P monic_X]
  simp [modByMonic_X]

theorem not_isUnit_of_natDegree_pos_of_isReduced [IsReduced R] (p : R[X])
    (hpl : 0 < p.natDegree) : ¬ IsUnit p := by
  simp only [ne_eq, isNilpotent_iff_eq_zero, not_and, not_forall, exists_prop,
    Polynomial.isUnit_iff_coeff_isUnit_isNilpotent]
  intro _
  refine ⟨p.natDegree, hpl.ne', ?_⟩
  contrapose! hpl
  simp only [coeff_natDegree, leadingCoeff_eq_zero] at hpl
  simp [hpl]

theorem not_isUnit_of_degree_pos_of_isReduced [IsReduced R] (p : R[X])
    (hpl : 0 < p.degree) : ¬ IsUnit p :=
  not_isUnit_of_natDegree_pos_of_isReduced _ (natDegree_pos_iff_degree_pos.mpr hpl)

end CommRing

section CommAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {a b : S}

lemma isNilpotent_aeval_sub_of_isNilpotent_sub (h : IsNilpotent (a - b)) :
    IsNilpotent (aeval a P - aeval b P) := by
  simp only [← eval_map_algebraMap]
  have ⟨c, hc⟩ := evalSubFactor (map (algebraMap R S) P) a b
  exact hc ▸ (Commute.all _ _).isNilpotent_mul_left h

variable {P}

lemma isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub
    (hb : IsUnit (aeval b P)) (hab : IsNilpotent (a - b)) :
    IsUnit (aeval a P) := by
  rw [← add_sub_cancel (aeval b P) (aeval a P)]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ hb (Commute.all _ _)
  exact isNilpotent_aeval_sub_of_isNilpotent_sub P hab

end CommAlgebra

end Polynomial
