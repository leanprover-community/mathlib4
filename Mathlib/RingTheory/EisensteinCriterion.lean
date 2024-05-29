/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.RingTheory.Prime
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Ideal.Quotient

#align_import ring_theory.eisenstein_criterion from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Eisenstein's criterion

A proof of a slight generalisation of Eisenstein's criterion for the irreducibility of
a polynomial over an integral domain.
-/


open Polynomial Ideal.Quotient

variable {R : Type*} [CommRing R]

namespace Polynomial

open Polynomial

namespace EisensteinCriterionAux

-- Section for auxiliary lemmas used in the proof of `irreducible_of_eisenstein_criterion`
theorem map_eq_C_mul_X_pow_of_forall_coeff_mem {f : R[X]} {P : Ideal R}
    (hfP : ∀ n : ℕ, ↑n < f.degree → f.coeff n ∈ P) :
    map (mk P) f = C ((mk P) f.leadingCoeff) * X ^ f.natDegree :=
  Polynomial.ext fun n => by
    by_cases hf0 : f = 0
    · simp [hf0]
    rcases lt_trichotomy (n : WithBot ℕ) (degree f) with (h | h | h)
    · erw [coeff_map, eq_zero_iff_mem.2 (hfP n h), coeff_C_mul, coeff_X_pow, if_neg,
        mul_zero]
      rintro rfl
      exact not_lt_of_ge degree_le_natDegree h
    · have : natDegree f = n := natDegree_eq_of_degree_eq_some h.symm
      rw [coeff_C_mul, coeff_X_pow, if_pos this.symm, mul_one, leadingCoeff, this, coeff_map]
    · rw [coeff_eq_zero_of_degree_lt, coeff_eq_zero_of_degree_lt]
      · refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
        rwa [← degree_eq_natDegree hf0]
      · exact lt_of_le_of_lt (degree_map_le _ _) h
set_option linter.uppercaseLean3 false in
#align polynomial.eisenstein_criterion_aux.map_eq_C_mul_X_pow_of_forall_coeff_mem Polynomial.EisensteinCriterionAux.map_eq_C_mul_X_pow_of_forall_coeff_mem

theorem le_natDegree_of_map_eq_mul_X_pow {n : ℕ} {P : Ideal R} (hP : P.IsPrime) {q : R[X]}
    {c : Polynomial (R ⧸ P)} (hq : map (mk P) q = c * X ^ n) (hc0 : c.degree = 0) :
    n ≤ q.natDegree :=
  Nat.cast_le.1
    (calc
      ↑n = degree (q.map (mk P)) := by
        rw [hq, degree_mul, hc0, zero_add, degree_pow, degree_X, nsmul_one]
      _ ≤ degree q := degree_map_le _ _
      _ ≤ natDegree q := degree_le_natDegree
      )
set_option linter.uppercaseLean3 false in
#align polynomial.eisenstein_criterion_aux.le_nat_degree_of_map_eq_mul_X_pow Polynomial.EisensteinCriterionAux.le_natDegree_of_map_eq_mul_X_pow

theorem eval_zero_mem_ideal_of_eq_mul_X_pow {n : ℕ} {P : Ideal R} {q : R[X]}
    {c : Polynomial (R ⧸ P)} (hq : map (mk P) q = c * X ^ n) (hn0 : n ≠ 0) : eval 0 q ∈ P := by
  rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, ← coeff_map, hq,
    coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_X, zero_pow hn0, mul_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.eisenstein_criterion_aux.eval_zero_mem_ideal_of_eq_mul_X_pow Polynomial.EisensteinCriterionAux.eval_zero_mem_ideal_of_eq_mul_X_pow

theorem isUnit_of_natDegree_eq_zero_of_isPrimitive {p q : R[X]}
    -- Porting note: stated using `IsPrimitive` which is defeq to old statement.
    (hu : IsPrimitive (p * q)) (hpm : p.natDegree = 0) : IsUnit p := by
  rw [eq_C_of_degree_le_zero (natDegree_eq_zero_iff_degree_le_zero.1 hpm), isUnit_C]
  refine hu _ ?_
  rw [← eq_C_of_degree_le_zero (natDegree_eq_zero_iff_degree_le_zero.1 hpm)]
  exact dvd_mul_right _ _
#align polynomial.eisenstein_criterion_aux.is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit Polynomial.EisensteinCriterionAux.isUnit_of_natDegree_eq_zero_of_isPrimitive

end EisensteinCriterionAux

open EisensteinCriterionAux

variable [IsDomain R]

/-- If `f` is a non constant polynomial with coefficients in `R`, and `P` is a prime ideal in `R`,
then if every coefficient in `R` except the leading coefficient is in `P`, and
the trailing coefficient is not in `P^2` and no non units in `R` divide `f`, then `f` is
irreducible. -/
theorem irreducible_of_eisenstein_criterion {f : R[X]} {P : Ideal R} (hP : P.IsPrime)
    (hfl : f.leadingCoeff ∉ P) (hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P) (hfd0 : 0 < degree f)
    (h0 : f.coeff 0 ∉ P ^ 2) (hu : f.IsPrimitive) : Irreducible f :=
  have hf0 : f ≠ 0 := fun _ => by simp_all only [not_true, Submodule.zero_mem, coeff_zero]
  have hf : f.map (mk P) = C (mk P (leadingCoeff f)) * X ^ natDegree f :=
    map_eq_C_mul_X_pow_of_forall_coeff_mem hfP
  have hfd0 : 0 < f.natDegree := WithBot.coe_lt_coe.1 (lt_of_lt_of_le hfd0 degree_le_natDegree)
  ⟨mt degree_eq_zero_of_isUnit fun h => by simp_all only [lt_irrefl], by
    rintro p q rfl
    rw [Polynomial.map_mul] at hf
    rcases mul_eq_mul_prime_pow
        (show Prime (X : Polynomial (R ⧸ P)) from monic_X.prime_of_degree_eq_one degree_X) hf with
      ⟨m, n, b, c, hmnd, hbc, hp, hq⟩
    have hmn : 0 < m → 0 < n → False := by
      intro hm0 hn0
      refine h0 ?_
      rw [coeff_zero_eq_eval_zero, eval_mul, sq]
      exact
        Ideal.mul_mem_mul (eval_zero_mem_ideal_of_eq_mul_X_pow hp hm0.ne')
          (eval_zero_mem_ideal_of_eq_mul_X_pow hq hn0.ne')
    have hpql0 : (mk P) (p * q).leadingCoeff ≠ 0 := by rwa [Ne, eq_zero_iff_mem]
    have hp0 : p ≠ 0 := fun h => by
      simp_all only [zero_mul, eq_self_iff_true, not_true, Ne]
    have hq0 : q ≠ 0 := fun h => by
      simp_all only [eq_self_iff_true, not_true, Ne, mul_zero]
    have hbc0 : degree b = 0 ∧ degree c = 0 := by
      apply_fun degree at hbc
      rwa [degree_C hpql0, degree_mul, eq_comm, Nat.WithBot.add_eq_zero_iff] at hbc
    have hmp : m ≤ natDegree p := le_natDegree_of_map_eq_mul_X_pow hP hp hbc0.1
    have hnq : n ≤ natDegree q := le_natDegree_of_map_eq_mul_X_pow hP hq hbc0.2
    have hpmqn : p.natDegree = m ∧ q.natDegree = n := by
      rw [natDegree_mul hp0 hq0] at hmnd
      contrapose hmnd
      apply ne_of_lt
      rw [not_and_or] at hmnd
      cases' hmnd with hmnd hmnd
      · exact add_lt_add_of_lt_of_le (lt_of_le_of_ne hmp (Ne.symm hmnd)) hnq
      · exact add_lt_add_of_le_of_lt hmp (lt_of_le_of_ne hnq (Ne.symm hmnd))
    obtain rfl | rfl : m = 0 ∨ n = 0 := by
      rwa [pos_iff_ne_zero, pos_iff_ne_zero, imp_false, Classical.not_not, ← or_iff_not_imp_left]
        at hmn
    · exact Or.inl (isUnit_of_natDegree_eq_zero_of_isPrimitive hu hpmqn.1)
    · exact Or.inr
          (isUnit_of_natDegree_eq_zero_of_isPrimitive
            (show IsPrimitive (q * p) by simpa [mul_comm] using hu)
            hpmqn.2)⟩
#align polynomial.irreducible_of_eisenstein_criterion Polynomial.irreducible_of_eisenstein_criterion

end Polynomial
