/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Polynomial.Basic

/-!
# Polynomials of specific degree

Facts about polynomials that have a specific integer degree.
-/

public section

namespace Polynomial

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
theorem Monic.irreducible_iff_roots_eq_zero_of_degree_le_three {p : R[X]} (hp : p.Monic)
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : p ≠ 1 := by rintro rfl; rw [natDegree_one] at hp2; cases hp2
  rw [hp.irreducible_iff_lt_natDegree_lt hp1]
  simp_rw [show p.natDegree / 2 = 1 from
      (Nat.div_le_div_right hp3).antisymm
        (by apply Nat.div_le_div_right (c := 2) hp2),
    show Finset.Ioc 0 1 = {1} from rfl,
    Finset.mem_singleton, Multiset.eq_zero_iff_forall_notMem, mem_roots hp0, ← dvd_iff_isRoot]
  refine ⟨fun h r ↦ h _ (monic_X_sub_C r) (natDegree_X_sub_C r), fun h q hq hq1 ↦ ?_⟩
  rw [hq.eq_X_add_C hq1, ← sub_neg_eq_add, ← C_neg]
  apply h

end IsDomain

section Field

variable {K : Type*} [Field K] {p : K[X]}

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
theorem irreducible_iff_roots_eq_zero_of_degree_le_three
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_roots_eq_zero_of_degree_le_three,
      mul_comm, roots_C_mul]
  · exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]

lemma irreducible_of_degree_le_three_of_not_isRoot
    (hdeg : p.natDegree ∈ Finset.Icc 1 3) (hnot : ∀ x, ¬ IsRoot p x) :
    Irreducible p := by
  rw [Finset.mem_Icc] at hdeg
  by_cases hdeg2 : 2 ≤ p.natDegree
  · rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg.2]
    apply Multiset.eq_zero_of_forall_notMem
    simp_all
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [← Nat.cast_one, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by simp)]
    exact le_antisymm (by rwa [not_le, Nat.lt_succ_iff] at hdeg2) hdeg.1

section quadratic

open UniqueFactorizationMonoid

variable {a b c : K}

/-- A quadratic is irreducible when its discriminant is not a square. -/
theorem irreducible_quadratic_of_not_isSquare_discrim (ha : a ≠ 0)
    (hs : ¬ IsSquare (discrim a b c)) :
    Irreducible (C a * X ^ 2 + C b * X + C c) := by
  have hd : (C a * X ^ 2 + C b * X + C c).natDegree = 2 := by compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hd]) ?_
  replace hs :  ∀ (s : K), discrim a b c ≠ s ^ 2 := by
    simpa [IsSquare, not_exists, ← pow_two] using hs
  simpa [IsRoot.def, pow_two] using quadratic_ne_zero_of_discrim_ne_sq hs

/-- If the discriminant is not a square, the only normalized factor is the monic quadratic. -/
theorem normalizedFactors_quadratic_of_not_isSquare_discrim [DecidableEq K] (ha : a ≠ 0)
    (hs : ¬ IsSquare (discrim a b c)) :
    normalizedFactors (C a * X ^ 2 + C b * X + C c) = {X ^ 2 + C (b * a⁻¹) * X + C (c * a⁻¹)} := by
  rw [normalizedFactors_irreducible (irreducible_quadratic_of_not_isSquare_discrim ha hs),
    normalize_apply, coe_normUnit, leadingCoeff_quadratic ha, CommGroupWithZero.coe_normUnit _ ha,
    add_mul, add_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul,
    mul_right_comm, ← map_mul, ← map_mul]

variable [NeZero (2 : K)] {s : K}

/-- If the discriminant is the square of `s`, the quadratic splits into the two linear factors
given by the quadratic formula. -/
theorem quadratic_eq_mul_of_discrim_eq_sq (ha : a ≠ 0) (h : discrim a b c = s ^ 2) :
    C a * X ^ 2 + C b * X + C c =
      C a * (X - C ((-b + s) / (2 * a))) * (X - C ((-b - s) / (2 * a))) := by
  polynomial_nf
  congr <;> field_simp; grind [discrim]

/-- If the discriminant is the square of `s`, the normalized factors are the two linear factors
given by the quadratic formula, equal to each other when `s = 0`. -/
theorem normalizedFactors_quadratic_of_discrim_eq_sq [DecidableEq K] (ha : a ≠ 0)
    (h : discrim a b c = s ^ 2) :
    normalizedFactors (C a * X ^ 2 + C b * X + C c) =
      {X - C ((-b + s) / (2 * a)), X - C ((-b - s) / (2 * a))} := by
  rw [quadratic_eq_mul_of_discrim_eq_sq ha h, normalizedFactors_mul
    (mul_ne_zero (C_ne_zero.mpr ha) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _),
    normalizedFactors_irreducible (irreducible_X_sub_C _),
    normalizedFactors_irreducible]
  · simp only [normalize_apply, coe_normUnit, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_X_sub_C, mul_one, CommGroupWithZero.coe_normUnit _ ha, normUnit_one, Units.val_one,
    map_one, Multiset.singleton_add, Multiset.insert_eq_cons, Multiset.cons_inj_left]
    rw [mul_rotate, mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, mul_one]
  · rw [irreducible_isUnit_mul (isUnit_C.mpr ha.isUnit)]
    exact irreducible_X_sub_C _

end quadratic

end Field

end Polynomial
