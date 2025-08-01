/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Polynomials of specific degree

Facts about polynomials that have a specific integer degree.
-/

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
    rw [← Nat.cast_one, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num)]
    exact le_antisymm (by rwa [not_le, Nat.lt_succ_iff] at hdeg2) hdeg.1

end Field

end Polynomial
