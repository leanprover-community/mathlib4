/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.Data.Polynomial.FieldDivision
import Mathlib.Tactic.IntervalCases

/-!
# Polynomials of specific degree

Facts about polynomials that have a specific integer degree.
-/

namespace Polynomial

variable {K : Type*} [Field K]

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
theorem irreducible_iff_roots_eq_zero_of_degree_le_three
    {p : K[X]} (hpl : 2 ≤ p.natDegree) (hp : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hpl
  have hpu : ¬ IsUnit p := p.not_isUnit_of_natDegree_pos (pos_of_gt hpl)

  -- Since the degree is at most three, the only divisors should be of degree one.
  -- (We take the contrapositive for ease of proving.)
  suffices : (∃ x, x ∣ p ∧ natDegree x = 1) ↔ ¬roots p = 0
  · rw [irreducible_iff_lt_natDegree_lt hp0 hpu, ← not_iff_not, ← this]
    have : (natDegree p) / 2 = 1
    · interval_cases natDegree p
      · rfl
      · rfl
    simp [this]
  constructor
  · rintro ⟨q, hdvd, hdeg⟩ hroots
    have hndeg := (degree_eq_iff_natDegree_eq (ne_zero_of_dvd_ne_zero hp0 hdvd)).mpr hdeg
    obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hndeg
    simpa [hroots] using (mem_roots hp0).mpr (hr.dvd hdvd)
  · intro h
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h
    exact ⟨X - C r,
      ⟨p /ₘ (X - C r), (mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mem_roots hr)).symm⟩,
      natDegree_X_sub_C _⟩

end Polynomial
