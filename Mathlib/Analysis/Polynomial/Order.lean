/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Eventual sign of polynomials

This file proves that a polynomial has a fixed sign beyond its largest or smallest root.

## Main statements

* `zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`:
  If `x` is larger than all roots of `P` and the leading coefficient of `P` is nonnegative
  then `P (x)` is positive.
* `zero_le_eval_of_roots_le_of_leadingCoeff_nonneg`:
  If we only assume that `x` is at least as large as all roots, then `P (x)` is nonnegative.
* `eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos`,
  `eval_le_zero_of_roots_le_of_leadingCoeff_nonpos`:
  Versions of the above when the leading coefficient of `P` is nonpositive.
* `zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg`,
  `zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg`,
  `negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos`,
  `negOnePow_mul_eval_le_zero_of_le_roots_of_leadingCoeff_nonpos`:
  Analogous results for `x` which is smaller than (or at least as small as) all roots.

## TODO

Generalize to real-closed fields.
-/

public section

open Real Polynomial

namespace Polynomial

section PolynomialSign

variable {P : ℝ[X]} {x : ℝ}

theorem zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → y < x) (hlc : 0 ≤ P.leadingCoeff) : 0 < P.eval x := by
  replace hlc : 0 < P.leadingCoeff := by
    contrapose! hroots
    exact ⟨x, by simp [leadingCoeff_eq_zero.mp <| eq_of_le_of_ge hroots hlc], le_refl x⟩
  by_cases! hdeg : P.degree ≤ 0
  · rwa [eq_C_of_degree_le_zero hdeg, ← natDegree_eq_zero_iff_degree_le_zero.mpr hdeg, eval_C]
  contrapose! hroots
  obtain ⟨z, hz⟩ := Filter.Eventually.exists_forall_of_atTop <|
    (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le).eventually_gt_atTop 0
  let w := max x z
  have hw : x ≤ w ∧ 0 < P.eval w := ⟨le_max_left .., hz w (le_max_right ..)⟩
  obtain ⟨y, hy⟩ := (Set.mem_image ..).mp
    (intermediate_value_Icc hw.1 P.continuous.continuousOn (show 0 ∈ _ by grind))
  exact ⟨y, ⟨hy.2, by grind⟩⟩

theorem zero_le_eval_of_roots_le_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → y ≤ x) (hlc : 0 ≤ P.leadingCoeff) : 0 ≤ P.eval x := by
  by_cases! hroots' : ∃ y, P.IsRoot y ∧ x ≤ y
  · obtain ⟨y, hroot, hle⟩ := hroots'
    rw [eq_of_le_of_ge hle (hroots y hroot), hroot]
  · exact (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots' hlc).le

theorem eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → y < x) (hlc : P.leadingCoeff ≤ 0) : P.eval x < 0 := by
  suffices 0 < (-P).eval x by apply neg_pos.mp; rwa [← eval_neg]
  refine zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, le_neg, neg_zero]

theorem eval_le_zero_of_roots_le_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → y ≤ x) (hlc : P.leadingCoeff ≤ 0) : P.eval x ≤ 0 := by
  suffices 0 ≤ (-P).eval x by apply neg_nonneg.mp; rwa [← eval_neg]
  refine zero_le_eval_of_roots_le_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, neg_nonneg]

theorem zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → x < y) (hlc : 0 ≤ P.leadingCoeff) :
      0 < Int.negOnePow P.natDegree * P.eval x := by
  have hroots' y (hy : (P.comp (-X)).IsRoot y) : y < -x := by
    grind [show P.IsRoot (-y) by rwa [IsRoot.def, eval_comp, eval_neg, eval_X, ← IsRoot.def] at hy]
  have hlc' : 0 ≤ Int.negOnePow (P.comp (-X)).natDegree * (P.comp (-X)).leadingCoeff := by
    rw [show (P.comp (-X)).leadingCoeff = P.leadingCoeff * Int.negOnePow P.natDegree by simp; ring,
      show (P.comp (-X)).natDegree = P.natDegree by simp [natDegree_comp], mul_comm, mul_assoc]
    simpa [Int.cast_negOnePow_natCast, pow_right_comm]
  cases P.natDegree.even_or_odd
  case inl h =>
    rw [Int.negOnePow_even] at hlc' ⊢
    · push_cast at hlc' ⊢; rw [one_mul] at hlc' ⊢
      have := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots' hlc'
      simpa using this
    · simpa
    · simpa [natDegree_comp]
  case inr h =>
    rw [Int.negOnePow_odd] at hlc' ⊢
    · push_cast at hlc' ⊢; rw [neg_one_mul] at hlc' ⊢
      have := eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hroots' (nonpos_of_neg_nonneg hlc')
      exact neg_pos.mpr (by simpa using this)
    · simpa
    · simpa [natDegree_comp]

theorem zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → x ≤ y) (hlc : 0 ≤ P.leadingCoeff) :
      0 ≤ Int.negOnePow P.natDegree * P.eval x := by
  by_cases! hroots' : ∃ y, P.IsRoot y ∧ y ≤ x
  · obtain ⟨y, hroot, hle⟩ := hroots'
    rw [eq_of_ge_of_le hle (hroots y hroot), hroot, mul_zero]
  · exact (zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg hroots' hlc).le

theorem negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → x < y) (hlc : P.leadingCoeff ≤ 0) :
      Int.negOnePow P.natDegree * P.eval x < 0 := by
  suffices 0 < Int.negOnePow (-P).natDegree * (-P).eval x by apply neg_pos.mp; simpa
  refine zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, le_neg, neg_zero]

theorem negOnePow_mul_eval_le_zero_of_le_roots_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → x ≤ y) (hlc : P.leadingCoeff ≤ 0) :
      Int.negOnePow P.natDegree * P.eval x ≤ 0 := by
  suffices 0 ≤ Int.negOnePow (-P).natDegree * (-P).eval x by apply neg_nonneg.mp; simpa
  refine zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, neg_nonneg]

end PolynomialSign

end Polynomial
