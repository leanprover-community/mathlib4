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

## Main statements

This file proves that a polynomial has a fixed sign beyond its largest root.

## TODO

Generalize to real-closed fields.
-/

public section

open Real Polynomial

namespace Polynomial

variable {P : ℝ[X]} {x : ℝ}
section PolynomialSign

theorem zero_lt_of_roots_lt_of_leadingCoeff_pos
    (hroots : ∀ y, P.IsRoot y → y < x) (hlc : 0 < P.leadingCoeff) : 0 < P.eval x := by
  wlog! hdeg : 0 < P.degree
  · rwa [eq_C_of_degree_le_zero hdeg, ← natDegree_eq_zero_iff_degree_le_zero.mpr hdeg, eval_C]
  contrapose! hroots
  obtain ⟨z, hz⟩ := ((P.tendsto_atTop_of_leadingCoeff_nonneg
    hdeg hlc.le).eventually_gt_atTop 0).exists_forall_of_atTop
  let w := max x z
  have hw : x ≤ w ∧ 0 < P.eval w := ⟨le_max_left .., hz w (le_max_right ..)⟩
  obtain ⟨y, hy⟩ := (Set.mem_image ..).mp
    (intermediate_value_Icc hw.1 P.continuous.continuousOn (show 0 ∈ _ by grind))
  exact ⟨y, ⟨hy.2, by grind⟩⟩

theorem zero_le_of_roots_le_of_leadingCoeff_nonneg
    (hroots : ∀ y, P.IsRoot y → y ≤ x) (hlc : 0 ≤ P.leadingCoeff) : 0 ≤ P.eval x := by
  wlog! hroots' : ∀ y, P.IsRoot y → y < x
  · obtain ⟨y, hroot, hle⟩ := hroots'
    rw [eq_of_le_of_ge hle (hroots y hroot), hroot]
  wlog! hlc' : 0 < P.leadingCoeff
  · have := eq_of_le_of_ge hlc' hlc
    have : P = 0 := by exact leadingCoeff_eq_zero.mp this
    rw [leadingCoeff_eq_zero.mp <| eq_of_le_of_ge hlc' hlc, eval_zero]
  exact (zero_lt_of_roots_lt_of_leadingCoeff_pos hroots' hlc').le

theorem lt_zero_of_roots_lt_of_leadingCoeff_neg
    (hroots : ∀ y, P.IsRoot y → y < x) (hlc : P.leadingCoeff < 0) : P.eval x < 0 := by
  suffices 0 < (-P).eval x by apply neg_pos.mp; rwa [← eval_neg]
  refine zero_lt_of_roots_lt_of_leadingCoeff_pos (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, neg_pos]

theorem le_zero_of_roots_le_of_leadingCoeff_nonpos
    (hroots : ∀ y, P.IsRoot y → y ≤ x) (hlc : P.leadingCoeff ≤ 0) : P.eval x ≤ 0 := by
  suffices 0 ≤ (-P).eval x by apply neg_nonneg.mp; rwa [← eval_neg]
  refine zero_le_of_roots_le_of_leadingCoeff_nonneg (fun y hy => hroots y ?_) ?_
  · rwa [IsRoot, ← neg_zero, ← neg_eq_iff_eq_neg, ← eval_neg]
  · rwa [leadingCoeff_neg, neg_nonneg]

end PolynomialSign

end Polynomial
