/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.Valuation.RankOne

/-!

# Discrete Valuative Relations

Discrete valuative relations have a maximal element less than one in the value group.

In the rank-one case, this is equivalent to the value group being isomorphic to `ℤᵐ⁰`.

-/

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

open WithZero

lemma nonempty_orderIso_withZeroMul_int_iff :
    Nonempty (ValueGroupWithZero R ≃*o ℤᵐ⁰) ↔
      IsDiscrete R ∧ IsNontrivial R ∧ MulArchimedean (ValueGroupWithZero R) := by
  constructor
  · rintro ⟨e⟩
    let x := e.symm (exp (-1))
    have hx0 : x ≠ 0 := by simp [x]
    have hx1 : x < 1 := by simp [- exp_neg, x, ← lt_map_inv_iff, ← exp_zero]
    refine ⟨⟨x, hx1, fun y hy ↦ ?_⟩, ⟨x, hx0, hx1.ne⟩, .comap e.toMonoidHom e.strictMono⟩
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    · rw [← map_one e.symm, ← map_inv_lt_iff, ← log_lt_log (by simp [hy0]) (by simp)] at hy
      rw [← map_inv_le_iff, ← log_le_log (by simp [hy0]) (by simp)]
      simp only [OrderMonoidIso.equivLike_inv_eq_symm, OrderMonoidIso.symm_symm, log_one,
        log_exp] at hy ⊢
      linarith
  · rintro ⟨hD, hN, hM⟩
    rw [isNontrivial_iff_nontrivial_units] at hN
    rw [LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
    intro H
    obtain ⟨x, hx, hx'⟩ := hD.has_maximal_element
    obtain ⟨y, hy, hy'⟩ := exists_between hx
    exact hy.not_ge (hx' y hy')

lemma IsDiscrete.of_compatible_withZeroMulInt (v : Valuation R ℤᵐ⁰) [v.Compatible] :
    IsDiscrete R := by
  have : IsRankLeOne R := .of_compatible_mulArchimedean v
  by_cases h : IsNontrivial R
  · by_cases H : DenselyOrdered (ValueGroupWithZero R)
    · exfalso
      refine (MonoidWithZeroHom.range_nontrivial (ValueGroupWithZero.embed v)).not_subsingleton ?_
      rw [← WithZero.denselyOrdered_set_iff_subsingleton]
      exact (ValueGroupWithZero.embed_strictMono v).denselyOrdered_range
    · rw [isNontrivial_iff_nontrivial_units] at h
      rw [← LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered] at H
      rw [nonempty_orderIso_withZeroMul_int_iff] at H
      exact H.left
  · rw [isNontrivial_iff_nontrivial_units, not_nontrivial_iff_subsingleton] at h
    refine ⟨⟨0, zero_lt_one, fun y hy ↦ ?_⟩⟩
    contrapose! hy
    have : 1 = Units.mk0 y hy.ne' := Subsingleton.elim _ _
    exact Units.val_le_val.mpr this.le

end ValuativeRel
