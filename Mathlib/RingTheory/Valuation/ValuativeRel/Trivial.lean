/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!

# Trivial Valuative Relations

Trivial valuative relations map all non-zero elements to a valuation of 1.

## TODO

This is equivalent to the value group being isomorphic to `WithZero Unit`.

-/

namespace ValuativeRel

variable {R Γ : Type} [CommRing R] [DecidableEq R] [IsDomain R]
  [LinearOrderedCommGroupWithZero Γ]


open WithZero

/-- The trivial valuative relation on a ring `R`, such that all zero-divisors are related. -/
def trivialRel : ValuativeRel R where
  rel x y := if y = 0 then x = 0 else True
  rel_total _ _ := by split_ifs <;> simp_all
  rel_trans _ _ := by split_ifs; simp_all
  rel_add _ _ := by split_ifs; simp_all
  rel_mul_right _ := by split_ifs <;> simp_all
  rel_mul_cancel _ := by split_ifs <;> simp_all
  not_rel_one_zero := by split_ifs <;> simp_all

lemma eq_trivialRel_of_compatible_one [h : ValuativeRel R]
    [hv : Valuation.Compatible (1 : Valuation R Γ)] : h = trivialRel := by
  ext
  change _ ↔ if _ = 0 then _ else _
  rw [hv.rel_iff_le]
  split_ifs <;>
  simp_all [Valuation.one_apply_of_ne_zero, Valuation.one_apply_le_one]

lemma trivialRel_eq_ofValuation_one :
    trivialRel = .ofValuation (1 : Valuation R Γ) := by
  convert (eq_trivialRel_of_compatible_one (Γ := Γ)).symm
  exact .ofValuation 1

lemma one_apply_posSubmonoid_of_trivialRel [ValuativeRel R]
    [Valuation.Compatible (1 : Valuation R Γ)] (x : posSubmonoid R) :
    (1 : Valuation R Γ) x = 1 :=
  Valuation.one_apply_of_ne_zero (by simp)

variable (R Γ) in
lemma subsingleton_units_valueGroupWithZero_of_trivialRel [ValuativeRel R]
    [Valuation.Compatible (1 : Valuation R Γ)] :
    Subsingleton (ValueGroupWithZero R)ˣ := by
  constructor
  intro a b
  have : (valuation R).IsEquiv (1 : Valuation R Γ) := isEquiv _ _
  obtain ⟨r, s, hr⟩ := valuation_surjective_unit a
  obtain ⟨t, u, ht⟩ := valuation_surjective_unit b
  rw [Units.ext_iff, ← hr, ← ht, div_eq_div_iff, ← map_mul, ← map_mul, this.val_eq] <;>
  simp [one_apply_posSubmonoid_of_trivialRel]

lemma not_isNontrivial_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)] :
    ¬ IsNontrivial R := by
  rintro ⟨⟨x, hx, hx'⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp_all
  · simp_all [Subsingleton.elim u 1]

lemma isDiscrete_trivialRel [ValuativeRel R] [Valuation.Compatible (1 : Valuation R Γ)] :
    IsDiscrete R := by
  refine ⟨⟨0, zero_lt_one, fun x ↦ ?_⟩⟩
  have := subsingleton_units_valueGroupWithZero_of_trivialRel R Γ
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp_all
  · rw [← Units.val_one, Units.val_lt_val]
    simp

end ValuativeRel
