/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Cardinality of a valued field

We show the cardinality of a valued field is at most the cardinality of the residue field
raised to the power of the cardinality of the value group.
-/

noncomputable section

universe u uK uΓ

variable {k : Type uK} [Field k]
  {Γ : Type uΓ} [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ)

/-- "Truncate" a given field element `x` at a precision `γ`. Analagous to `HahnSeries.truncLT`.
Two elements have the same truncation iff they differ by an element of valuation `≤ γ`. -/
def trunc (γ : v.ValueGroup₀) (x : k) : k :=
  (QuotientAddGroup.mk' (v.restrict.leAddSubgroup γ) x).out

theorem trunc_spec (γ : v.ValueGroup₀) (x : k) : v.restrict (x - trunc v γ x) ≤ γ := by
  unfold trunc
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_out_eq_add (v.restrict.leAddSubgroup γ) x
  rw [← v.restrict.mem_leAddSubgroup_iff, QuotientAddGroup.mk'_apply, hc, sub_add_cancel_left]
  exact neg_mem c.2

theorem trunc_eq_of_le (γ : v.ValueGroup₀) {x y : k} (hxy : v.restrict (x - y) ≤ γ) :
    trunc v γ x = trunc v γ y := by
  unfold trunc
  rw [eq_comm, Quotient.out_inj, QuotientAddGroup.mk'_eq_mk']
  exact ⟨x - y, by simpa using hxy, by simp⟩

/-- The `γ`-th "coefficient" of `x` is defined as the residue of `(x - trunc x γ) / c`,
where `c` is an arbitrarily chosen element of `k` of valuation equal to `γ`
(but the choice of `c` is made independent of `x`). Analagous to `HahnSeries.coeff`.
Two elements with the same truncation have the same coefficient
iff they differ by an element of valuation `< γ`. -/
def coeff (x : k) (γ : v.ValueGroup₀) : IsLocalRing.ResidueField v.valuationSubring :=
  IsLocalRing.residue _ ⟨(x - trunc v γ x) / (v.restrict_surjective γ).choose, by
    rw [v.mem_valuationSubring_iff, ← v.restrict_le_one_iff, map_div₀,
      (v.restrict_surjective γ).choose_spec]
    exact div_le_one_of_le₀ (trunc_spec v γ x) zero_le⟩

theorem coeff_injective : Function.Injective (coeff v) := by
  intro x y hcc
  by_contra! hxy
  rw [← sub_ne_zero, ← v.ne_zero_iff, ← v.restrict_ne_zero_iff] at hxy
  absurd congrFun hcc (v.restrict (x - y))
  unfold coeff
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.notMem_maximalIdeal,
    ValuationSubring.valuation_eq_one_iff, AddSubgroupClass.coe_sub,
    ← (v.isEquiv_valuation_valuationSubring).eq_one_iff_eq_one,
    ← sub_div, ← v.restrict_eq_one_iff, map_div₀, sub_sub_sub_comm,
    sub_eq_zero.2 (trunc_eq_of_le v (v.restrict (x - y)) le_rfl), sub_zero,
    (v.restrict_surjective (v.restrict (x - y))).choose_spec]
  exact div_self hxy

open Cardinal

public theorem Valuation.lift_cardinalMk_le_pow :
    Cardinal.lift.{uΓ} #k ≤
      Cardinal.lift.{uΓ} #(IsLocalRing.ResidueField v.valuationSubring) ^
      Cardinal.lift.{uK} #v.ValueGroup₀ := by
  rw [← Cardinal.lift_umax]
  grw [Cardinal.lift_mk_le'.2 ⟨coeff v, coeff_injective v⟩]
  simp

public theorem Valuation.cardinalMk_le_pow {k : Type u} [Field k]
    {Γ : Type u} [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) :
    #k ≤ #(IsLocalRing.ResidueField v.valuationSubring) ^ #v.ValueGroup₀ := by
  simpa using v.lift_cardinalMk_le_pow
