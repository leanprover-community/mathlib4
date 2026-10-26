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

def norm (x : k) (γ : v.ValueGroup₀) : k :=
  have hy : ∃ y, v.restrict (x - y) ≤ γ := ⟨x, by simp⟩
  hy.choose

theorem norm_spec (x : k) (γ : v.ValueGroup₀) : v.restrict (x - norm v x γ) ≤ γ :=
  have hy : ∃ y, v.restrict (x - y) ≤ γ := ⟨x, by simp⟩
  hy.choose_spec

theorem norm_eq_of_le {x y : k} (γ : v.ValueGroup₀) (hxy : v.restrict (x - y) ≤ γ) :
    norm v x γ = norm v y γ := by
  unfold norm
  dsimp only
  congr! 2 with z
  rw [← sub_add_sub_cancel x y z]
  constructor
  · intro h
    simpa using v.restrict.map_sub_le h hxy
  · intro h
    exact v.restrict.map_add_le hxy h

def coeff (x : k) (γ : v.ValueGroup₀) : IsLocalRing.ResidueField v.valuationSubring :=
  IsLocalRing.residue _ ⟨(x - norm v x γ) / (v.restrict_surjective γ).choose, by
    have hv := (v.restrict_surjective γ).choose_spec
    rw [v.mem_valuationSubring_iff, ← v.restrict_le_one_iff, map_div₀, hv]
    exact div_le_one_of_le₀ (norm_spec v x γ) zero_le⟩

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
    sub_eq_zero.2 (norm_eq_of_le v (v.restrict (x - y)) le_rfl), sub_zero,
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
