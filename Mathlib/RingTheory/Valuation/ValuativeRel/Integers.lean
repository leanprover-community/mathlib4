/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!

# Ring of integers for `ValuativeRel`

## Main results
- `ValuativeRel.IsIntegers`: A predicate on `[ValuativeRel R]` saying that is the `R` is the ring
  of integers.
- `ValuativeRel.isValuativeTopology_iff_isAdic`: If `R` is the ring of integers of a discrete
  rank one valuation, then the valuative topology and the adic topology coincides.

-/

variable {R : Type*} [CommRing R] [ValuativeRel R]

open Valuation Topology

namespace ValuativeRel

/--
Given a commutative `R` with a valuation `v` on `R`, `R` is the ring of integers of `v` if
`v b ≤ v a ↔ b ∣ a`.

To say that `R` is the ring of integers of `(K, v)`, one would say
`[IsFractionRing R K] [ValuativeRel R] [ValuativeExtension R K] [IsIntegers R]`
-/
class IsIntegers (R : Type*) [CommRing R] [ValuativeRel R] : Prop where
  rel_one (a : R) : a ≤ᵥ 1
  dvd_of_rel {a b : R} : a ≤ᵥ b → b ∣ a

lemma rel_iff_dvd [IsIntegers R] {a b : R} :
    a ≤ᵥ b ↔ b ∣ a := by
  refine ⟨IsIntegers.dvd_of_rel, ?_⟩
  rintro ⟨c, rfl⟩
  simpa using rel_mul_left b (IsIntegers.rel_one c)

instance (priority := 50) [IsIntegers R] : PreValuationRing R :=
  PreValuationRing.iff_dvd_total.mpr ⟨fun a b ↦ by
    simpa [rel_iff_dvd] using rel_total b a⟩

instance (priority := 50) [IsIntegers R] : Nontrivial R where
  exists_pair_ne :=
    ⟨0, 1, fun e ↦ not_rel_one_zero (R := R) (e ▸ rel_rfl)⟩

instance (priority := 50) [IsIntegers R] [IsDomain R] : ValuationRing R where

instance (priority := 50) [IsIntegers R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ((ValuationRing.valuation R K).comap (algebraMap R K)).Compatible where
  rel_iff_le x y := by
    simp_rw [rel_iff_dvd, dvd_def, @eq_comm _ x, mul_comm y]
    change _ ↔ ∃ _, _
    simp [Algebra.smul_def, ← map_mul]

lemma isUnit_iff [IsIntegers R] {x : R} :
    IsUnit x ↔ 1 ≤ᵥ x := by
  rw [isUnit_iff_dvd_one, rel_iff_dvd]

lemma mem_maximalIdeal [IsIntegers R] {x} :
    x ∈ IsLocalRing.maximalIdeal R ↔ ¬ 1 ≤ᵥ x := by
  rw [← isUnit_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

lemma IsIntegers.range_valuation [IsIntegers R] :
    Set.range (valuation R) = Set.Iic 1 := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Set.mem_Iic, ← (valuation R).map_one, ← Compatible.rel_iff_le]
    exact rel_one _
  · rintro x (hx : x ≤ 1)
    obtain ⟨a, b, rfl⟩ := valuation_surjective x
    rw [div_le_one₀ (by simp), ← Compatible.rel_iff_le, rel_iff_dvd] at hx
    obtain ⟨c, rfl⟩ := hx
    simp

lemma mem_maximalIdeal_iff_valuation_le
    [IsIntegers R] [IsDiscrete R] {x} :
    x ∈ IsLocalRing.maximalIdeal R ↔ valuation R x ≤ uniformizer R := by
  rw [le_uniformizer_iff, mem_maximalIdeal, ← (valuation R).map_one,
    lt_iff_le_not_ge, ← Compatible.rel_iff_le, ← Compatible.rel_iff_le,
    and_iff_right (IsIntegers.rel_one _)]

lemma mem_maximalIdeal_pow [IsIntegers R] [IsDiscrete R] {x n} :
    x ∈ IsLocalRing.maximalIdeal R ^ n ↔ valuation R x ≤ uniformizer R ^ n := by
  constructor
  · intro hx
    induction n generalizing x with
    | zero =>
      simp_rw [pow_zero, ← (valuation R).map_one, ← Compatible.rel_iff_le, IsIntegers.rel_one]
    | succ n IH =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) (fun y z ↦ map_add_le _)
      rw [map_mul, pow_succ]
      rw [mem_maximalIdeal_iff_valuation_le] at hz
      exact mul_le_mul (IH hy) hz zero_le' zero_le'
  · obtain ⟨ϖ, hϖ⟩ := IsIntegers.range_valuation (R := R).ge (uniformizer_lt_one.le)
    intro hx
    rw [← hϖ, ← map_pow, ← Compatible.rel_iff_le, rel_iff_dvd] at hx
    obtain ⟨x, rfl⟩ := hx
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    rw [mem_maximalIdeal_iff_valuation_le, hϖ]

open Topology in
lemma isValuativeTopology_iff_isAdic [IsIntegers R] [IsNontrivial R] [IsDiscrete R] [IsRankLeOne R]
    [TopologicalSpace R] :
    IsValuativeTopology R ↔ IsAdic (IsLocalRing.maximalIdeal R) := by
  wlog H : IsTopologicalRing R
  · constructor <;> intro h
    · cases (H inferInstance)
    · have : NonarchimedeanRing R := h ▸ (IsLocalRing.maximalIdeal R).nonarchimedean
      cases (H inferInstance)
  rw [IsValuativeTopology.iff_hasBasis_nhds_zero, isAdic_iff_hasBasis_zero]
  change _ ↔ (𝓝 0).HasBasis _ ({ x | x ∈ IsLocalRing.maximalIdeal R ^ · })
  simp_rw [mem_maximalIdeal_pow]
  refine Filter.HasBasis.to_hasBasis_iff (fun γ _ ↦ ?_) (fun n _ ↦ ?_)
  · obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one) γ
    exact ⟨n, trivial, fun x hx ↦ hx.trans_lt hn⟩
  · exact ⟨.mk0 (uniformizer R ^ n) (by simp [uniformizer_pos.ne']),
      trivial, by simp +contextual [le_of_lt]⟩

end ValuativeRel
