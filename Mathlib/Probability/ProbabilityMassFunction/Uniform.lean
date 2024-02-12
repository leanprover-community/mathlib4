/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions

#align_import probability.probability_mass_function.uniform from "leanprover-community/mathlib"@"e50b8c261b0a000b806ec0e1356b41945eda61f7"

/-!
# Uniform Probability Mass Functions

This file defines a number of uniform `PMF` distributions from various inputs,
  uniformly drawing from the corresponding object.

`PMF.uniformOfFinset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`PMF.uniformOfFintype` gives all elements equal probability,
  equal to the inverse of the size of the `Fintype`.

`PMF.ofMultiset` draws randomly from the given `Multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `Multiset`

-/

noncomputable section

namespace PMF

variable {α β γ : Type*}

open scoped Classical BigOperators NNReal ENNReal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  refine' ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s _ _
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne.def, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    refine' ENNReal.mul_inv_cancel this <| ENNReal.nat_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]
#align pmf.uniform_of_finset PMF.uniformOfFinset

variable {s : Finset α} (hs : s.Nonempty) {a : α}

@[simp]
theorem uniformOfFinset_apply (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl
#align pmf.uniform_of_finset_apply PMF.uniformOfFinset_apply

theorem uniformOfFinset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]
#align pmf.uniform_of_finset_apply_of_mem PMF.uniformOfFinset_apply_of_mem

theorem uniformOfFinset_apply_of_not_mem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]
#align pmf.uniform_of_finset_apply_of_not_mem PMF.uniformOfFinset_apply_of_not_mem

@[simp]
theorem support_uniformOfFinset : (uniformOfFinset s hs).support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff, Finset.ne_empty_of_mem ha])
#align pmf.support_uniform_of_finset PMF.support_uniformOfFinset

theorem mem_support_uniformOfFinset_iff (a : α) : a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  simp
#align pmf.mem_support_uniform_of_finset_iff PMF.mem_support_uniformOfFinset_iff

section Measure

variable (t : Set α)

@[simp]
theorem toOuterMeasure_uniformOfFinset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = (s.filter (· ∈ t)).card / s.card :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :=
      (tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_comm])
    _ = ∑ x in s.filter (· ∈ t), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :=
      (tsum_eq_sum fun x hx => if_neg fun h => hx (Finset.mem_filter.2 h))
    _ = ∑ _x in s.filter (· ∈ t), (s.card : ℝ≥0∞)⁻¹ :=
      (Finset.sum_congr rfl fun x hx => by
        let this : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true])
    _ = (s.filter (· ∈ t)).card / s.card := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

#align pmf.to_outer_measure_uniform_of_finset_apply PMF.toOuterMeasure_uniformOfFinset_apply

@[simp]
theorem toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = (s.filter (· ∈ t)).card / s.card :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)
#align pmf.to_measure_uniform_of_finset_apply PMF.toMeasure_uniformOfFinset_apply

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty
#align pmf.uniform_of_fintype PMF.uniformOfFintype

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, if_true, uniformOfFinset_apply]
  rfl
#align pmf.uniform_of_fintype_apply PMF.uniformOfFintype_apply

@[simp]
theorem support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]
#align pmf.support_uniform_of_fintype PMF.support_uniformOfFintype

theorem mem_support_uniformOfFintype (a : α) : a ∈ (uniformOfFintype α).support := by simp
#align pmf.mem_support_uniform_of_fintype PMF.mem_support_uniformOfFintype

section Measure

variable (s : Set α)

theorem toOuterMeasure_uniformOfFintype_apply :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  rw [uniformOfFintype, toOuterMeasure_uniformOfFinset_apply,Fintype.card_ofFinset]
  rfl
#align pmf.to_outer_measure_uniform_of_fintype_apply PMF.toOuterMeasure_uniformOfFintype_apply

theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  simp [uniformOfFintype, hs]
  rfl
#align pmf.to_measure_uniform_of_fintype_apply PMF.toMeasure_uniformOfFintype_apply

end Measure

end UniformOfFintype

section OfMultiset

/-- Given a non-empty multiset `s` we construct the `PMF` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def ofMultiset (s : Multiset α) (hs : s ≠ 0) : PMF α :=
  ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : ℝ≥0∞) / (Multiset.card s))
          = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑' b, (s.count b : ℝ≥0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
        _ = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑ b in s.toFinset, (s.count b : ℝ≥0∞) :=
          (congr_arg (fun x => (Multiset.card s : ℝ≥0∞)⁻¹ * x)
            (tsum_eq_sum fun a ha =>
              Nat.cast_eq_zero.2 <| by rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]))
        _ = 1 := by
          rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq s,
            ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (ENNReal.nat_ne_top _)]
        )⟩
#align pmf.of_multiset PMF.ofMultiset

variable {s : Multiset α} (hs : s ≠ 0)

@[simp]
theorem ofMultiset_apply (a : α) : ofMultiset s hs a = s.count a / (Multiset.card s) :=
  rfl
#align pmf.of_multiset_apply PMF.ofMultiset_apply

@[simp]
theorem support_ofMultiset : (ofMultiset s hs).support = s.toFinset :=
  Set.ext (by simp [mem_support_iff, hs])
#align pmf.support_of_multiset PMF.support_ofMultiset

theorem mem_support_ofMultiset_iff (a : α) : a ∈ (ofMultiset s hs).support ↔ a ∈ s.toFinset := by
  simp
#align pmf.mem_support_of_multiset_iff PMF.mem_support_ofMultiset_iff

theorem ofMultiset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0 := by
  simpa only [ofMultiset_apply, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    ENNReal.nat_ne_top, or_false_iff] using ha
#align pmf.of_multiset_apply_of_not_mem PMF.ofMultiset_apply_of_not_mem

section Measure

variable (t : Set α)

@[simp]
theorem toOuterMeasure_ofMultiset_apply :
    (ofMultiset s hs).toOuterMeasure t =
      (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) := by
  simp_rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, toOuterMeasure_apply]
  refine' tsum_congr fun x => _
  by_cases hx : x ∈ t <;> simp [Set.indicator, hx, div_eq_mul_inv]
#align pmf.to_outer_measure_of_multiset_apply PMF.toOuterMeasure_ofMultiset_apply

@[simp]
theorem toMeasure_ofMultiset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset s hs).toMeasure t = (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofMultiset_apply hs t)
#align pmf.to_measure_of_multiset_apply PMF.toMeasure_ofMultiset_apply

end Measure

end OfMultiset

end PMF
