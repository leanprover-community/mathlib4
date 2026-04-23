/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Properties of variation

We prove basic properties of `variation` for `μ : VectorMeasure X V` in `ENormedAddCommMonoid V` on
`MeasurableSpace X`. It is defined as the supremum over partitions `{Eᵢ}` of `E`, of the quantity
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define the integral against
such vector-valued measures.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset
open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}
  [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

@[simp]
lemma variation_apply (μ : VectorMeasure X V) (s : Set X) :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/-- Measure version of `sum_le_preVariationFun_of_subset`. -/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : ∀ t ∈ P, t ⊆ s) (hP₂ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p ∈ P, ‖μ p‖ₑ ≤ μ.variation s := by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : ∀ t ∈ Q'.parts, t ⊆ s := by simp [Q', Q]; grind
  calc
    ∑ p ∈ P, ‖μ p‖ₑ = ∑ p ∈ Q.parts, ‖μ p‖ₑ :=
      (Finpartition.sum_ofPairwiseDisjoint_eq_sum hP₂ (by simp)).symm
    _ = ∑ p ∈ Q'.parts, ‖μ p‖ₑ := (Q.sum_ofSubset_eq_sum _ _ _ (by simp_all)).symm
    _ ≤ ∑ p ∈ (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
      sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ ≤ μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      simp only [sup_set_eq_biUnion, id_eq]
      exact hs.diff <| .biUnion (Finset.countable_toSet _) (by simp)

theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ ≤ variation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [μ.not_measurable' hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p ∈ (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ ≤ preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

@[simp]
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, coe_zero, Pi.zero_apply, enorm_zero]
  exact preVariation_zero

@[simp]
lemma variation_neg {V : Type*} [NormedAddCommGroup V] (μ : MeasureTheory.VectorMeasure X V) :
    (-μ).variation = μ.variation := by simp [variation]

lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ ≤ 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable' hsm

end MeasureTheory.VectorMeasure
