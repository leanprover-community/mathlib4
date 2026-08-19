/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Parker
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Krylov-Bogolyubov theorem

The Krylov–Bogolyubov theorem asserts the existence of invariant Borel probability measures
for continuous dynamics on compact metrizable spaces.

## Main results

- `exists_measurePreserving_probabilityMeasure`: the Krylov-Bogolyubov theorem.

## Implementation notes

In order to minimise public imports, the details of the proof are contained in private lemmas.
We define a sequence of empirical orbit measures for the system starting from a given point,
and show that the cluster points of this sequence give an invariant measure if the space is compact.

We do not assume that the space is metrizable; it is sufficient to assume `HasOuterApproxClosed`
and `T2Space`.
-/

namespace MeasureTheory

open Filter
open scoped BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X]

noncomputable def orbitMeasure (f : X → X) (x : X) (n : ℕ) : ProbabilityMeasure X :=
  ⟨(n + 1 : ENNReal)⁻¹ • ∑ k ∈ Finset.range (n + 1), Measure.dirac (f^[k] x),
    ⟨by simp [ENNReal.inv_mul_cancel]⟩⟩

section Integrals

variable [TopologicalSpace X] [BorelSpace X] [T2Space X]
variable (f : X → X) (g : X →ᵇ ℝ) (x : X)

lemma integral_orbitMeasure (n : ℕ) :
    ∫ y, g y ∂(orbitMeasure f x n : Measure X) =
      (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g (f^[k] x) := by
  simp only [orbitMeasure, ProbabilityMeasure.coe_mk, integral_smul_measure,
    ENNReal.toReal_inv]
  have h : ∀ k ∈ Finset.range (n + 1), Integrable g (Measure.dirac (f^[k] x)) := by
    simp [BoundedContinuousFunction.integrable]
  rw [integral_finsetSum_measure h]
  congr
  simp

lemma integral_comp_sub_integral_orbitMeasure (n : ℕ) (hf : Continuous f) :
    (∫ y, g (f y) ∂(orbitMeasure f x n)) - ∫ y, g y ∂(orbitMeasure f x n) =
        (n + 1 : ℝ)⁻¹ * (g (f^[n + 1] x) - g x) := by
  change (∫ (y : X), (g.compContinuous ⟨f, hf⟩) y ∂↑(orbitMeasure f x n)) - _ = _
  rw [integral_orbitMeasure, integral_orbitMeasure,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr
  simpa [BoundedContinuousFunction.compContinuous_apply, Function.iterate_succ_apply'] using
    (Finset.sum_range_sub (fun k ↦ g (f^[k] x)) (n + 1))

lemma tendsto_integral_comp_sub_integral_orbitMeasure (hf : Continuous f) :
    Tendsto (fun n ↦ (∫ y, g (f y) ∂(orbitMeasure f x n)) - ∫ y, g y ∂(orbitMeasure f x n))
      atTop (nhds 0) := by
  simp only [integral_comp_sub_integral_orbitMeasure _ _ _ _ hf, ← div_eq_inv_mul]
  apply tendsto_bdd_div_atTop_nhds_zero (B := 2 * ‖g‖) (b := -2 * ‖g‖)
  · apply Eventually.of_forall
    intro n
    linarith [g.neg_norm_le_apply (f^[n + 1] x), g.apply_le_norm x]
  · apply Eventually.of_forall
    intro n
    linarith [g.apply_le_norm (f^[n + 1] x), g.neg_norm_le_apply x]
  · simpa using
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

end Integrals

lemma ProbabilityMeasure.map_eq_self_of_mapClusterPt
    [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    {α : Type*} {F : Filter α} {f : X → X} (hf : Continuous f)
    {u : α → ProbabilityMeasure X} {μ : ProbabilityMeasure X} (hμ : MapClusterPt μ F u)
    (h : ∀ g : X →ᵇ ℝ, Tendsto (fun t ↦ (∫ y, g (f y) ∂(u t)) - ∫ y, g y ∂(u t)) F (nhds 0)) :
    μ.map hf.measurable.aemeasurable = μ := by
  rcases (mapClusterPt_iff_ultrafilter.mp hμ) with ⟨U, hUl, hUμ⟩
  have hpush_to_μ : Tendsto (fun t ↦ (u t).map hf.measurable.aemeasurable) U (nhds μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    have hbase : Tendsto (fun t ↦ ∫ y, g y ∂(u t)) U (nhds (∫ y, g y ∂μ)) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hUμ) g
    have hdiff : Tendsto (fun t ↦ (∫ y, g (f y) ∂(u t)) - ∫ y, g y ∂(u t)) U (nhds 0) :=
      (h g).mono_left hUl
    have hcomp : Tendsto (fun t ↦ ∫ y, g (f y) ∂(u t)) U (nhds (∫ y, g y ∂μ)) := by
      simpa using hdiff.add hbase
    have hmap_integral (t : α) :
        ∫ y, g y ∂((u t).map hf.measurable.aemeasurable : Measure X) = ∫ y, g (f y) ∂(u t) := by
      rw [ProbabilityMeasure.toMeasure_map]
      exact MeasureTheory.integral_map_of_stronglyMeasurable
        hf.measurable g.continuous.stronglyMeasurable
    simpa only [hmap_integral] using hcomp
  have hpush_to_map :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous u μ hUμ hf
  exact tendsto_nhds_unique hpush_to_map hpush_to_μ

/-- **Krylov-Bogolyubov theorem**: there exists an invariant Borel probability measure,
for a continuous function on a nonempty, compact, Hausdorff space which satisfies
`HasOuterApproxClosed`. It is sufficient for the space to be metrizable. -/
public theorem exists_measurePreserving_probabilityMeasure
    [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X] [T2Space X]
    [CompactSpace X] [Nonempty X] {f : X → X} (hf : Continuous f) :
    ∃ μ : ProbabilityMeasure X, MeasurePreserving f μ μ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨μ, _, hμ⟩ := isCompact_univ.exists_mapClusterPt
      (u := fun n ↦ orbitMeasure f x n) (f := atTop) (by simp)
  have hmap := ProbabilityMeasure.map_eq_self_of_mapClusterPt hf hμ
    (tendsto_integral_comp_sub_integral_orbitMeasure f (hf := hf) (x := x))
  exact ⟨μ, ⟨hf.measurable, congrArg ProbabilityMeasure.toMeasure hmap⟩⟩

end MeasureTheory
