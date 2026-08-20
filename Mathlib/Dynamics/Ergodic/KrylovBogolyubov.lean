/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Parker
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support

import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Krylov-Bogolyubov theorem

The Krylov–Bogolyubov (or Krylov–Bogoliubov) theorem asserts the existence of invariant Borel
probability measures for continuous dynamics on compact metrizable spaces.

## Main results

- `exists_measurePreserving_probabilityMeasure`: the classical Krylov-Bogolyubov theorem.
- `exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant` gives an invariant
  probability measure defined over a (not necessarily compact) ambient space, supported on a
  compact, forward invariant subset

## Implementation notes

In order to minimise public imports, the details of the proof are contained in private lemmas.
We define a sequence of empirical orbit measures for the system starting from a given point,
and show that the cluster points of this sequence give an invariant measure if the space is compact.

We do not assume that the space is metrizable; it is sufficient to assume it is Hausdorff.

## TODO

- When the `Measurable` requirement of `MeasurePreserving` is relaxed,
  `exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant` can be generalized.
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

lemma ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt
    [TopologicalSpace X] [BorelSpace X]
    {α : Type*} {F : Filter α} {f : X → X} (hf : Continuous f)
    {u : α → ProbabilityMeasure X} {μ : ProbabilityMeasure X} (hμ : MapClusterPt μ F u)
    (h : ∀ g : X →ᵇ ℝ, Tendsto (fun t ↦ (∫ y, g (f y) ∂(u t)) - ∫ y, g y ∂(u t)) F (nhds 0)) :
    ∀ g : X →ᵇ ℝ, ∫ y, g (f y) ∂μ = ∫ y, g y ∂μ := by
  rcases (mapClusterPt_iff_ultrafilter.mp hμ) with ⟨U, hUl, hUμ⟩
  intro g
  have hgf : Tendsto (fun t ↦ ∫ y, g (f y) ∂(u t)) U (nhds (∫ y, g (f y) ∂μ)) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hUμ) (g.compContinuous ⟨f, hf⟩)
  have hgf' : Tendsto (fun t ↦ ∫ y, g (f y) ∂(u t)) U (nhds (∫ y, g y ∂μ)) := by
    simpa using ((h g).mono_left hUl).add
      ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hUμ) g)
  exact tendsto_nhds_unique hgf hgf'

/-- **Krylov-Bogolyubov theorem**: there exists an invariant Borel probability measure,
for a continuous function on a nonempty, compact, Hausdorff space. -/
public theorem exists_measurePreserving_probabilityMeasure
    [TopologicalSpace X] [BorelSpace X] [T2Space X]
    [CompactSpace X] [Nonempty X] {f : X → X} (hf : Continuous f) :
    ∃ μ : ProbabilityMeasure X, MeasurePreserving f μ μ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨μ, _, hμ⟩ := isCompact_univ.exists_mapClusterPt
    (u := fun n ↦ orbitMeasure f x n) (f := atTop) (by simp)
  have hμinv := ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hf hμ
    (tendsto_integral_comp_sub_integral_orbitMeasure f (hf := hf) (x := x))
  obtain ⟨ν, hνreg, hνfin, hμν⟩ := (μ : Measure X).exists_regular_eq_of_compactSpace
  have hprob : ν Set.univ = 1 := by
    rw [← ENNReal.toReal_eq_one_iff]
    change ν.real Set.univ = 1
    simpa using (hμν (BoundedContinuousFunction.const X 1)).symm
  have : (ν.map f).Regular := by
    have := Measure.InnerRegularCompactLTTop.map_of_continuous hf (μ := ν)
    infer_instance
  have hmap : ν.map f = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    rw [integral_map hf.aemeasurable] --
    · simp_rw [← g.toBoundedContinuousFunction_apply]
      rw [← ContinuousMap.coe_mk f hf]
      simp_rw [← g.toBoundedContinuousFunction.compContinuous_apply ⟨f,hf⟩, ← hμν]
      exact hμinv g.toBoundedContinuousFunction
    · exact g.continuous.aestronglyMeasurable
  exact ⟨⟨ν, ⟨hprob⟩⟩,hf.measurable, hmap⟩

/-- **Krylov-Boboglyubov theorem** for forward invariant compact sets. -/
public theorem exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant
    [TopologicalSpace X] [BorelSpace X] [T2Space X]
    {K : Set X} (hcomp : IsCompact K) (hnonempty : K.Nonempty)
    {f : X → X} (hfcont : ContinuousOn f K) (hfinv : Set.MapsTo f K K)
    (hfmeas : Measurable f) : -- TODO: relax this
    ∃ μ : ProbabilityMeasure X, MeasurePreserving f μ μ ∧ Measure.support μ ⊆ K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hcomp
  have : Nonempty K := hnonempty.to_subtype
  let f' : K → K := Set.MapsTo.restrict f K K hfinv
  let ι : K → X := Subtype.val
  obtain ⟨μ, hμ⟩ := exists_measurePreserving_probabilityMeasure (hfcont.mapsToRestrict hfinv)
  have hιmeas : Measurable ι :=  measurable_subtype_coe
  let ν := μ.map hιmeas.aemeasurable
  have hιmp : MeasurePreserving ι μ ν := ⟨hιmeas, by simp [ν]⟩
  have hsemi : Function.Semiconj ι f' f := by
    intro
    rfl
  refine ⟨ν, ⟨hιmp.of_semiconj hμ hsemi hfmeas, ?_⟩⟩
  -- Now we prove that the invariant measure is supported on the forward invariant set
  apply Measure.support_subset_of_isClosed hcomp.isClosed
  rw [MeasureTheory.mem_ae_iff]
  simpa [ν, ι] using
    (ProbabilityMeasure.map_apply' μ hιmeas.aemeasurable hcomp.isClosed.measurableSet.compl)

end MeasureTheory
