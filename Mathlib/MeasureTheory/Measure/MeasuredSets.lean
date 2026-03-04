/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measured sets

Consider a measure `μ` on a measurable space. One can define an extended distance on the space
of measurable sets, by `edist s t := μ (s ∆ t)`. In this file, we introduce this definition
on the type synonym `MeasuredSets μ`, and we prove that `μ` is a continuous function on this space.

We also give a density criterion for this distance,
in `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`: given a ring of sets `C` covering the
space modulo `0` and generating the measurable space structure, then any measurable set can be
approximated by elements of `C`.
Note that the covering condition is necessary: for a counterexample otherwise, take `{0, 1}` with
the counting measure and `C = {∅, {0}}`. Then the set `{1}` can not be approximated by
an element of `C`.
-/

@[expose] public section

open MeasurableSpace Set Filter
open scoped symmDiff ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

set_option linter.unusedVariables false in
/-- The subtype of all measurable sets. We denote it as `MeasuredSets μ`, with an explicit but
unused parameter `μ`, to be able to define a distance on it given by `edist s t = μ (s ∆ t)` -/
@[nolint unusedArguments]
def MeasuredSets (μ : Measure α) : Type _ := {s : Set α // MeasurableSet s}

instance : SetLike (MeasuredSets μ) α where
  coe s := s.1
  coe_injective' := Subtype.coe_injective

instance : PseudoEMetricSpace (MeasuredSets μ) where
  edist s t := μ ((s : Set α) ∆ t)
  edist_self := by simp
  edist_comm := by grind
  edist_triangle s t u := measure_symmDiff_le _ _ _

lemma MeasuredSets.edist_def (s t : MeasuredSets μ) : edist s t = μ ((s : Set α) ∆ t) := rfl

/-- Measure on `MeasuredSets` is a 1-lipschitz function.

We cannot state this in terms of `LipschitzWith`, because `ℝ≥0∞` is not a `PseudoEMetricSpace`. -/
lemma MeasuredSets.sub_le_edist (s t : MeasuredSets μ) : μ s - μ t ≤ edist s t :=
  le_measure_diff.trans <| measure_mono subset_union_left

lemma MeasuredSets.continuous_measure : Continuous (fun (s : MeasuredSets μ) ↦ μ s) := by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun s t ↦ ?_
  rw [one_mul, ← tsub_le_iff_left]
  exact sub_le_edist s t

instance [IsFiniteMeasure μ] : PseudoMetricSpace (MeasuredSets μ) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun s t ↦ μ.real ((s : Set α) ∆ t)) (fun s t ↦ ENNReal.toReal_nonneg)
    (fun s t ↦ by simp [Measure.real, MeasuredSets.edist_def])

lemma MeasuredSets.dist_def [IsFiniteMeasure μ] (s t : MeasuredSets μ) :
    dist s t = μ.real ((s : Set α) ∆ t) := rfl

lemma MeasuredSets.real_sub_real_le_dist [IsFiniteMeasure μ] (s t : MeasuredSets μ) :
    μ.real s - μ.real t ≤ dist s t := by
  grw [dist_edist, ← sub_le_edist]
  exacts [ENNReal.le_toReal_sub (measure_ne_top _ _), edist_ne_top _ _]

lemma MeasuredSets.lipschitzWith_measureReal [IsFiniteMeasure μ] :
    LipschitzWith 1 (fun s : MeasuredSets μ ↦ μ.real s) :=
  .of_le_add fun s t ↦ sub_le_iff_le_add'.mp <| real_sub_real_le_dist s t

/-- Given a ring of sets `C` covering the space modulo `0` and generating the measurable space
structure, any measurable set can be approximated by elements of `C`. -/
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetRing [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetRing C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ C, μ (t ∆ s) < ε := by
  /- We check that the set of sets satisfying the conclusion of the lemma for all positive
  `ε` contains `C` and is stable under complement and disjoint union. It follows that it is
  all the sigma-algebra, as desired. -/
  apply MeasurableSpace.induction_on_inter (C := fun s hs ↦ ∀ (ε : ℝ≥0∞) (hε : 0 < ε),
    ∃ t ∈ C, μ (t ∆ s) < ε) h hC.isSetSemiring.isPiSystem ?_ ?_ ?_ ?_ s hs ε hε
  · intro ε εpos
    exact ⟨∅, hC.empty_mem, by simp [εpos]⟩
  · intro s hs ε εpos
    exact ⟨s, hs, by simp [εpos]⟩
  · /- To check the stability under complement, we use the condition `h'C` which guarantees
    that the space is almost an element of `C`. If `t` approximates `s`, then `univ \ t`
    approximates well `sᶜ`, and therefore `t' \ t` approximates well `sᶜ` when `t'` is a good
    enough approximation to `univ`. As `t' \ t` belongs to `C` when `t` and `t'` do, this
    concludes this step. -/
    intro s hs h's ε εpos
    obtain ⟨t, tC, ht⟩ : ∃ t ∈ C, μ (t ∆ s) < ε / 2 := h's _ (ENNReal.half_pos εpos.ne')
    obtain ⟨t', t'C, ht'⟩ : ∃ t' ∈ C, μ (t'ᶜ) < ε / 2 := by
      obtain ⟨D, D_count, DC, hD, Dne⟩ :
          ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0 ∧ D.Nonempty := by
        rcases h'C with ⟨D, D_count, DC, hD⟩
        refine ⟨D ∪ {∅}, D_count.union (by simp), ?_⟩
        simp only [union_subset_iff, DC, singleton_subset_iff, true_and, and_true, hC.empty_mem]
        simp only [union_singleton, sUnion_insert, empty_union, insert_nonempty, and_true, hD]
      obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, D = Set.range f := Set.Countable.exists_eq_range D_count Dne
      have fC n : Set.accumulate f n ∈ C := hC.accumulate_mem (fun n ↦ DC (by simp [hf])) n
      have : Tendsto (fun n ↦ μ (Set.accumulate f n)ᶜ) atTop (𝓝 0) := by
        have : ⋃₀ D = ⋃ n, Set.accumulate f n := by simp [hf, iUnion_accumulate]
        rw [show (⋃₀ D)ᶜ = ⋂ n, (Set.accumulate f n)ᶜ by simp [this]] at hD
        rw [← hD]
        apply tendsto_measure_iInter_atTop (fun i ↦ ?_)
          (fun i j hij ↦ by simpa using monotone_accumulate hij) ⟨0, by simp⟩
        apply MeasurableSet.nullMeasurableSet
        rw [h]
        exact (measurableSet_generateFrom (fC i)).compl
      obtain ⟨n, hn⟩ : ∃ n, μ (accumulate f n)ᶜ < ε / 2 :=
        ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
      exact ⟨accumulate f n, fC n, hn⟩
    refine ⟨t' \ t, hC.diff_mem t'C tC, ?_⟩
    calc μ ((t' \ t) ∆ sᶜ)
      _ ≤ μ (t ∆ s ∪ t'ᶜ) := by gcongr; grind
      _ ≤ μ (t ∆ s) + μ (t'ᶜ) := measure_union_le _ _
      _ < ε / 2 + ε / 2 := by gcongr
      _ = ε := ENNReal.add_halves ε
  · /- To check the stability under disjoint union, approximate `f n` by a set `t n ∈ C`. Then
    `⋃ i, f i` is well approximated by `U i < n, f i` for large enough `n`, which is itself
    well approximated by `⋃ i < n, t i`. As this set belongs to `C`, this concludes this step. -/
    intro f f_disj f_meas hf ε εpos
    rcases ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos εpos.ne').ne' ℕ with ⟨δ, δpos, hδ⟩
    have A i : ∃ t ∈ C, μ (t ∆ (f i)) < δ i := hf i _ (δpos i)
    choose! t tC ht using A
    have : Tendsto (fun n ↦ μ (⋃ i ∈ Ici n, f i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i ↦ (f_meas i).nullMeasurableSet) f_disj
    obtain ⟨n, hn⟩ : ∃ n, μ (⋃ i ∈ Ici n, f i) < ε / 2 :=
      ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
    refine ⟨⋃ i ∈ Finset.range n, t i, hC.biUnion_mem _ (fun i hi ↦ tC _), ?_⟩
    calc μ ((⋃ i ∈ Finset.range n, t i) ∆ (⋃ i, f i))
    _ ≤ μ ((⋃ i ∈ Finset.range n, (t i) ∆ (f i)) ∪ ⋃ i ∈ Ici n, f i) := by
      gcongr
      intro x hx
      simp only [Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop, not_exists, not_and,
        mem_Ici, mem_union] at hx ⊢
      grind
    _ ≤ ∑ i ∈ Finset.range n, μ (t i ∆ f i) + μ (⋃ i ∈ Ici n, f i) := by
      apply (measure_union_le _ _).trans
      gcongr
      apply measure_biUnion_finset_le
    _ ≤ ∑ i ∈ Finset.range n, δ i + μ (⋃ i ∈ Ici n, f i) := by
      gcongr with i; exact (ht i).le
    _ ≤ ∑' i, δ i + μ (⋃ i ∈ Ici n, f i) := by
      gcongr; exact ENNReal.sum_le_tsum (Finset.range n)
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε :=  ENNReal.add_halves ε

/-- Given a semiring of sets `C` covering the space modulo `0` and generating the measurable space
structure, any measurable set can be approximated by finite unions of elements of `C`. -/
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetSemiring C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ t ∈ supClosure C, μ (t ∆ s) < ε := by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC.isSetRing_supClosure ?_ ?_ hs hε
  · rcases h'C with ⟨D, D_count, DC, hD⟩
    exact ⟨D, D_count, DC.trans subset_supClosure, hD⟩
  · rw [h]
    apply le_antisymm (generateFrom_mono subset_supClosure)
    apply generateFrom_le (fun t ht ↦ ?_)
    apply measurableSet_generateFrom_of_mem_supClosure ht

/-- A ring of sets covering the space modulo `0` and generating the measurable space
structure is dense among measurable sets. -/
lemma dense_of_generateFrom_isSetRing [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetRing C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) :
    Dense ((SetLike.coe : MeasuredSets μ → Set α) ⁻¹' C) := by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC h'C h s.2 εpos with ⟨t, tC, ht⟩
  have t_meas : MeasurableSet t := by rw [h]; exact measurableSet_generateFrom tC
  refine ⟨⟨t, t_meas⟩, ?_, tC⟩
  simpa [MeasuredSets.edist_def] using ht

/-- Given a semiring of sets `C` covering the space modulo `0` and generating the measurable space
structure, finite unions of elements of `C` are dense among measurable sets. -/
lemma dense_of_generateFrom_isSetSemiring [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetSemiring C)
    (h'C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) :
    Dense ((SetLike.coe : MeasuredSets μ → Set α) ⁻¹' (supClosure C)) := by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h'C h s.2 εpos
    with ⟨t, tC, ht⟩
  refine ⟨⟨t, ?_⟩, by simpa [MeasuredSets.edist_def] using ht, tC⟩
  rw [h]
  exact measurableSet_generateFrom_of_mem_supClosure tC

end MeasureTheory
