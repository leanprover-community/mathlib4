/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Continuity of measures

This file proves several versions of continuity from above and continuity from below of measures,
namely statements of the form `μ (⋃ n, s n) = ⨆ n, μ (s n)`
and `μ (⋂ n, s n) = ⨅ n, μ (s n)` for `s : ℕ → Set α`.

## Tags

continuity of measures
-/

public section

open Set Function Filter ENNReal
open scoped Topology

namespace MeasureTheory

variable {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : ι → Set α}

/-- Continuity from below:
the measure of the union of a directed sequence of (not necessarily measurable) sets
is the supremum of the measures. -/
theorem _root_.Directed.measure_iUnion [Countable ι] (hd : Directed (· ⊆ ·) s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  -- WLOG, `ι = ℕ`
  rcases Countable.exists_injective_nat ι with ⟨e, he⟩
  generalize ht : Function.extend e s ⊥ = t
  replace hd : Directed (· ⊆ ·) t := ht ▸ hd.extend_bot he
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion, iSup_extend_bot he,
      Function.comp_def, Pi.bot_apply, bot_eq_empty, measure_empty] at this
    exact this.trans (iSup_extend_bot he _)
  clear! ι
  -- The `≥` inequality is trivial
  refine le_antisymm ?_ (iSup_le fun i ↦ measure_mono <| subset_iUnion _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : ℕ → Set α := fun n => toMeasurable μ (t n)
  set Td : ℕ → Set α := disjointed T
  have hm : ∀ n, MeasurableSet (Td n) := .disjointed fun n ↦ measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) = μ (⋃ n, Td n) := by rw [iUnion_disjointed, measure_iUnion_toMeasurable]
    _ ≤ ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset ℕ, ∑ n ∈ I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ ≤ ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n ∈ I, μ (Td n)) = μ (⋃ n ∈ I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ ≤ μ (⋃ n ∈ I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n ∈ I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ ≤ μ (t N) := measure_mono (iUnion₂_subset hN)
        _ ≤ ⨆ n, μ (t n) := le_iSup (μ ∘ t) N

/-- Continuity from below:
the measure of the union of a monotone family of sets is equal to the supremum of their measures.
The theorem assumes that the `atTop` filter on the index set is countably generated,
so it works for a family indexed by a countable type, as well as `ℝ`. -/
theorem _root_.Monotone.measure_iUnion [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] (hs : Monotone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ =>
    rcases exists_seq_monotone_tendsto_atTop_atTop ι with ⟨x, hxm, hx⟩
    rw [← hs.iUnion_comp_tendsto_atTop hx, ← Monotone.iSup_comp_tendsto_atTop _ hx]
    exacts [(hs.comp hxm).directed_le.measure_iUnion, fun _ _ h ↦ measure_mono (hs h)]

theorem _root_.Antitone.measure_iUnion [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] (hs : Antitone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) :=
  hs.dual_left.measure_iUnion

/-- Continuity from below: the measure of the union of a sequence of
(not necessarily measurable) sets is the supremum of the measures of the partial unions. -/
theorem measure_iUnion_eq_iSup_accumulate [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] :
    μ (⋃ i, s i) = ⨆ i, μ (accumulate s i) := by
  rw [← iUnion_accumulate]
  exact monotone_accumulate.measure_iUnion

theorem measure_biUnion_eq_iSup {t : Set ι} (ht : t.Countable)
    (hd : DirectedOn ((· ⊆ ·) on s) t) : μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion, hd.directed_val.measure_iUnion, ← iSup_subtype'']

/-- **Continuity from above**:
the measure of the intersection of a directed downwards countable family of measurable sets
is the infimum of the measures. -/
theorem _root_.Directed.measure_iInter [Countable ι]
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Directed (· ⊇ ·) s) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  rcases hfin with ⟨k, hk⟩
  have : ∀ t ⊆ s k, μ t ≠ ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le (fun i => μ (s i)) k), ENNReal.sub_iInf, ←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k)), ←
    measure_sdiff (iInter_subset _ k) (.iInter h) (this _ (iInter_subset _ k)),
    sdiff_iInter, Directed.measure_iUnion]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => le_measure_sdiff)
    rcases hd i k with ⟨j, hji, hjk⟩
    use j
    rw [← measure_sdiff hjk (h _) (this _ hjk)]
    gcongr
  · exact hd.mono_comp _ fun _ _ => sdiff_subset_sdiff_right

/-- **Continuity from above**:
the measure of the intersection of a monotone family of measurable sets
indexed by a type with countably generated `atBot` filter
is equal to the infimum of the measures. -/
theorem _root_.Monotone.measure_iInter [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] (hs : Monotone s)
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine le_antisymm (le_iInf fun i ↦ measure_mono <| iInter_subset _ _) ?_
  have := hfin.nonempty
  rcases exists_seq_antitone_tendsto_atTop_atBot ι with ⟨x, hxm, hx⟩
  calc
    ⨅ i, μ (s i) ≤ ⨅ n, μ (s (x n)) := le_iInf_comp (μ ∘ s) x
    _ = μ (⋂ n, s (x n)) := by
      refine .symm <| (hs.comp_antitone hxm).directed_ge.measure_iInter (fun n ↦ hsm _) ?_
      rcases hfin with ⟨k, hk⟩
      rcases (hx.eventually_le_atBot k).exists with ⟨n, hn⟩
      exact ⟨n, ne_top_of_le_ne_top hk <| measure_mono <| hs hn⟩
    _ ≤ μ (⋂ i, s i) := by
      refine measure_mono <| iInter_mono' fun i ↦ ?_
      rcases (hx.eventually_le_atBot i).exists with ⟨n, hn⟩
      exact ⟨n, hs hn⟩

/-- Continuity from above (a.e. version):
the measure of the intersection of a family of sets that is almost everywhere monotone
is equal to the infimum of the measures. -/
theorem measure_iInter_of_ae_monotone [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] (hs : ∀ᵐ ω ∂μ, Monotone (ω ∈ s ·))
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  obtain ⟨i, hi⟩ := hfin
  have : Nonempty ι := ⟨i⟩
  let t : ι → Set α := fun i ↦ s i ∩ {ω | Monotone (ω ∈ s ·)}
  have hst (i : ι) : s i =ᵐ[μ] t i := by
    filter_upwards [hs] with ω hω
    suffices ω ∈ s i ↔ ω ∈ t i from propext this
    simpa [t] using fun _ ↦ hω
  have hMono : Monotone t := fun i j hij ω hω ↦ ⟨hω.2 hij hω.1, hω.2⟩
  rw [iInf_congr <| fun i ↦ measure_congr <| hst i,
    ← hMono.measure_iInter (fun i ↦ (hsm i).congr (hst i)) ⟨i, by rwa [← measure_congr (hst i)]⟩]
  refine measure_congr ?_
  nth_rw 1 [← iInter_inter, ← inter_univ (⋂ i, s i)]
  exact ae_eq_set_inter (by rfl) (ae_eq_univ.2 hs).symm

/-- **Continuity from above**:
the measure of the intersection of an antitone family of measurable sets
indexed by a type with countably generated `atTop` filter
is equal to the infimum of the measures. -/
theorem _root_.Antitone.measure_iInter [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] (hs : Antitone s)
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) :=
  hs.dual_left.measure_iInter hsm hfin

/-- Continuity from above (a.e. version):
the measure of the intersection of a family of sets that is almost everywhere antitone
is equal to the infimum of the measures. -/
lemma measure_iInter_of_ae_antitone [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] (hs : ∀ᵐ ω ∂μ, Antitone (ω ∈ s ·))
    (hsm : ∀ (i : ι), NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine measure_iInter_of_ae_monotone (ι := ιᵒᵈ) ?_ hsm hfin
  filter_upwards [hs] with ω hω using hω.dual_left

/-- Continuity from above: the measure of the intersection of a sequence of
measurable sets is the infimum of the measures of the partial intersections. -/
theorem measure_iInter_eq_iInf_measure_iInter_le [Countable ι] [Preorder ι] [IsDirectedOrder ι]
    (h : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (⋂ j ≤ i, s j) := by
  rw [← Antitone.measure_iInter]
  · rw [iInter_comm]
    exact congrArg μ <| iInter_congr fun i ↦ (biInf_const nonempty_Ici).symm
  · exact fun i j h ↦ biInter_mono (Iic_subset_Iic.2 h) fun _ _ ↦ Set.Subset.rfl
  · exact fun i ↦ .biInter (to_countable _) fun _ _ ↦ h _
  · refine hfin.imp fun k hk ↦ ne_top_of_le_ne_top hk <| measure_mono <| iInter₂_subset k ?_
    rfl

/-- Continuity from below: the measure of the union of an increasing sequence of (not necessarily
measurable) sets is the limit of the measures. -/
theorem tendsto_measure_iUnion_atTop [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iUnion]
  exact tendsto_atTop_iSup fun n m hnm => measure_mono <| hm hnm

theorem tendsto_measure_iUnion_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    (hm : Antitone s) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋃ n, s n))) :=
  tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
theorem tendsto_measure_iUnion_accumulate [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] :
    Tendsto (fun i ↦ μ (accumulate s i)) atTop (𝓝 (μ (⋃ i, s i))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
theorem tendsto_measure_iInter_atTop [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)]
    (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iInter hs hf]
  exact tendsto_atTop_iInf fun n m hnm => measure_mono <| hm hnm

/-- Continuity from above: the measure of the intersection of an increasing sequence of measurable
sets is the limit of the measures. -/
theorem tendsto_measure_iInter_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Monotone s)
    (hf : ∃ i, μ (s i) ≠ ∞) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋂ n, s n))) :=
  tendsto_measure_iInter_atTop (ι := ιᵒᵈ) hs hm.dual_left hf

/-- Continuity from above: the measure of the intersection of a sequence of measurable
sets such that one has finite measure is the limit of the measures of the partial intersections. -/
theorem tendsto_measure_iInter_le [Countable ι] [Preorder ι] (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hf : ∃ i, μ (s i) ≠ ∞) :
    Tendsto (fun i ↦ μ (⋂ j ≤ i, s j)) atTop (𝓝 (μ (⋂ i, s i))) := by
  refine .of_neBot_imp fun hne ↦ ?_
  cases atTop_neBot_iff.mp hne
  rw [measure_iInter_eq_iInf_measure_iInter_le hm hf]
  exact tendsto_atTop_iInf
    fun i j hij ↦ measure_mono <| biInter_subset_biInter_left fun k hki ↦ le_trans hki hij

/-- Some version of continuity of a measure in the empty set using the intersection along a set of
sets. -/
theorem exists_measure_iInter_lt [SemilatticeSup ι] [Countable ι]
    (hm : ∀ i, NullMeasurableSet (s i) μ) {ε : ℝ≥0∞} (hε : 0 < ε) (hfin : ∃ i, μ (s i) ≠ ∞)
    (hfem : ⋂ n, s n = ∅) : ∃ m, μ (⋂ n ≤ m, s n) < ε := by
  let F m := μ (⋂ n ≤ m, s n)
  have hFAnti : Antitone F :=
      fun i j hij => measure_mono (biInter_subset_biInter_left fun k hki => le_trans hki hij)
  suffices Filter.Tendsto F Filter.atTop (𝓝 0) by
    let _ := hfin.nonempty
    rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hFAnti] at this
    exact this ε hε
  have hzero : μ (⋂ n, s n) = 0 := by
    simp only [hfem, measure_empty]
  rw [← hzero]
  exact tendsto_measure_iInter_le hm hfin

/-- The measure of the intersection of a decreasing sequence of measurable
sets indexed by a linear order with first countable topology is the limit of the measures. -/
theorem tendsto_measure_biInter_gt [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [FirstCountableTopology ι]
    {a : ι} (hs : ∀ r > a, NullMeasurableSet (s r) μ) (hm : ∀ i j, a < i → i ≤ j → s i ⊆ s j)
    (hf : ∃ r > a, μ (s r) ≠ ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) := by
  by_cases ha : Order.IsPredPrelimit a
  · have : (atBot : Filter (Ioi a)).IsCountablyGenerated := by
      rw [← comap_coe_Ioi_nhdsGT a ha]
      infer_instance
    simp_rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, ← mem_Ioi, biInter_eq_iInter]
    apply tendsto_measure_iInter_atBot
    · rwa [Subtype.forall]
    · exact fun i j h ↦ hm i j i.2 h
    · simpa only [Subtype.exists, exists_prop]
  · rw [Order.not_isPredPrelimit_iff] at ha
    rcases ha with ⟨b, hab⟩
    simp [hab.nhdsGT]

end MeasureTheory
