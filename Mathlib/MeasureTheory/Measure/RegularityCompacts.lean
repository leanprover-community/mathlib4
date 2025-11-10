/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Inner regularity of finite measures

The main result of this file is
`InnerRegularCompactLTTop_of_pseudoEMetricSpace_completeSpace_secondCountable`:
A finite measure `μ` on a `PseudoEMetricSpace E` and `CompleteSpace E` with
`SecondCountableTopology E` is inner regular with respect to compact sets. In other
words, a finite measure on such a space is a tight measure.

Finite measures on Polish spaces are an important special case, which makes the result
`MeasureTheory.PolishSpace.innerRegular_isCompact_isClosed_measurableSet` an important result in
probability.
-/

open Set MeasureTheory

open scoped ENNReal Uniformity

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem innerRegularWRT_isCompact_closure_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed ↔ μ.InnerRegularWRT IsCompact IsClosed := by
  constructor <;> intro h A hA r hr
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    exact ⟨closure K, closure_minimal hK1 hA, hK2, hK3.trans_le (measure_mono subset_closure)⟩
  · rcases h hA r hr with ⟨K, ⟨hK1, hK2, hK3⟩⟩
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [closure_closure, Function.comp_apply] using hK2.closure
    · exact hK3.trans_le (measure_mono subset_closure)

lemma innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure
    [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  constructor <;> intro h A hA r hr
  · obtain ⟨K, hK1, ⟨hK2, _⟩, hK4⟩ := h hA r hr
    refine ⟨K, hK1, ?_, hK4⟩
    simp only [Function.comp_apply]
    exact hK2.closure
  · obtain ⟨K, hK1, hK2, hK3⟩ := h hA r hr
    refine ⟨closure K, closure_minimal hK1 hA, ?_, ?_⟩
    · simpa only [isClosed_closure, and_true]
    · exact hK3.trans_le (measure_mono subset_closure)

lemma innerRegularWRT_isCompact_isClosed_iff [TopologicalSpace α] [R1Space α] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed
      ↔ μ.InnerRegularWRT IsCompact IsClosed :=
  innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure.trans
    innerRegularWRT_isCompact_closure_iff

/--
If predicate `p` is preserved under intersections with sets satisfying predicate `q`, and sets
satisfying `p` cover the space arbitrarily well, then `μ` is inner regular with respect to
predicates `p` and `q`.
-/
theorem innerRegularWRT_of_exists_compl_lt {p q : Set α → Prop} (hpq : ∀ A B, p A → q B → p (A ∩ B))
    (hμ : ∀ ε, 0 < ε → ∃ K, p K ∧ μ Kᶜ < ε) :
    μ.InnerRegularWRT p q := by
  intro A hA r hr
  obtain ⟨K, hK, hK_subset, h_lt⟩ : ∃ K, p K ∧ K ⊆ A ∧ μ (A \ K) < μ A - r := by
    obtain ⟨K', hpK', hK'_lt⟩ := hμ (μ A - r) (tsub_pos_of_lt hr)
    refine ⟨K' ∩ A, hpq K' A hpK' hA, inter_subset_right, ?_⟩
    · refine (measure_mono fun x ↦ ?_).trans_lt hK'_lt
      simp only [diff_inter_self_eq_diff, mem_diff, mem_compl_iff, and_imp, imp_self, imp_true_iff]
  refine ⟨K, hK_subset, hK, ?_⟩
  have h_lt' : μ A - μ K < μ A - r := le_measure_diff.trans_lt h_lt
  exact lt_of_tsub_lt_tsub_left h_lt'

theorem innerRegularWRT_isCompact_closure_of_univ [TopologicalSpace α]
    (hμ : ∀ ε, 0 < ε → ∃ K, IsCompact (closure K) ∧ μ (Kᶜ) < ε) :
    μ.InnerRegularWRT (IsCompact ∘ closure) IsClosed := by
  refine innerRegularWRT_of_exists_compl_lt (fun s t hs ht ↦ ?_) hμ
  have : IsCompact (closure s ∩ t) := hs.inter_right ht
  refine this.of_isClosed_subset isClosed_closure ?_
  refine (closure_inter_subset_inter_closure _ _).trans_eq ?_
  rw [IsClosed.closure_eq ht]

theorem exists_isCompact_closure_measure_compl_lt [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K, IsCompact (closure K) ∧ P Kᶜ < ε := by
  /-
  If α is empty, the result is trivial.

  Otherwise, fix a dense sequence `seq` and an antitone basis `t` of entourages. We find a sequence
  of natural numbers `u n`, such that `interUnionBalls seq u t`, which is the intersection over
  `n` of the `t n`-neighborhood of `seq 1, ..., seq (u n)`, covers the space arbitrarily well.
  -/
  cases isEmpty_or_nonempty α
  case inl =>
    refine ⟨∅, by simp, ?_⟩
    rwa [Set.eq_empty_of_isEmpty ∅ᶜ, measure_empty]
  case inr =>
    let seq := TopologicalSpace.denseSeq α
    have hseq_dense : DenseRange seq := TopologicalSpace.denseRange_denseSeq α
    obtain ⟨t : ℕ → SetRel α α,
        ht : ∀ i, t i ∈ 𝓤 α ∧ IsOpen (t i) ∧ (t i).IsSymm,
        h_basis : (uniformity α).HasAntitoneBasis t⟩ :=
      (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
    choose htu hto _ using ht
    let f : ℕ → ℕ → Set α := fun n m ↦ UniformSpace.ball (seq m) (t n)
    have h_univ n : (⋃ m, f n m) = univ := hseq_dense.iUnion_uniformity_ball (htu n)
    have h3 n (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ m, P (⋂ m' ≤ m, (f n m')ᶜ) < ε := by
      refine exists_measure_iInter_lt (fun m ↦ ?_) hε ⟨0, measure_ne_top P _⟩ ?_
      · exact (measurable_prodMk_left (hto n).measurableSet).compl.nullMeasurableSet
      · rw [← compl_iUnion, h_univ, compl_univ]
    choose! s' s'bound using h3
    rcases ENNReal.exists_pos_sum_of_countable' (ne_of_gt hε) ℕ with ⟨δ, hδ1, hδ2⟩
    classical
    let u : ℕ → ℕ := fun n ↦ s' n (δ n)
    refine ⟨interUnionBalls seq u t, isCompact_closure_interUnionBalls h_basis.toHasBasis seq u, ?_⟩
    rw [interUnionBalls, Set.compl_iInter]
    refine ((measure_iUnion_le _).trans ?_).trans_lt hδ2
    refine ENNReal.tsum_le_tsum (fun n ↦ ?_)
    have h'' n : Prod.swap ⁻¹' t n = t n := by ext; exact (t n).comm
    simp only [h'', compl_iUnion, ge_iff_le]
    exact (s'bound n (δ n) (hδ1 n)).le

theorem innerRegularWRT_isCompact_closure [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (IsCompact ∘ closure) IsClosed :=
  innerRegularWRT_isCompact_closure_of_univ
    (exists_isCompact_closure_measure_compl_lt P)

theorem innerRegularWRT_isCompact_isClosed [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed := by
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure P

theorem innerRegularWRT_isCompact [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsClosed := by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure P

theorem innerRegularWRT_isCompact_isClosed_isOpen [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsOpen :=
  (innerRegularWRT_isCompact_isClosed P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

theorem innerRegularWRT_isCompact_isOpen [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsOpen :=
  (innerRegularWRT_isCompact P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

/--
A finite measure `μ` on a `PseudoEMetricSpace E` and `CompleteSpace E` with
`SecondCountableTopology E` is inner regular. In other words, a finite measure
on such a space is a tight measure.
-/
instance InnerRegular_of_pseudoEMetricSpace_completeSpace_secondCountable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegular := by
  suffices P.InnerRegularCompactLTTop from inferInstance
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen P
  · exact fun s t hs_compact ht_open ↦ hs_compact.inter_right ht_open.isClosed_compl

/--
A special case of `innerRegular_of_pseudoEMetricSpace_completeSpace_secondCountable` for Polish
spaces: A finite measure on a Polish space is a tight measure.
-/
instance InnerRegular_of_polishSpace [TopologicalSpace α]
    [PolishSpace α] [BorelSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegular := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
  exact InnerRegular_of_pseudoEMetricSpace_completeSpace_secondCountable P

/--
A measure `μ` on a `PseudoEMetricSpace E` and `CompleteSpace E` with `SecondCountableTopology E`
is inner regular for finite measure sets with respect to compact sets.
-/
instance InnerRegularCompactLTTop_of_pseudoEMetricSpace_completeSpace_secondCountable
    [PseudoEMetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (μ : Measure α) :
    μ.InnerRegularCompactLTTop := by
  constructor
  intro A ⟨hA1, hA2⟩ r hr
  have := Fact.mk hA2.lt_top
  have hA2' : (μ.restrict A) A ≠ ⊤ := by
    rwa [Measure.restrict_apply_self]
  have hr' : r < μ.restrict A A := by
    rwa [Measure.restrict_apply_self]
  obtain ⟨K, ⟨hK1, hK2, hK3⟩⟩ := MeasurableSet.exists_lt_isCompact_of_ne_top hA1 hA2' hr'
  use K, hK1, hK2
  rwa [Measure.restrict_eq_self μ hK1] at hK3

/--
A special case of `innerRegularCompactLTTop_of_pseudoEMetricSpace_completeSpace_secondCountable`
for Polish spaces: A measure `μ` on a Polish space inner regular for finite measure sets with
respect to compact sets.
-/
instance InnerRegularCompactLTTop_of_polishSpace
    [TopologicalSpace α] [PolishSpace α] [BorelSpace α] (μ : Measure α) :
    μ.InnerRegularCompactLTTop := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
  exact InnerRegularCompactLTTop_of_pseudoEMetricSpace_completeSpace_secondCountable μ

theorem innerRegular_isCompact_isClosed_measurableSet_of_finite [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  suffices P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s)
      fun s ↦ MeasurableSet s ∧ P s ≠ ∞ by
    convert this
    simp only [iff_self_and]
    exact fun _ ↦ measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isClosed_isOpen P
  · rintro s t ⟨hs_compact, hs_closed⟩ ht_open
    rw [diff_eq]
    exact ⟨hs_compact.inter_right ht_open.isClosed_compl,
      hs_closed.inter (isClosed_compl_iff.mpr ht_open)⟩

/--
On a Polish space, any finite measure is regular with respect to compact and closed sets. In
particular, a finite measure on a Polish space is a tight measure.
-/
theorem PolishSpace.innerRegular_isCompact_isClosed_measurableSet [TopologicalSpace α]
    [PolishSpace α] [BorelSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
  exact innerRegular_isCompact_isClosed_measurableSet_of_finite P

end MeasureTheory
