/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Polish

/-!
# Inner regularity of finite measures

The main result of this file is `theorem inner_regularWRT_isCompact_of_complete_countable`:
A `FiniteMeasure P` on a `PseudoEMetricSpace E` and `CompleteSpace E` with
`SecondCountableTopology E` is inner regular with respect to compact sets.

Finite measures on Polish spaces are an important special case, which makes the result
`theorem PolishSpace.innerRegular_isCompact_measurableSet` an important result in probability.
-/

open Set MeasureTheory

open scoped ENNReal Topology

variable {α : Type*}

section Topology

namespace UniformSpace

lemma _root_.MeasurableSet.ball {_ : MeasurableSpace α} (x : α)
    {s : Set (α × α)} (hs : MeasurableSet s) :
    MeasurableSet (UniformSpace.ball x s) := measurable_prod_mk_left hs

/-- Given a family of points `xs n`, a family of entourages `V n` of the diagonal and a family of
natural numbers `u n`, the intersection over `n` of the `V n`-neighborhood of `xs 1, ..., xs (u n)`.
Designed to be relatively compact when `V n` tends to the diagonal. -/
def interUnionBalls (xs : ℕ → α) (u : ℕ → ℕ) (V : ℕ → Set (α × α)) : Set α :=
  ⋂ n, ⋃ m ≤ u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n)

lemma totallyBounded_interUnionBalls [UniformSpace α] {p : ℕ → Prop} {U : ℕ → Set (α × α)}
    (H : (uniformity α).HasBasis p U) (xs : ℕ → α) (u : ℕ → ℕ) :
    TotallyBounded (interUnionBalls xs u U) := by
  rw [Filter.HasBasis.totallyBounded_iff H]
  intro i _
  have h_subset : interUnionBalls xs u U
      ⊆ ⋃ m ≤ u i, UniformSpace.ball (xs m) (Prod.swap ⁻¹' U i) :=
    fun x hx ↦ Set.mem_iInter.1 hx i
  classical
  refine ⟨Finset.image xs (Finset.range (u i + 1)), Finset.finite_toSet _, fun x hx ↦ ?_⟩
  simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio, iUnion_exists, biUnion_and',
    iUnion_iUnion_eq_right, Nat.lt_succ_iff]
  exact h_subset hx

/-- The construction `interUnionBalls` is used to have a relatively compact set. -/
theorem isCompact_closure_interUnionBalls [UniformSpace α] {p : ℕ → Prop} {U : ℕ → Set (α × α)}
    (H : (uniformity α).HasBasis p U) [CompleteSpace α] (xs : ℕ → α) (u : ℕ → ℕ) :
    IsCompact (closure (interUnionBalls xs u U)) := by
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  exact totallyBounded_interUnionBalls H xs u

theorem _root_.MeasureTheory.measure_compl_interUnionBalls_le {_ : MeasurableSpace α}
    (μ : Measure α) (xs : ℕ → α) (u : ℕ → ℕ) (V : ℕ → Set (α × α)) :
    μ (UniformSpace.interUnionBalls xs u V)ᶜ ≤
      ∑' n, μ (⋃ m ≤ u n, UniformSpace.ball (xs m) (Prod.swap ⁻¹' V n))ᶜ := by
  rw [UniformSpace.interUnionBalls, Set.compl_iInter]
  exact measure_iUnion_le _

end UniformSpace

end Topology


namespace MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}

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
    simp only [closure_closure, Function.comp_apply]
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

theorem exists_isCompact_closure_measure_lt_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K, IsCompact (closure K) ∧ P Kᶜ < ε := by
  cases isEmpty_or_nonempty α
  case inl =>
    refine ⟨∅, by simp, ?_⟩
    rw [← Set.univ_eq_empty_iff.mpr]
    · simpa only [compl_univ, measure_empty, ENNReal.coe_pos] using hε
    · assumption
  case inr =>
    let seq := TopologicalSpace.denseSeq α
    have hseq_dense : DenseRange seq := TopologicalSpace.denseRange_denseSeq α
    obtain ⟨t : ℕ → Set (α × α),
        hto : ∀ i, t i ∈ (uniformity α).sets ∧ IsOpen (t i) ∧ SymmetricRel (t i),
        h_basis : (uniformity α).HasAntitoneBasis t⟩ :=
      (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
    let f : ℕ → ℕ → Set α := fun n m ↦ UniformSpace.ball (seq m) (t n)
    have h_univ n : (⋃ m, f n m) = univ := hseq_dense.iUnion_uniformity_ball (hto n).1
    have h3 n (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ m, P (⋂ m' ≤ m, (f n m')ᶜ) < ε := by
      refine exists_measure_iInter_lt (fun m ↦ ?_) hε ⟨0, measure_ne_top P _⟩ ?_
      · exact ((IsOpen.measurableSet (hto n).2.1).ball _).compl.nullMeasurableSet
      · rw [← compl_iUnion, h_univ, compl_univ]
    choose! s' s'bound using h3
    rcases ENNReal.exists_seq_pos_lt ε hε with ⟨δ, hδ1, hδ2⟩
    classical
    let u : ℕ → ℕ := fun n ↦ s' n (δ n)
    let A := UniformSpace.interUnionBalls seq u t
    refine ⟨A, UniformSpace.isCompact_closure_interUnionBalls h_basis.toHasBasis seq u, ?_⟩
    refine ((measure_compl_interUnionBalls_le P seq u t).trans ?_).trans_lt hδ2
    refine ENNReal.tsum_le_tsum (fun n ↦ ?_)
    have h'' n : Prod.swap ⁻¹' t n = t n := SymmetricRel.eq (hto n).2.2
    simp only [h'', compl_iUnion, ge_iff_le]
    exact (s'bound n (δ n) (hδ1 n)).le

theorem innerRegularWRT_isCompact_closure_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (IsCompact ∘ closure) IsClosed :=
  innerRegularWRT_isCompact_closure_of_univ
    (exists_isCompact_closure_measure_lt_of_complete_countable P)

theorem innerRegularWRT_isCompact_isClosed_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsClosed := by
  have : R1Space α := by
    exact instR1Space
  rw [innerRegularWRT_isCompact_isClosed_iff_innerRegularWRT_isCompact_closure]
  exact innerRegularWRT_isCompact_closure_of_complete_countable P

theorem innerRegularWRT_isCompact_of_complete_countable [UniformSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [(uniformity α).IsCountablyGenerated]
    [OpensMeasurableSpace α] (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsClosed := by
  rw [← innerRegularWRT_isCompact_closure_iff]
  exact innerRegularWRT_isCompact_closure_of_complete_countable P

theorem innerRegularWRT_isCompact_isClosed_isOpen_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) IsOpen :=
  (innerRegularWRT_isCompact_isClosed_of_complete_countable P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

theorem innerRegularWRT_isCompact_isOpen_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT IsCompact IsOpen :=
  (innerRegularWRT_isCompact_of_complete_countable P).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace P)

theorem InnerRegularCompactLTTop_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularCompactLTTop := by
  refine ⟨Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_⟩
  · exact innerRegularWRT_isCompact_isOpen_of_complete_countable P
  · exact fun s t hs_compact ht_open ↦ hs_compact.inter_right ht_open.isClosed_compl

theorem innerRegular_isCompact_isClosed_measurableSet_of_complete_countable [PseudoEMetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
    (P : Measure α) [IsFiniteMeasure P] :
    P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  suffices P.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s)
      fun s ↦ MeasurableSet s ∧ P s ≠ ∞ by
    convert this
    simp only [eq_iff_iff, iff_self_and]
    exact fun _ ↦ measure_ne_top P _
  refine Measure.InnerRegularWRT.measurableSet_of_isOpen ?_ ?_
  · exact innerRegularWRT_isCompact_isClosed_isOpen_of_complete_countable P
  · rintro s t ⟨hs_compact, hs_closed⟩ ht_open
    rw [diff_eq]
    exact ⟨hs_compact.inter_right ht_open.isClosed_compl,
      hs_closed.inter (isClosed_compl_iff.mpr ht_open)⟩

/-- On a Polish space, any finite measure is regular with respect to compact and closed sets. -/
theorem PolishSpace.innerRegular_isCompact_measurableSet [TopologicalSpace α] [PolishSpace α]
    [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet := by
  letI := upgradePolishSpace α
  exact innerRegular_isCompact_isClosed_measurableSet_of_complete_countable μ

end MeasureTheory
