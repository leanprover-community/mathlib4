/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Pre-variation of a subadditive set function

Given a σ-subadditive `ℝ≥0∞`-valued set function `f`, we define the pre-variation as the supremum
over finite measurable partitions of the sum of `f` on the parts. This construction yields a
measure.

## Main definitions

* `IsSigmaSubadditiveSetFun f` — `f` is σ-subadditive on measurable sets
* `ennrealPreVariation f` — the `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function
* `preVariation f` — the `Measure X` built from a σ-subadditive function

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

open NNReal ENNReal Function

namespace MeasureTheory

/-!
## Pre-variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all finite partitions of measurable sets `E i` of the sum of `∑ i, f (E i)`. If `f` is
σ-subadditive then the function defined is an `ℝ≥0∞`-valued measure.
-/

section

variable (f : Set X → ℝ≥0∞)

open Classical in
/-- If `s` is measurable then `preVariationFun f s` is the supremum over partitions `P` of `s` of
the quantity `∑ p ∈ P.parts, f p`. If `s` is not measurable then it is set to `0`. -/
noncomputable def preVariationFun (s : Set X) : ℝ≥0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p
  else 0

end

namespace preVariation

variable (f : Set X → ℝ≥0∞)

/-- `preVariationFun` of the empty set is equal to zero. -/
lemma empty : preVariationFun f ∅ = 0 := by simp [preVariationFun]

lemma sum_le {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s := by
  simpa [preVariationFun, hs, le_iSup_iff] using fun _ a ↦ a P

open Classical in
/-- If `P` is a partition of `s₁` and `s₁ ⊆ s₂` then
`∑ p ∈ P.parts, f p ≤ preVariationFun f s₂`. -/
lemma sum_le_preVariationFun_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) (P : Finpartition (⟨s₁, hs₁⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s₂ := by
  by_cases heq : s₁ = s₂
  · rw [← heq]; exact sum_le f hs₁ P
  · let b : Subtype MeasurableSet := ⟨s₂ \ s₁, hs₂.diff hs₁⟩
    have hb : b ≠ ⊥ := fun hc => heq (h.antisymm (Set.diff_eq_empty.mp (congrArg (·.1) hc)))
    have hab : Disjoint (⟨s₁, hs₁⟩ : Subtype MeasurableSet) b := by
      simp only [b, disjoint_iff, Subtype.ext_iff]
      exact Set.inter_diff_self s₁ s₂
    have hc : (⟨s₁, hs₁⟩ : Subtype MeasurableSet) ⊔ b = ⟨s₂, hs₂⟩ :=
      Subtype.ext (Set.union_diff_cancel h)
    calc ∑ p ∈ P.parts, f p
      _ ≤ ∑ p ∈ (P.extend hb hab hc).parts, f p :=
          Finset.sum_le_sum_of_subset fun _ hx => Finset.mem_insert_of_mem hx
      _ ≤ preVariationFun f s₂ := sum_le f hs₂ _

/-- `preVariationFun` is monotone in terms of the (measurable) set. -/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    preVariationFun f s₁ ≤ preVariationFun f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariationFun_of_subset f hs₁ hs₂ h
    simp_all [preVariationFun]
  · simp [preVariationFun, hs₁]

lemma exists_Finpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < preVariationFun f s) : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    a < ∑ p ∈ P.parts, f p := by
  simp_all [preVariationFun, lt_iSup_iff]

set_option backward.isDefEq.respectTransparency false in
lemma exists_Finpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : ℝ≥0} (hε : 0 < ε)
    (h : preVariationFun f s ≠ ⊤) :
    ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariationFun f s ≤ ∑ p ∈ P.parts, f p + ε := by
  let ε' := min ε (preVariationFun f s).toNNReal
  have hε' : ε' ≤ preVariationFun f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : preVariationFun f s ≠ 0 ∨ preVariationFun f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariationFun f s - ε'
    have ha : a < preVariationFun f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariationFun f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ ≤ ∑ p ∈ P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ ≤ ∑ p ∈ P.parts, f p + ε := by gcongr
  · simp [*]

open Classical in
/-- The sup of measurable set subtypes over a finset equals the biUnion of the underlying sets. -/
lemma Finset.sup_measurableSetSubtype_eq_biUnion {ι : Type*}
    (s : ι → Subtype (@MeasurableSet X _)) (I : Finset ι) :
    ((I.sup s : Subtype MeasurableSet) : Set X) = ⋃ i ∈ I, (s i).val := by
  refine I.induction_on (by simp) ?_
  intro _ _ _ h
  simp [← h]

open Classical in
lemma sum_le_preVariationFun_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : ∀ (i : ℕ), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p ≤ preVariationFun f (⋃ i, s i) := by
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set ℕ) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.combine P hs_disj.supIndep
  have hQ_le : (Finset.range n).sup s' ≤ ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe, Finset.sup_measurableSetSubtype_eq_biUnion s']
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p
    _ = ∑ p ∈ Q.parts, f p := (Finpartition.sum_combine P hs_disj.supIndep (fun p => f p)).symm
    _ ≤ ∑ p ∈ R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ ≤ preVariationFun f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

lemma sum_le_preVariationFun_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariationFun f (s i) ≤ preVariationFun f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  by_cases hn : n = 0
  · simp [hn]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : preVariationFun f (s i) ≠ ⊤ := lt_top_iff_ne_top.mp <|
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariationFun f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, preVariationFun f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
    _ ≤ preVariationFun f (⋃ i, s i) + ε' := by
      gcongr; exact sum_le_preVariationFun_iUnion' f hs hs' P n

end preVariation

/-- A set function is σ-subadditive on measurable sets if the value assigned to the union of a
countable disjoint family of measurable sets is bounded above by the sum of values on the family. -/
def IsSigmaSubadditiveSetFun (f : Set X → ℝ≥0∞) : Prop :=
  ∀ (s : ℕ → {t : Set X // MeasurableSet t}), Pairwise (Disjoint on (Subtype.val ∘ s)) →
    f (⋃ i, (s i).val) ≤ ∑' i, f (s i)

namespace preVariation

variable {f : Set X → ℝ≥0∞}

open Classical in
/-- Additivity of `preVariationFun` for disjoint measurable sets. -/
lemma iUnion (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ preVariationFun f (s i)) (preVariationFun f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (le_antisymm (sum_le_preVariationFun_iUnion f hs hs') ?_)
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb ↦ ?_
  simp only [preVariationFun, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : ℕ) := Q.restrict (b := s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q ∈ Q.parts, f q ≤ ∑' i, ∑ p ∈ (P i).parts, f p := by
    calc ∑ q ∈ Q.parts, f q
      _ ≤ ∑ q ∈ Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val ∩ s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          let t (i : ℕ) : Subtype MeasurableSet := ⟨q.val ∩ s i, q.2.inter (hs i)⟩
          have ht_disj : Pairwise (Disjoint on (Subtype.val ∘ t)) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val ∩ s i) := congrArg f hq_eq
            _ = f (⋃ i, (t i).val) := rfl
            _ ≤ ∑' i, f (t i) := hf t ht_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q ∈ Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)).symm
      _ = ∑' i, ∑ p ∈ (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp <| ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : ℕ) : ∑ p ∈ (P i).parts, f p ≤ preVariationFun f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

end preVariation

/-!
## Construction of measures from σ-subadditive functions
-/

variable (f : Set X → ℝ≥0∞)

/-- The `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function. -/
noncomputable def ennrealPreVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) :
    VectorMeasure X ℝ≥0∞ where
  measureOf' := preVariationFun f
  empty' := preVariation.empty f
  not_measurable' _ h := by simp [preVariationFun, h]
  m_iUnion' := preVariation.iUnion hf hf'

/-- The `Measure X` built from a σ-subadditive function. -/
noncomputable def preVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) : Measure X :=
  (ennrealPreVariation f hf hf').ennrealToMeasure

end MeasureTheory
