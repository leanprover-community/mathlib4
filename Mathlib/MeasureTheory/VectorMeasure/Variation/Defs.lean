/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Subpartition

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function actually is a measure.

## Main definition

* `VectorMeasure.variation` is the definition of the total variation measure.

## Implementation notes

Variation is defined as an `ℝ≥0∞`-valued `VectorMeasure` rather than as a `Measure`, this is
somewhat natural since we start with `VectorMeasure`. The corresponding `Measure` is given by
`VectorMeasure.ennrealToMeasure`.

Variation is defined for signed measures in `MeasureTheory.SignedMeasure.totalVariation`. This
definition uses the Hahn–Jordan decomposition of a signed measure. However this construction doesn't
generalize to other vector-valued measures, in particular doesn't apply to the case of complex
measures.

The notion of defining a set function as the supremum over all choices of partition of the sum gives
a measure for any subadditive set function which assigns zero measure to the empty set. Consequently
the construction is first developed for any subadditive set function before specializing to the case
of `s ↦ ‖μ s‖ₑ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

open MeasureTheory BigOperators ENNReal Function

namespace MeasureTheory

/-!
## Variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all partitions `E i` of the sum of `∑ i, f (E i)`. If `f` is sub-additive then the function
defined is an `ℝ≥0∞`-valued measure.
-/

section

variable {X : Type*} [MeasurableSpace X] (f : Set X → ℝ≥0∞)

open Classical in
/-- If `s` is measurable then `preVariation s f` is the supremum over subpartitions
(`IsSubpartition`) `P` of `s` of the quantity `∑ p ∈ P, f p`. If `s` is not measurable then it is
set to `0`. -/
noncomputable def preVariation (s : Set X) :=
  if (MeasurableSet s) then ⨆ (P : Finset (Set X)) (_ : IsSubpartition s P), ∑ p ∈ P, f p else 0

end

namespace preVariation

variable {X : Type*} [MeasurableSpace X] (f : Set X → ℝ≥0∞)

/-- `preVariation` of the empty set is equal to zero. -/
lemma empty : preVariation f ∅ = 0 := by
  suffices ∀ s, IsSubpartition ∅ s → ∑ p ∈ s, f p = 0 by
    simpa [preVariation]
  intro _ hP
  simp_all [IsSubpartition.eq_empty hP]

/-- `preVariation` is monotone in terms of the (measurable) set. -/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    preVariation f s₁ ≤ preVariation f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · simp only [preVariation, hs₁, reduceIte, hs₂]
    exact iSup_le_iSup_of_subset (IsSubpartition.mono h)
  · simp [preVariation, hs₁]

lemma exists_isSubpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < preVariation f s) : ∃ P, IsSubpartition s P ∧ a < ∑ p ∈ P, f p := by
  simp_all [preVariation, lt_iSup_iff]

lemma exists_isSubpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε : 0 < ε)
    (h : preVariation f s ≠ ⊤) : ∃ P, IsSubpartition s P ∧ preVariation f s ≤ ∑ p ∈ P, f p + ε := by
  let ε' := min ε (preVariation f s).toNNReal
  have hε1 : ε' ≤ preVariation f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : preVariation f s ≠ 0 ∨ preVariation f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariation f s - ε'
    have ha : a < preVariation f s := by exact ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP, hP'⟩ := exists_isSubpartition_sum_gt f hs ha
    refine ⟨P, hP, ?_⟩
    calc preVariation f s
      _ = a + ε' := (tsub_add_cancel_of_le hε1).symm
      _ ≤ ∑ p ∈ P, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP')
      _ ≤ ∑ p ∈ P, f p + ε := by gcongr
  · simp_rw [hw, zero_le, and_true]
    exact ⟨{ }, by simp, by simp, by simp, by simp⟩

lemma sum_le {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP : IsSubpartition s P) : ∑ p ∈ P, f p ≤ preVariation f s := by
  simpa [preVariation, hs] using le_biSup (fun P ↦ ∑ p ∈ P, f p) hP

/-- A set function is subadditive if the value assigned to the union of disjoint sets is bounded
above by the sum of the values assigned to the individual sets. -/
def IsSubadditive (f : Set X → ℝ≥0∞) := ∀ (s : ℕ → Set X), (∀ i, MeasurableSet (s i)) →
  Pairwise (Disjoint on s) → f (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), f (s i)

/-- Given a subpartition `Q`, `∑ q ∈ Q, f q` is bounded by the sum of the `∑ q ∈ (P i), f q` where
the `P i` are the subpartitions formed by restricting to a disjoint set of sets `s i`. -/
lemma sum_part_le_tsum_sum_part (hf : IsSubadditive f) (hf' : f ∅ = 0) {s : ℕ → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) {Q : Finset (Set X)}
    (hQ : IsSubpartition (⋃ i, s i) Q) :
    ∑ q ∈ Q, f q ≤ ∑' i, ∑ p ∈ (IsSubpartition.restriction (s i) Q), f p := by
  classical
  let P (i : ℕ) := IsSubpartition.restriction (s i) Q
  calc ∑ q ∈ Q, f q
    _ = ∑ q ∈ Q, f (⋃ i, q ∩ s i) := ?_
    _ ≤ ∑ q ∈ Q, ∑' i, f (q ∩ s i) := ?_
    _ = ∑' i, ∑ q ∈ Q, f (q ∩ s i) := ?_
    _ ≤ ∑' i, ∑ p ∈ (P i), f p := ?_
  · -- Each `q` is equal to the union of `q ∩ s i`.
    -- TO DO: This only needs one direction of the argument since subadditivity implies monotone.
    suffices h : ∀ q ∈ Q, q = ⋃ i, q ∩ s i by
      exact Finset.sum_congr rfl (fun q hq ↦ (by simp [← h q hq]))
    intro q hq
    ext x
    refine ⟨fun hx ↦ ?_, by simp_all⟩
    obtain ⟨_, hs⟩ := (hQ.1 q hq) hx
    obtain ⟨i, _⟩ := Set.mem_range.mp hs.1
    simp_all [Set.mem_iUnion_of_mem i]
  · -- Subadditivity of `f` since the `s i` are pairwise disjoint.
    suffices h : ∀ p ∈ Q, f (⋃ i, p ∩ s i) ≤ ∑' (i : ℕ), f (p ∩ s i) by exact Finset.sum_le_sum h
    intro p hp
    refine hf (fun (i : ℕ) ↦ p ∩ s i) (fun i ↦ ?_) ?_
    · exact MeasurableSet.inter (hQ.measurableSet p hp) (hs i)
    · refine (Symmetric.pairwise_on (fun ⦃x y⦄ a ↦ Disjoint.symm a) fun i ↦ p ∩ s i).mpr ?_
      intro _ _ _
      exact Disjoint.inter_left' p (Disjoint.inter_right' p (hs' (by omega)))
  · -- Swapping the order of the sum.
    refine Eq.symm (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable))
  · -- By defintion of the restricted subpartition
    refine ENNReal.tsum_le_tsum (fun i ↦ ?_)
    calc ∑ q ∈ Q, f (q ∩ s i)
      _ = ∑ p ∈ (Finset.image (fun q ↦ q ∩ s i) Q), f p := by
        refine Eq.symm (Finset.sum_image_of_disjoint (by simp [hf']) ?_)
        intro _ hp _ hq hpq
        exact Disjoint.inter_left (s i) (Disjoint.inter_right (s i) (hQ.disjoint hp hq hpq))
      _ ≤  ∑ p ∈ P i, f p := by
        refine Finset.sum_le_sum_of_ne_zero (fun p hp hp' ↦ ?_)
        obtain hc | hc : p = ∅ ∨ ¬p = ∅ := eq_or_ne p ∅
        · simp [hc, hf'] at hp'
        · simp only [P, IsSubpartition.restriction, Finset.mem_filter, Finset.mem_image]
          obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hp
          refine ⟨⟨q, hq, hq'⟩, ?_⟩
          exact Set.nonempty_iff_ne_empty.mpr hc

lemma sum_le_preVariation_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (P : ℕ → Finset (Set X))
    (hP : ∀ (i : ℕ), IsSubpartition (s i) (P i)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p ≤ preVariation f (⋃ i, s i) := by
  classical
  let Q := Finset.biUnion (Finset.range n) P
  have hQ : IsSubpartition (⋃ i, s i) Q := by exact IsSubpartition.iUnion hs' hP (Finset.range n)
  calc
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ P i, f p := by simp
    _ = ∑ q ∈ Q, f q := by
      refine Eq.symm (Finset.sum_biUnion fun l _ m _ hlm ↦ ?_)
      exact IsSubpartition.disjoint_of_disjoint (hs' hlm) (hP l) (hP m)
    _ ≤ preVariation f (⋃ i, s i) := by
      simpa using sum_le f (MeasurableSet.iUnion hs) hQ

lemma sum_le_preVariation_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariation f (s i) ≤ preVariation f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  wlog hn : n ≠ 0
  · simp [show n = 0 by omega]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : preVariation f (s i) ≠ ⊤ := by
    refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt ?_ hsnetop
    exact mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a)
  -- For each set `s i` we choose a subpartition `P i` such that, for each `i`,
  -- `preVariation f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_isSubpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, preVariation f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i), f p + ε) := by
      gcongr with i _
      exact (hP i).2
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p + ε' := by
      rw [Finset.sum_add_distrib]
      norm_cast
      simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
    _ ≤ preVariation f (⋃ i, s i) + ε' := by
      have := sum_le_preVariation_iUnion' f hs hs' P (fun i ↦ (hP i).1) n
      gcongr

lemma sum_le_tsum' {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ b < a, ∃ n, b < ∑ i ∈ Finset.range n, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨n, hn⟩ := h b hb
  exact lt_of_lt_of_le hn (ENNReal.sum_le_tsum <| Finset.range n)

open Classical in
lemma iUnion_le {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (hf : IsSubadditive f) (hf' : f ∅ = 0) :
    preVariation f (⋃ i, s i) ≤ ∑' i, preVariation f (s i) := by
  refine sum_le_tsum' fun b hb ↦ ?_
  simp only [preVariation, MeasurableSet.iUnion hs, reduceIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ, hbQ⟩ := hb
  -- Take the subpartitions defined as intersection of `Q` and `s i`.
  let P (i : ℕ) := IsSubpartition.restriction (s i) Q
  have hP (i : ℕ) : IsSubpartition (s i) (P i) :=
    IsSubpartition.restriction_of_measurableSet hQ (hs i)
  have hP' := calc
    b < ∑ q ∈ Q, f q := hbQ
    _ ≤ ∑' i, ∑ p ∈ (P i), f p := by exact sum_part_le_tsum_sum_part f hf hf' hs hs' hQ
  have := tendsto_nat_tsum fun i ↦ ∑ p ∈ (P i), f p
  obtain ⟨n, hn, _⟩ := (((tendsto_order.mp this).1 b hP').and (Filter.Ici_mem_atTop 1)).exists
  use n
  calc
    b < ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p := hn
    _ ≤ ∑ i ∈ Finset.range n, preVariation f (s i) := by
      gcongr with i hi
      exact sum_le f (hs i) (hP i)

/-- Additivity of `variation_aux` for disjoint measurable sets. -/
lemma iUnion (hf : IsSubadditive f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ preVariation f (s i)) (preVariation f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (eq_of_le_of_ge ?_ ?_)
  · exact sum_le_preVariation_iUnion f hs hs'
  · exact iUnion_le f hs hs' hf hf'

end preVariation

/-!
## Definition of variation
-/

namespace VectorMeasure

open MeasureTheory.VectorMeasure preVariation

variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

lemma isSubadditive_enorm_vectorMeasure (μ : VectorMeasure X V) : IsSubadditive (‖μ ·‖ₑ) := by
  intro _ hs hs'
  simpa [VectorMeasure.of_disjoint_iUnion hs hs'] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ where
  measureOf' := preVariation (‖μ ·‖ₑ)
  empty' := preVariation.empty (‖μ ·‖ₑ)
  not_measurable' _ h := if_neg h
  m_iUnion' := iUnion (‖μ ·‖ₑ) (isSubadditive_enorm_vectorMeasure μ) (by simp)

/-- The variation of a `VectorMeasure` as a `Measure`. -/
noncomputable def variation (μ : VectorMeasure X V) := (ennrealVariation μ).ennrealToMeasure

end VectorMeasure

end MeasureTheory
