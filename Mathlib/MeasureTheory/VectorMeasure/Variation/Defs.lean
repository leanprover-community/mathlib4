/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure`.

Given a vector-valued measure μ we consider the problem of finding a function f such that, for any
set E, ‖μ(E)‖ ≤ f(E). This suggests defining f(E) as the supremum over partitions {Eᵢ} of E, of the
quantity ∑ᵢ, ‖μ(Eᵢ)‖. Indeed any solution of the problem must be not less than this function. It
turns out that this function actually is a measure.

## Main definitions & statements

* `VectorMeasure.variation` is the definition of the total variation measure.

## Implementation notes

Variation is defined as an `ℝ≥0∞`-valued `VectorMeasure` rather than as a `Measure`, this is
somewhat natural since we start with `VectorMeasure`.

Variation is defined for signed measures in `MeasureTheory.SignedMeasure.totalVariation`. This
definition uses the Hahn–Jordan decomposition of a signed measure. However this construction doesn't
generalize to other vector-valued measures, in particular doesn't apply to the case of complex
measures.

The notion of defining a set function as the supremum over all choices of partition of the sum gives
a measure for any subadditive set function which assigns zero measure to the emptyset. Consequently
the construction is first developed for any subadditive set function before specializing to the case
of `s ↦ ‖μ s‖ₑ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

open MeasureTheory BigOperators NNReal ENNReal Function Filter

namespace MeasureTheory.VectorMeasure

/-!
## Inner partitions

Instead of working with partitions of a set `s`, we work with finite sets of disjoints sets
contained within `s` since the same value will be achieved in the supremum. The empty set is
forbidden so that partitions of disjoint sets are disjoint sets of sets.
-/

section IsInnerPart

variable {X : Type*} [MeasurableSpace X]

/-- An inner partition is a finite collection of pairwise disjoint sets which are all contained
within a given set. Different to `Setoid.IsPartition` there is no requirement for the union to be
the entire set and the the number of partition elements is required to be finite. -/
def IsInnerPart (s : Set X) (P : Finset (Set X)) : Prop :=
    (∀ t ∈ P, t ⊆ s) ∧ (∀ t ∈ P, MeasurableSet t) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
    (∀ p ∈ P, p ≠ ∅)

lemma isInnerPart_of_empty {P : Finset (Set X)} (hP : IsInnerPart ∅ P) : P = ∅ := by
  obtain ⟨h, _, _, h'⟩ := hP
  refine Finset.eq_empty_of_forall_notMem ?_
  by_contra! hc
  obtain ⟨p, hp⟩ := hc
  exact h' p hp <| Set.subset_eq_empty (h p hp) rfl

lemma isInnerPart_self {s : Set X} (hs : MeasurableSet s) (hs' : s ≠ ∅) : IsInnerPart s {s} := by
  simpa [IsInnerPart] using ⟨hs, hs'⟩

lemma isInnerPart_monotone {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) (P : Finset (Set X))
    (hP : IsInnerPart s₁ P) : IsInnerPart s₂ P := by
  obtain ⟨h1, h2, h3, _⟩ := hP
  exact ⟨fun p hp ↦ subset_trans (h1 p hp) h, h2, h3, by simp_all⟩

open Classical in
/-- If the `s i` are pairwise disjoint sets and each `P i` is a partition of `s i` then the union of
the `P i` is a partition of `⋃ i, s i`. -/
lemma isInnerPart_iUnion {s : ℕ → Set X} (hs : Pairwise (Disjoint on s))
    {P : ℕ → Finset (Set X)} (hP : ∀ i, IsInnerPart (s i) (P i)) (n : ℕ) :
    IsInnerPart (⋃ i, s i) (Finset.biUnion (Finset.range n) P) := by
  suffices (∀ t, ∀ x < n, t ∈ P x → t ⊆ ⋃ i, s i) ∧ (∀ t, ∀ x < n, t ∈ P x → MeasurableSet t) ∧
      (⋃ x, ⋃ (_ : x < n), (P x : Set (Set X))).PairwiseDisjoint id ∧
      ∀ p, ∀ x < n, p ∈ P x → ¬p = ∅ by
    simpa [IsInnerPart]
  refine ⟨fun p i _ hp ↦ ?_, fun p i _ hp ↦ ?_, fun p hp q hq hpq _ hrp hrq ↦ ?_, fun _ i _ h' ↦ ?_⟩
  · exact Set.subset_iUnion_of_subset i ((hP i).1 p hp)
  · exact (hP i).2.1 p hp
  · obtain ⟨i, hi, hp⟩ : ∃ i < n, p ∈ P i := by simp_all
    obtain ⟨j, hj, hq⟩ : ∃ i < n, q ∈ P i := by simp_all
    obtain hc | hc : i = j ∨ i ≠ j := by omega
    · rw [hc] at hp
      simpa using Set.subset_eq_empty ((hP j).2.2.1 hp hq hpq hrp hrq) rfl
    · have hp' := (hP i).1 p hp
      have hq' := (hP j).1 q hq
      simpa using Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · exact ne_of_mem_of_not_mem h' <| fun a ↦ ((hP i).2.2.2 ∅) a rfl

/-- If P, Q are partitions of two disjoint sets then P and Q are disjoint. -/
lemma isInnerPart_of_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : IsInnerPart s P) (hQ : IsInnerPart t Q) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr
    (Finset.nonempty_iff_ne_empty.mp hc)
  have := hst (hP.1 r <| hRP hr) (hQ.1 r <| hRQ hr)
  exact hP.2.2.2 r (hRP hr) <| Set.subset_eq_empty this rfl

open Classical in
/-- The restriction of a partition `P` to the set `t`. -/
noncomputable def restriction (t : Set X) (P : Finset (Set X)) : Finset (Set X) :=
  (P.image (fun p ↦ p ∩ t)).filter (· ≠ ∅)

open Classical in
/-- If `P` is a partition then the restriction of `P` to a set `s` is a partition of `s`. -/
lemma restriction_isInnerPart {s t : Set X} {P : Finset (Set X)} (hs : IsInnerPart s P)
    (ht : MeasurableSet t) : IsInnerPart t (restriction t P) := by
  refine ⟨fun _ h ↦ ?_, fun r hr ↦ ?_, fun _ hr _ hr' ↦ ?_, fun _ hp ↦ ?_⟩
  · obtain ⟨_, _, hp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    simp [← hp]
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    simpa [← hp'] using MeasurableSet.inter (hs.2.1 p hp) ht
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr').1
    rw [← hp', ← hq']
    intro hpqt _ h h'
    have hpq : p ≠ q := fun h ↦ hpqt (congrFun (congrArg Inter.inter h) t)
    exact hs.2.2.1 hp hq hpq (Set.subset_inter_iff.mp h).1 (Set.subset_inter_iff.mp h').1
  · exact (Finset.mem_filter.mp hp).2

end IsInnerPart

/-!
## Variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all partitions `E i` of the sum of `∑ i, f (E i)`. If `f` is sub-additive then the function
defined is an `ℝ≥0∞`-valued measure.
-/

section var_aux

variable {X : Type*} [MeasurableSpace X] (f : Set X → ℝ≥0∞)

open Classical in
/-- If `s` is measurable then `var_aux s f` is the supremum over partitions `P` of `s` of the
quantity `∑ p ∈ P, f p`. If `s` is not measurable then it is set to `0`. -/
noncomputable def var_aux (s : Set X) :=
  if (MeasurableSet s) then ⨆ (P : Finset (Set X)) (_ : IsInnerPart s P), ∑ p ∈ P, f p else 0

/-- `var_aux` of the empty set is equal to zero. -/
lemma var_aux_empty' : var_aux f ∅ = 0 := by
  suffices ∀ s, IsInnerPart ∅ s → ∑ p ∈ s, f p = 0 by
    simpa [var_aux]
  intro _ hP
  simp_all [isInnerPart_of_empty hP]

lemma var_aux_zero (s : Set X) : var_aux (fun _ ↦ 0) s = 0 := by simp [var_aux]

/-- `var_aux` is monotone in terms of the set. -/
lemma var_aux_monotone {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    var_aux f s₁ ≤ var_aux f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · simp only [var_aux, hs₁, reduceIte, hs₂]
    exact iSup_le_iSup_of_subset (isInnerPart_monotone h)
  · simp [var_aux, hs₁]

lemma var_aux_lt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞} (ha : a < var_aux f s) :
    ∃ P, IsInnerPart s P ∧ a < ∑ p ∈ P, f p := by
  obtain ⟨P, hP, hP'⟩ : ∃ P, IsInnerPart s P ∧ a < ∑ p ∈ P, f p := by
    simp_all [var_aux, lt_iSup_iff]
  exact ⟨P, hP, by gcongr⟩

lemma var_aux_le {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε : 0 < ε)
    (h : var_aux f s ≠ ⊤) : ∃ P, IsInnerPart s P ∧ var_aux f s ≤ ∑ p ∈ P, f p + ε := by
  let ε' := min ε (var_aux f s).toNNReal
  have hε1 : ε' ≤ var_aux f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : var_aux f s ≠ 0 ∨ var_aux f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := var_aux f s - ε'
    have ha : a < var_aux f s := by exact ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP, hP'⟩ := var_aux_lt f hs ha
    refine ⟨P, hP, ?_⟩
    calc var_aux f s
      _ = a + ε' := (tsub_add_cancel_of_le hε1).symm
      _ ≤ ∑ p ∈ P, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP')
      _ ≤ ∑ p ∈ P, f p + ε := by gcongr
  · simp_rw [hw, zero_le, and_true]
    exact ⟨{ }, by simp, by simp, by simp, by simp⟩

lemma le_var_aux {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP : IsInnerPart s P) : ∑ p ∈ P, f p ≤ var_aux f s := by
  simpa [var_aux, hs] using le_biSup (fun P ↦ ∑ p ∈ P, f p) hP

/-- A set function is subadditive if the value assigned to the union of disjoint sets is bounded
above by the sum of the values assigned to the individual sets. -/
def IsSubadditive (f : Set X → ℝ≥0∞) := ∀ (s : ℕ → Set X), (∀ i, MeasurableSet (s i)) →
  Pairwise (Disjoint on s) → f (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), f (s i)

open Classical in
/-- Given a partition `Q`, `varOfPart μ Q` is bounded by the sum of the `varOfPart μ (P i)` where
the `P i` are the partitions formed by restricting to a disjoint set of sets `s i`. -/
lemma sum_part_le_tsum_sum_part (hf : IsSubadditive f) (hf' : f ∅ = 0) {s : ℕ → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) {Q : Finset (Set X)}
    (hQ : IsInnerPart (⋃ i, s i) Q) : ∑ q ∈ Q, f q ≤ ∑' i, ∑ p ∈ (restriction (s i) Q), f p := by
  let P (i : ℕ) := restriction (s i) Q
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
    refine hf (fun i ↦ p ∩ s i) (fun i ↦ ?_) ?_
    · exact MeasurableSet.inter (hQ.2.1 p hp) (hs i)
    · refine (Symmetric.pairwise_on (fun ⦃x y⦄ a ↦ Disjoint.symm a) fun i ↦ p ∩ s i).mpr ?_
      intro _ _ _
      exact Disjoint.inter_left' p (Disjoint.inter_right' p (hs' (by omega)))
  · -- Swapping the order of the sum.
    refine Eq.symm (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable))
  · -- By defintion of the restricted partition
    refine ENNReal.tsum_le_tsum (fun i ↦ ?_)
    calc ∑ q ∈ Q, f (q ∩ s i)
      _ = ∑ p ∈ (Finset.image (fun q ↦ q ∩ s i) Q), f p := by
        refine Eq.symm (Finset.sum_image_of_disjoint (by simp [hf']) ?_)
        intro _ hp _ hq hpq
        exact Disjoint.inter_left (s i) (Disjoint.inter_right (s i) (hQ.2.2.1 hp hq hpq))
      _ ≤  ∑ p ∈ P i, f p := by
        refine Finset.sum_le_sum_of_ne_zero (fun p hp hp' ↦ ?_)
        obtain hc | hc : p = ∅ ∨ ¬p = ∅ := eq_or_ne p ∅
        · simp [hc, hf'] at hp'
        · simp only [P, restriction, Finset.mem_filter, Finset.mem_image]
          obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hp
          exact ⟨⟨q, hq, hq'⟩, hc⟩

open Classical in
lemma le_var_aux_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (P : ℕ → Finset (Set X))
    (hP : ∀ (i : ℕ), IsInnerPart (s i) (P i)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p ≤ var_aux f (⋃ i, s i) := by
  let Q := Finset.biUnion (Finset.range n) P
  have hQ : IsInnerPart (⋃ i, s i) Q := by exact isInnerPart_iUnion hs' hP n
  calc
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ P i, f p := by simp
    _ = ∑ q ∈ Q, f q := by
      refine Eq.symm (Finset.sum_biUnion fun l _ m _ hlm ↦ ?_)
      exact isInnerPart_of_disjoint (hs' hlm) (hP l) (hP m)
    _ ≤ var_aux f (⋃ i, s i) := by
      simpa using le_var_aux f (MeasurableSet.iUnion hs) hQ

open Classical in
lemma le_var_aux_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, var_aux f (s i) ≤ var_aux f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  wlog hn : n ≠ 0
  · simp [show n = 0 by omega]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : var_aux f (s i) ≠ ⊤ := by
    refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt ?_ hsnetop
    exact var_aux_monotone f (MeasurableSet.iUnion hs) (Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a)
  -- For each set `s i` we choose a partition `P i` such that, for each `i`,
  -- `var_aux f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ var_aux_le f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, var_aux f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i), f p + ε) := by
      gcongr with i _
      exact (hP i).2
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p + ε' := by
      rw [Finset.sum_add_distrib]
      norm_cast
      simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
    _ ≤ var_aux f (⋃ i, s i) + ε' := by
      have := le_var_aux_iUnion' f hs hs' P (fun i ↦ (hP i).1) n
      gcongr

lemma sum_le_tsum' {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ b < a, ∃ n, b < ∑ i ∈ Finset.range n, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨n, hn⟩ := h b hb
  exact lt_of_lt_of_le hn (ENNReal.sum_le_tsum <| Finset.range n)

open Classical in
lemma var_aux_iUnion_le {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (hf : IsSubadditive f) (hf' : f ∅ = 0) :
    var_aux f (⋃ i, s i) ≤ ∑' i, var_aux f (s i) := by
  refine sum_le_tsum' fun b hb ↦ ?_
  simp only [var_aux, MeasurableSet.iUnion hs, reduceIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ, hbQ⟩ := hb
  -- Take the partitions defined as intersection of `Q` and `s i`.
  let P (i : ℕ) := restriction (s i) Q
  have hP (i : ℕ) : IsInnerPart (s i) (P i) := restriction_isInnerPart hQ (hs i)
  have hP' := calc
    b < ∑ q ∈ Q, f q := hbQ
    _ ≤ ∑' i, ∑ p ∈ (P i), f p := by exact sum_part_le_tsum_sum_part f hf hf' hs hs' hQ
  have := tendsto_nat_tsum fun i ↦ ∑ p ∈ (P i), f p
  obtain ⟨n, hn, _⟩ := (((tendsto_order.mp this).1 b hP').and (Ici_mem_atTop 1)).exists
  use n
  calc
    b < ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p := hn
    _ ≤ ∑ i ∈ Finset.range n, var_aux f (s i) := by
      gcongr with i hi
      exact le_var_aux f (hs i) (hP i)

/-- Additivity of `variation_aux` for disjoint measurable sets. -/
lemma var_aux_iUnion (hf : IsSubadditive f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ var_aux f (s i)) (var_aux f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (eq_of_le_of_ge ?_ ?_)
  · exact le_var_aux_iUnion f hs hs'
  · exact var_aux_iUnion_le f hs hs' hf hf'

end var_aux

/-!
## Definition of variation
-/

section variation

variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

lemma isSubadditive_enorm_vectorMeasure (μ : VectorMeasure X V) : IsSubadditive (‖μ ·‖ₑ) := by
  intro _ hs hs'
  simpa [VectorMeasure.of_disjoint_iUnion hs hs'] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
noncomputable def variation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ where
  measureOf'          := var_aux (‖μ ·‖ₑ)
  empty'              := var_aux_empty' (‖μ ·‖ₑ)
  not_measurable' _ h := if_neg h
  m_iUnion'           := var_aux_iUnion (‖μ ·‖ₑ) (isSubadditive_enorm_vectorMeasure μ) (by simp)

end variation

end MeasureTheory.VectorMeasure
