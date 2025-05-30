/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
import Mathlib.MeasureTheory.VectorMeasure.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Variation and total variation for vector-valued measures

This file contains the definition of variation for vector-valued measures and contains theorems of
some basic properities of variation.

Given a vector-valued measure μ we consider the problem of finding a function f such that, for any
set E, ‖μ(E)‖ ≤ f(E). This suggests defining f(E) as the supremum over partitions {Eᵢ} of E, of the
quantity ∑ᵢ, ‖μ(Eᵢ)‖. Indeed any solution of the problem must be not less than this function. It
turns out that this function actually is a measure.

## Main definitions & statements

* `VectorMeasure.variation` is the definition of the (total) variation measure.

## Implementation notes

Variation is defined as an `ℝ≥0∞`-valued `VectorMeasure` rather than as a `Measure`, this is
somewhat natural since we start with `VectorMeasure`.

Variation is defined for signed measures in `MeasureTheory.SignedMeasure.totalVariation`. This
definition uses the Hahn–Jordan decomposition of a signed measure. However this construction doesn't
generalize to other vector-valued measures, in particular doesn't work for the important case of
complex measures.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

* Total variation is a norm on the space of vector-valued measures.
* If `μ` is a `ℝ≥0∞`-valued `VectorMeasure` then `variation μ = μ`.
* Variation is equivalent to that defined via the Hahn–Jordan decomposition for signed measures.
* If `μ` is a complex measure then `variation univ < ∞`.
* Suppose that `μ` is a measure, that `g ∈ L¹(μ)` and `λ(E) = ∫_E g dμ` for each measureable `E`.
  Then `variation μ E = ∫_E |g| dμ` (Rudin Theorem 6.13).
-/

open MeasureTheory BigOperators NNReal ENNReal Function Filter

section CompleteLinearOrder

variable {α : Type*}{ι : Type*} [CompleteLinearOrder α] {s : Set α} {a b : α}

theorem lt_biSup_iff {s : Set ι} {f : ι → α} : a < ⨆ i ∈ s, f i ↔ ∃ i ∈ s, a < f i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, hi⟩ := lt_iSup_iff.mp h
    obtain ⟨his, ha⟩ := lt_iSup_iff.mp hi
    exact ⟨i, ⟨his, ha⟩⟩
  · obtain ⟨i, hi⟩ := h
    apply lt_iSup_iff.mpr
    exact ⟨i , lt_iSup_iff.mpr (by simpa [exists_prop])⟩

end CompleteLinearOrder

namespace VectorMeasure

variable {X V 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedField 𝕜]
  [NormedSpace 𝕜 V] (μ : VectorMeasure X V)

/-!
## Inner partitions

Instead of working with partitions of a set `s`, we work with finite sets of disjoints sets
contained within `s` since the same value will be achieved in the supremum.

The empty set is forbidden so that partitions of disjoint sets are disjoint sets of sets.
-/

/-- An inner partition is a finite collection of pairwise disjoint sets which are all contained
within a given set. Different to `Setoid.IsPartition` there is no requirement for the union to be
the entire set and the the number of partition elements is required to be finite. -/
def partitions (s : Set X) : Set (Finset (Set X)) :=
    {P | (∀ t ∈ P, t ⊆ s) ∧ (∀ t ∈ P, MeasurableSet t) ∧ (P.toSet.PairwiseDisjoint id) ∧
    (∀ p ∈ P, p ≠ ∅)}

lemma partitions_empty : partitions (∅ : Set X) = {∅} := by
  dsimp [partitions]
  ext P
  simp only [Set.subset_empty_iff, Finset.forall_mem_not_eq', Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro ⟨hP', a, b, hP''⟩
    by_contra! hP
    obtain ⟨p, hp⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_iff_ne_empty.mpr hP)
    simp_all [hP' p hp, ne_eq]
  · intro hp
    simp [hp]

lemma partitions_monotone {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) : partitions s₁ ⊆ partitions s₂ := by
  intro P hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  exact ⟨fun p hp ↦ subset_trans (h1 p hp) h, h2, h3, h4⟩

open Classical in
/-- If each `P i` is a partition of `s i` then the union is a partition of `⋃ i, s i`. -/
lemma partition_union {s : ℕ → Set X} (hs : Pairwise (Disjoint on s))
    {P : ℕ → Finset (Set X)} (hP : ∀ i, P i ∈ partitions (s i)) (n : ℕ):
    Finset.biUnion (Finset.range n) P ∈ partitions (⋃ i, s i) := by
  simp only [partitions, ne_eq, Finset.forall_mem_not_eq', Set.mem_setOf_eq, Finset.mem_biUnion,
    Finset.mem_range, forall_exists_index, and_imp, not_exists, not_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p i _ hp
    exact Set.subset_iUnion_of_subset i ((hP i).1 p hp)
  · intro p i _ hp
    exact (hP i).2.1 p hp
  · intro p hp q hq hpq r hrp hrq
    simp only [Set.bot_eq_empty, Set.le_eq_subset, Set.subset_empty_iff]
    simp only [id_eq, Set.le_eq_subset] at hrp hrq
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_Iio, Set.mem_iUnion, Finset.mem_coe,
      exists_prop] at hp hq
    obtain ⟨i, hi, hp⟩ := hp
    obtain ⟨j, hj, hq⟩ := hq
    obtain hc | hc : i = j ∨ i ≠ j := by omega
    · rw [hc] at hp
      exact Set.subset_eq_empty ((hP j).2.2.1 hp hq hpq hrp hrq) rfl
    · have hp' := (hP i).1 p hp
      have hq' := (hP j).1 q hq
      exact Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · intro i _ h
    exact (hP i).2.2.2 ∅ h rfl

/-- If P, Q are partitions of two disjoint sets then P and Q are disjoint. -/
lemma partitions_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : P ∈ partitions s) (hQ : Q ∈ partitions t) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hc
  have := hst (hP.1 r <| hRP hr) (hQ.1 r <| hRQ hr)
  have := hP.2.2.2 r (hRP hr)
  simp_all

open Classical in
/-- If `P` is a partition then the restriction of `P` to a set `s` is a partition of `s`. -/
lemma partition_restrict {s t : Set X} {P : Finset (Set X)} (hs : P ∈ partitions s)
    (ht : MeasurableSet t) : (P.image (fun p ↦ p ∩ t)).filter (· ≠ ∅) ∈ partitions t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ h
    obtain ⟨_, _, hp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    simp [← hp]
  · intro r hr
    obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    rw [← hp']
    exact MeasurableSet.inter (hs.2.1 p hp) ht
  · intro _ hr _ hr'
    obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr').1
    rw [← hp', ← hq']
    intro hpqt
    have hpq : p ≠ q := fun h ↦ hpqt (congrFun (congrArg Inter.inter h) t)
    intro a ha ha'
    have hap : a ≤ p := by
      simp only [id_eq, Set.le_eq_subset, Set.subset_inter_iff] at ha
      exact ha.1
    have haq : a ≤ q := by
      simp only [id_eq, Set.le_eq_subset, Set.subset_inter_iff] at ha'
      exact ha'.1
    exact hs.2.2.1 hp hq hpq hap haq
  · intro _ hp
    exact (Finset.mem_filter.mp hp).2

/-!
## Definition of variation
-/

/-- Given a partition `E` of a set `s`, this returns the sum of the norm of the measure of the
elements of that partition. -/
private noncomputable def varOfPart (P : Finset (Set X)) := ∑ p ∈ P, ‖μ p‖ₑ

open Classical in
/-- The variation of a measure is defined as the supremum over all partitions of the sum of the norm
of the measure of each partition element. -/
noncomputable def variation_aux (s : Set X) :=
    if (MeasurableSet s) then ⨆ P ∈ partitions s, varOfPart μ P else 0

/-- `variation_aux` of the empty set is equal to zero. -/
lemma variation_empty' : variation_aux μ ∅ = 0 := by
  simp [variation_aux, varOfPart, partitions_empty]

/-- variation_aux is monotone as a function of the set. -/
lemma variation_aux_monotone {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) : variation_aux μ s₁ ≤ variation_aux μ s₂ := by
  simp only [variation_aux, hs₁, reduceIte, hs₂]
  exact iSup_le_iSup_of_subset (partitions_monotone h)

lemma variation_aux_lt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞} (ha : a < variation_aux μ s) :
    ∃ P ∈ partitions s, a < varOfPart μ P := by
  simp only [variation_aux, hs, reduceIte] at ha
  exact lt_biSup_iff.mp ha

lemma variation_aux_le' {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε: 0 < ε)
    (h : variation_aux μ s ≠ ⊤) :
    ∃ P ∈ partitions s, variation_aux μ s ≤ varOfPart μ P + ε := by
  let ε' := min ε (variation_aux μ s).toNNReal
  have hε1 : ε' ≤ variation_aux μ s := by simp_all [ε']
  have _ : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : variation_aux μ s ≠ 0 ∨ variation_aux μ s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := variation_aux μ s - ε'
    have ha : a < variation_aux μ s := by
      dsimp [a]
      refine ENNReal.sub_lt_self h hw (by positivity)
    have ha' : variation_aux μ s = a + ε' := by
      exact Eq.symm (tsub_add_cancel_of_le hε1)
    obtain ⟨P, hP, hP'⟩ := variation_aux_lt μ hs ha
    refine ⟨P, hP, ?_⟩
    calc variation_aux μ s
      _ = a + ε' := ha'
      _ ≤ varOfPart μ P + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP')
      _ ≤ varOfPart μ P + ε := by gcongr
  · simp_rw [hw, zero_le, and_true]
    exact ⟨{}, by simp, by simp [hs], by simp, by simp⟩

lemma le_variation_aux {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP : P ∈ partitions s) : varOfPart μ P ≤ variation_aux μ s := by
  simp only [variation_aux, hs, reduceIte]
  exact le_biSup (varOfPart μ) hP

open Classical in
/-- Given a partition `Q`, `varOfPart μ Q` is bounded by the sum of the `varOfPart μ (P i)` where
the `P i` are the partitions formed by restricting to a disjoint set of sets `s i`. -/
lemma varOfPart_le_tsum {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) {Q : Finset (Set X)} (hQ : Q ∈ partitions (⋃ i, s i)) :
    varOfPart μ Q ≤ ∑' i, varOfPart μ ({x ∈ Finset.image (fun q ↦ q ∩ s i) Q | x ≠ ∅}) := by
  let P (i : ℕ) := (Q.image (fun q ↦ q ∩ (s i))).filter (· ≠ ∅)
  calc
    _ = ∑ q ∈ Q, ‖μ q‖ₑ := by simp [varOfPart]
    _ = ∑ q ∈ Q, ‖μ (⋃ i, q ∩ s i)‖ₑ := ?_
    _ ≤ ∑ q ∈ Q, ∑' i, ‖μ (q ∩ s i)‖ₑ := ?_
    _ = ∑' i, ∑ q ∈ Q, ‖μ (q ∩ s i)‖ₑ := ?_
    _ ≤ ∑' i, ∑ p ∈ (P i), ‖μ p‖ₑ := ?_
    _ = ∑' i, (varOfPart μ (P i)) := by simp [varOfPart]
  · -- Each `q` is equal to the union of `q ∩ s i`.
    suffices h : ∀ q ∈ Q, q = ⋃ i, q ∩ s i by
      refine Finset.sum_congr rfl (fun q hq ↦ ?_)
      simp_rw [← h q hq]
    intro q hq
    ext x
    constructor
    · intro hx
      obtain ⟨_, hs⟩ := (hQ.1 q hq) hx
      obtain ⟨i, _⟩ := Set.mem_range.mp hs.1
      simp_all [Set.mem_iUnion_of_mem i]
    · intro _
      simp_all
  · -- Additivity of the measure since the `s i` are pairwise disjoint.
    gcongr with p hp
    have : μ (⋃ i, p ∩ s i) = ∑' i, μ (p ∩ s i) := by
      have hps : ∀ i, MeasurableSet (p ∩ s i) := by
        intro i
        refine MeasurableSet.inter (hQ.2.1 p hp) (hs i)
      have hps' : Pairwise (Disjoint on fun i ↦ p ∩ s i) := by
        refine (Symmetric.pairwise_on (fun ⦃x y⦄ a ↦ Disjoint.symm a) fun i ↦ p ∩ s i).mpr ?_
        intro _ _ _
        refine Disjoint.inter_left' p (Disjoint.inter_right' p ?_)
        exact hs' (by omega)
      exact VectorMeasure.of_disjoint_iUnion hps hps'
    rw [this]
    exact enorm_tsum_le_tsum_enorm
  · -- Swapping the order of the sum.
    refine Eq.symm (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable))
  · -- By defintion of the restricted partition
    refine ENNReal.tsum_le_tsum ?_
    intro i
    calc ∑ q ∈ Q, ‖μ (q ∩ s i)‖ₑ
      _ = ∑ p ∈ (Finset.image (fun q ↦ q ∩ s i) Q), ‖μ p‖ₑ := by
        refine Eq.symm (Finset.sum_image_of_disjoint ?_ ?_)
        · simp
        · intro p hp q hq hpq
          refine Disjoint.inter_left (s i) (Disjoint.inter_right (s i) ?_)
          exact hQ.2.2.1 hp hq hpq
      _ ≤  ∑ p ∈ P i, ‖μ p‖ₑ := by
        refine Finset.sum_le_sum_of_ne_zero ?_
        intro p hp hp'
        dsimp [P]
        obtain hc | hc : p = ∅ ∨ ¬p = ∅ := eq_or_ne p ∅
        · simp [hc] at hp'
        · rw [Finset.mem_filter, Finset.mem_image]
          refine ⟨?_, hc⟩
          obtain ⟨q, _, _⟩ := Finset.mem_image.mp hp
          use q

/-- Aditivity of `variation_aux` for disjoint measurable sets. -/
lemma variation_m_iUnion' (s : ℕ → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ variation_aux μ (s i)) (variation_aux μ (⋃ i, s i)) := by
  rw [ENNReal.hasSum_iff_bounds_nat]
  constructor
  · -- The sum of `variation_aux μ (s i)` is le `variation_aux μ (⋃ i, s i)`.
    intro n
    wlog hn : n ≠ 0
    · simp [show n = 0 by omega]
    apply ENNReal.le_of_forall_pos_le_add
    intro ε' hε' hsnetop
    let ε := ε' / n
    have hε : 0 < ε := by positivity
    have hs'' i : variation_aux μ (s i) ≠ ⊤ := by
      have : s i ⊆ ⋃ i, s i := Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
      have := variation_aux_monotone μ this (hs i) (MeasurableSet.iUnion hs)
      exact lt_top_iff_ne_top.mp <| lt_of_le_of_lt this hsnetop
    -- For each set `s i` we choose a partition `P i` such that, for each `i`,
    -- `variation_aux μ (s i) ≤ varOfPart μ (P i) + ε`.
    choose P hP using fun i ↦ variation_aux_le' μ (hs i) (hε) (hs'' i)
    calc ∑ i ∈ Finset.range n, variation_aux μ (s i)
      _ ≤ ∑ i ∈ Finset.range n, (varOfPart μ (P i) + ε) := by
        gcongr with i hi
        exact (hP i).2
      _ = ∑ i ∈ Finset.range n, varOfPart μ (P i) + ε' := by
        rw [Finset.sum_add_distrib]
        norm_cast
        simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
      _ ≤ variation_aux μ (⋃ i, s i) + ε' := by
        -- Since the union of the partitions `P i` is a partition of `⋃ i, s i`, we know that
        -- `∑' i, varOfPart μ (E i) ≤ variation_aux μ (⋃ i, s i)`.
        suffices h : ∑ i ∈ Finset.range n, varOfPart μ (P i) ≤ variation_aux μ (⋃ i, s i) by gcongr
        classical
        let Q := Finset.biUnion (Finset.range n) P
        have hQ : Q ∈ partitions (⋃ i, s i) := partition_union hs' (fun i ↦ (hP i).1) n
        calc
          _ = ∑ i ∈ Finset.range n, ∑ p ∈ P i, ‖μ p‖ₑ := by simp [varOfPart]
          _ = ∑ q ∈ Q, ‖μ q‖ₑ := by
            refine Eq.symm (Finset.sum_biUnion ?_)
            intro l _ m _ hlm
            exact partitions_disjoint (hs' hlm) (hP l).1 (hP m).1
          _ ≤ variation_aux μ (⋃ i, s i) := by
            have := le_variation_aux μ (MeasurableSet.iUnion hs) hQ
            simpa
  · -- Variation of the union, `variation_aux μ (⋃ i, s i)` le the sum of `variation_aux μ (s i)`.
    intro b hb
    -- simp only [variation_aux, hs, reduceIte]
    simp only [variation_aux, MeasurableSet.iUnion hs, reduceIte] at hb
    obtain ⟨Q, hQ, hbQ⟩ := lt_biSup_iff.mp hb
    -- Take the partitions defined as intersection of `Q` and `s i`.
    classical
    let P (i : ℕ) := (Q.image (fun q ↦ q ∩ (s i))).filter (· ≠ ∅)
    have hP (i : ℕ) : P i ∈ partitions (s i) := partition_restrict hQ (hs i)
    have hP' := calc
      b < varOfPart μ Q := hbQ
      _ ≤ ∑' i, varOfPart μ (P i) := by exact varOfPart_le_tsum μ hs hs' hQ
    have := tendsto_nat_tsum fun i ↦ VectorMeasure.varOfPart μ (P i)
    obtain ⟨n, hn, hn'⟩ := (((tendsto_order.mp this).1 b hP').and (Ici_mem_atTop 1)).exists
    use n
    calc
      b < ∑ i ∈ Finset.range n, varOfPart μ (P i) := hn
      _ ≤ ∑ i ∈ Finset.range n, variation_aux μ (s i) := by
        gcongr with i hi
        exact le_variation_aux μ (hs i) (hP i)

/-- The variation of a vector-valued measure as a `VectorMeasure`. -/
noncomputable def variation : VectorMeasure X ℝ≥0∞ where
  measureOf'          := variation_aux μ
  empty'              := variation_empty' μ
  not_measurable' _ h := if_neg h
  m_iUnion'           := variation_m_iUnion' μ

end VectorMeasure

/-!
## Section : properties of variation
-/

namespace VectorMeasure
variable {X V 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedField 𝕜]
  [NormedSpace 𝕜 V]

theorem norm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ ≤ variation μ E := by
  wlog hE' : E ≠ ∅
  · push_neg at hE'
    simp [hE', varOfPart, partitions_empty]
  by_cases hE : MeasurableSet E
  · have h : {E} ∈ partitions E := ⟨by simp, by simpa, by simp, by simpa⟩
    have := le_biSup (fun P ↦ ∑ p ∈ P, ‖μ p‖ₑ) h
    simp_all [varOfPart, variation, variation_aux]
  · simp [hE, μ.not_measurable' hE]

end VectorMeasure
