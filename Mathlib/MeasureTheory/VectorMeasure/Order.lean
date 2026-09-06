/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Operations

/-!

# Order structure on vector measures

This file defines the pointwise order on vector measures, comparison after restriction to a set,
and the conversion of nonnegative or nonpositive parts of signed measures to ordinary measures.

## Main definitions

* `VectorMeasure.instPartialOrder` is the pointwise partial order on vector measures.
* `v ≤[i] w` means that `v.restrict i ≤ w.restrict i`.
* `SignedMeasure.toMeasureOfZeroLE` and `SignedMeasure.toMeasureOfLEZero` turn positive and
  negative restrictions of signed measures into ordinary measures.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.
-/

public section

noncomputable section

open NNReal ENNReal

open scoped Function -- required for scoped `on` notation
namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

open Set

namespace VectorMeasure

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `Measure.instPartialOrder`. -/
instance instPartialOrder : PartialOrder (VectorMeasure α M) where
  le v w := ∀ i, MeasurableSet i → v i ≤ w i
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm _ _ h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

variable {v w : VectorMeasure α M}

theorem le_iff : v ≤ w ↔ ∀ i, MeasurableSet i → v i ≤ w i := Iff.rfl

theorem le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i := by
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]

end

/-- `v ≤[i] w` is notation for `v.restrict i ≤ w.restrict i`. -/
scoped[MeasureTheory]
  notation3:50 v " ≤[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i ≤ MeasureTheory.VectorMeasure.restrict w i

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M)

theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
    v ≤[i] w ↔ ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun _ hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) Set.inter_subset_right⟩

theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v ≤[i] w)
    {j : Set α} (hj : j ⊆ i) : v j ≤ w j := by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]

theorem restrict_le_restrict_of_subset_le {i : Set α}
    (h : ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j) : v ≤[i] w := by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]

theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w)
    (hij : j ⊆ i) : v ≤[j] w :=
  restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)

theorem le_restrict_empty : v ≤[∅] w := by
  simp

theorem le_restrict_univ_iff_le : v ≤[Set.univ] w ↔ v ≤ w := by
  simp

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M] [IsTopologicalAddGroup M]
variable (v w : VectorMeasure α M)

nonrec theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v ≤[i] w) : -w ≤[i] -v := by
  intro j hj₁
  rw [restrict_apply _ hi hj₁, restrict_apply _ hi hj₁, neg_apply, neg_apply]
  refine neg_le_neg ?_
  rw [← restrict_apply _ hi hj₁, ← restrict_apply _ hi hj₁]
  exact h j hj₁

theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w ≤[i] -v ↔ v ≤[i] w :=
  ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] [OrderClosedTopology M]
variable (v w : VectorMeasure α M) {i j : Set α}

theorem restrict_le_restrict_iUnion {f : ℕ → Set α} (hf₁ : ∀ n, MeasurableSet (f n))
    (hf₂ : ∀ n, v ≤[f n] w) : v ≤[⋃ n, f n] w := by
  refine restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => ?_
  have ha₃ : ⋃ n, a ∩ disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
  have ha₄ : Pairwise (Disjoint on fun n => a ∩ disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃, v.of_disjoint_iUnion _ ha₄, w.of_disjoint_iUnion _ ha₄]
  · refine Summable.tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) ?_ ?_)
      ?_ ?_
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact Set.Subset.trans Set.inter_subset_right (disjointed_subset _ _)
    · refine (v.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
    · refine (w.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)

theorem restrict_le_restrict_countable_iUnion [Countable β] {f : β → Set α}
    (hf₁ : ∀ b, MeasurableSet (f b)) (hf₂ : ∀ b, v ≤[f b] w) : v ≤[⋃ b, f b] w := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine restrict_le_restrict_iUnion v w ?_ ?_
  · intro n
    measurability
  · intro n
    rcases Encodable.decode₂ β n with - | b
    · simp
    · simp [hf₂ b]

theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hj₁ : MeasurableSet j)
    (hj₂ : v ≤[j] w) : v ≤[i ∪ j] w := by
  rw [Set.union_eq_iUnion]
  refine restrict_le_restrict_countable_iUnion v w ?_ ?_
  · measurability
  · rintro (_ | _) <;> simpa

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v : VectorMeasure α M) {i j : Set α}

theorem nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) : 0 ≤ v i := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

theorem nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) : v i ≤ 0 := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 ≤[i] v := by
  rw [restrict_zero, restrict_not_measurable _ hi]

theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v ≤[i] 0 := by
  rw [restrict_zero, restrict_not_measurable _ hi]

theorem measurable_of_not_zero_le_restrict (hi : ¬0 ≤[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi

theorem measurable_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi

theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v) : 0 ≤[j] v :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0) : v ≤[j] 0 :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [LinearOrder M]
variable (v : VectorMeasure α M) {i j : Set α}

theorem exists_pos_measure_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ 0 < v j := by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push Not at hi
  exact hi

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
  [AddLeftMono M] [ContinuousAdd M]

instance instAddLeftMono : AddLeftMono (VectorMeasure α M) :=
  ⟨fun _ _ _ h i hi => by simp only [_root_.add_apply]; grw [h i hi]⟩

end


end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open MeasureTheory

/-- The underlying function for `SignedMeasure.toMeasureOfZeroLE`. -/
def toMeasureOfZeroLE' (s : SignedMeasure α) (i : Set α) (hi : 0 ≤[i] s) (j : Set α)
    (hj : MeasurableSet j) : ℝ≥0∞ :=
  ((↑) : ℝ≥0 → ℝ≥0∞) (.mk (s.restrict i j) (le_trans (by simp) (hi j hj)))

/-- Given a signed measure `s` and a positive measurable set `i`, `toMeasureOfZeroLE`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
def toMeasureOfZeroLE (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 ≤[i] s) :
    Measure α := by
  refine Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) ?_ ?_
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
  · intro f hf₁ hf₂
    have h₁ : ∀ n, MeasurableSet (i ∩ f n) := fun n => hi₁.inter (hf₁ n)
    have h₂ : Pairwise (Disjoint on fun n : ℕ => i ∩ f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion h₁ h₂]
    have h : ∀ n, 0 ≤ s (i ∩ f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ Set.inter_subset_left hi₂)
    rw [NNReal.coe_tsum_of_nonneg h, ENNReal.coe_tsum]
    · refine tsum_congr fun n => ?_
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable

variable (s : SignedMeasure α) {i j : Set α}

theorem toMeasureOfZeroLE_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfZeroLE i hi₁ hi j = ((↑) : ℝ≥0 → ℝ≥0∞) (.mk (s (i ∩ j)) (nonneg_of_zero_le_restrict
      s (zero_le_restrict_subset s hi₁ Set.inter_subset_left hi))) := by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]

theorem toMeasureOfZeroLE_real_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfZeroLE i hi₁ hi).real j = s (i ∩ j) := by
  simp [measureReal_def, toMeasureOfZeroLE_apply, hj₁]

/-- Given a signed measure `s` and a negative measurable set `i`, `toMeasureOfLEZero`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`. -/
def toMeasureOfLEZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s ≤[i] 0) :
    Measure α :=
  toMeasureOfZeroLE (-s) i hi₁ <| @neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi₂

theorem toMeasureOfLEZero_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfLEZero i hi₁ hi j =
    ((↑) : ℝ≥0 → ℝ≥0∞) (NNReal.mk (-s (i ∩ j)) (neg_apply s (i ∩ j) ▸
      nonneg_of_zero_le_restrict _ (zero_le_restrict_subset _ hi₁ Set.inter_subset_left
      (@neg_zero (VectorMeasure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi)))) := by
  simp [toMeasureOfLEZero, toMeasureOfZeroLE_apply _ _ _ hj₁]

theorem toMeasureOfLEZero_real_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfLEZero i hi₁ hi).real j = -s (i ∩ j) := by
  simp [measureReal_def, toMeasureOfLEZero_apply _ hi hi₁ hj₁]

/-- `SignedMeasure.toMeasureOfZeroLE` is a finite measure. -/
instance toMeasureOfZeroLE_finite (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfZeroLE i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

/-- `SignedMeasure.toMeasureOfLEZero` is a finite measure. -/
instance toMeasureOfLEZero_finite (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfLEZero i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

theorem toMeasureOfZeroLE_toSignedMeasure (hs : 0 ≤[Set.univ] s) :
    (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs).toSignedMeasure = s := by
  ext i hi
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi, measureReal_def]

theorem toMeasureOfLEZero_toSignedMeasure (hs : s ≤[Set.univ] 0) :
    (s.toMeasureOfLEZero Set.univ MeasurableSet.univ hs).toSignedMeasure = -s := by
  ext i hi
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi, measureReal_def]

end SignedMeasure

namespace Measure

open VectorMeasure

variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α)

theorem zero_le_toSignedMeasure : 0 ≤ μ.toSignedMeasure := by
  rw [← le_restrict_univ_iff_le]
  refine restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => ?_
  simp [hj₁]

theorem toSignedMeasure_toMeasureOfZeroLE :
    μ.toSignedMeasure.toMeasureOfZeroLE Set.univ MeasurableSet.univ
      ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeasure μ)) = μ := by
  refine Measure.ext fun i hi => ?_
  lift μ i to ℝ≥0 using (measure_lt_top _ _).ne with m hm
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi, ENNReal.coe_inj]
  congr
  simp [hi, ← hm, measureReal_def]

theorem toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext A hA
  simp [VectorMeasure.restrict_apply, hA, hs]

theorem toSignedMeasure_le_toSignedMeasure_iff :
    μ.toSignedMeasure ≤ ν.toSignedMeasure ↔ μ ≤ ν := by
  rw [Measure.le_iff, VectorMeasure.le_iff]
  congrm ∀ s, (hs : MeasurableSet s) → ?_
  simp_rw [toSignedMeasure_apply_measurable hs, real_def]
  apply ENNReal.toReal_le_toReal <;> finiteness

end Measure

end MeasureTheory
