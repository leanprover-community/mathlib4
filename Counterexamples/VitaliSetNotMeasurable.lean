/-
Copyright (c) 2024-present Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou <chingtsun.chou@gmail.com>
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Vitali set and its non-measurability

This file defines the Vitali set and proves that it is not measurable.
The proof is essentially the one in Wikipedia:

## References

* <https://en.wikipedia.org/wiki/Vitali_set>
-/

open Set Filter Real MeasureTheory

noncomputable section

/-- We first derive the measure theoretic results that we need from
the more general theorems in Mathlib. -/

example {a b : ℝ} : volume (Icc a b) = ENNReal.ofReal (b - a) :=
  volume_Icc

lemma volume_mono {s t : Set ℝ} (h : s ⊆ t) : volume s ≤ volume t := by
  exact OuterMeasureClass.measure_mono volume h

lemma measurable_nullmeasurable {s : Set ℝ} (h : MeasurableSet s) : NullMeasurableSet s volume :=
  MeasurableSet.nullMeasurableSet h

lemma measurable_null_nullmeasurable {s t : Set ℝ}
    (hm : NullMeasurableSet s) (hn : volume t = 0) : NullMeasurableSet (s ∪ t) :=
  NullMeasurableSet.union_null hm hn

lemma nullmeasurable_measurable_null {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := NullMeasurableSet.exists_measurable_subset_ae_eq h
  use t, t_sub_s, t_m
  constructor
  · exact measure_congr t_eq_s
  · refine ae_le_set.mp ?_
    exact t_eq_s.symm.le

lemma shift_volume (s : Set ℝ) (c : ℝ) : volume ((fun x ↦ x + c)''s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

lemma shift_nullmeasurable {s : Set ℝ} (h : NullMeasurableSet s volume) (c : ℝ) :
    NullMeasurableSet ((fun x ↦ x + c)''s) volume := by
  rcases nullmeasurable_measurable_null h with ⟨t, ts, tm, vs, vt⟩
  rw [← union_diff_cancel ts, image_union]
  refine measurable_null_nullmeasurable ?_ ?_
  · have : MeasurableSet ((fun x ↦ x + c)''t) := by
      apply (MeasurableEmbedding.measurableSet_image ?_).mpr tm
      exact measurableEmbedding_addRight c
    exact measurable_nullmeasurable this
  · rw [shift_volume (s \ t), vt]

lemma union_volume_null {s t : Set ℝ} (hs : MeasurableSet s) (ht : volume t = 0) :
    volume (s ∪ t) = volume s := by
  have hu : s ∪ t = s ∪ (t \ s) := union_diff_self.symm
  have hd : Disjoint s (t \ s) := disjoint_sdiff_right
  have hz : volume (t \ s) = 0 := by
    apply le_antisymm
    · rw [← ht]
      exact volume_mono diff_subset
    · exact zero_le (volume (t \ s))
  rw [hu, measure_union' hd hs, hz]
  abel

lemma biUnion_null {ι : Type*} {I : Set ι} {f : ι → Set ℝ}
    (hs : I.Countable) : volume (⋃ i ∈ I, f i) = 0 ↔ ∀ i ∈ I, volume (f i) = 0 :=
  measure_biUnion_null_iff hs

lemma biUnion_volume {ι : Type*} {I : Set ι} {s : ι → Set ℝ}
    (hc : I.Countable) (hd : I.PairwiseDisjoint s) (hm : ∀ i ∈ I, NullMeasurableSet (s i) volume) :
    volume (⋃ i ∈ I, s i) = ∑' (i : ↑I), volume (s ↑i) := by
  have : ∀ i ∈ I, ∃ t ⊆ s i, MeasurableSet t ∧ volume t = volume (s i) ∧ volume (s i \ t) = 0 := by
    intro i i_I
    exact nullmeasurable_measurable_null (hm i i_I)
  choose! t t_s t_m t_v t_z using this
  have h_st : ⋃ i ∈ I, s i = (⋃ i ∈ I, t i) ∪ (⋃ i ∈ I, (s i \ t i)) := by
    -- This is probably not the most elegant proof of this rather trivial fact.
    refine le_antisymm ?_ ?_
    · intro x
      simp only [mem_union, mem_iUnion₂]
      rintro ⟨i, i_I, x_s⟩
      rcases em (x ∈ t i) with x_t | x_nt
      · left ; use i, i_I
      · right ; use i, i_I
        rw [mem_diff]
        constructor <;> assumption
    · refine union_subset ?_ ?_
      · exact biUnion_mono (subset_refl I) t_s
      · refine biUnion_mono (subset_refl I) ?_
        intro i ?_
        exact diff_subset
  have hm_ti : ∀ i ∈ I, MeasurableSet (t i) := by
    intro i i_I
    exact t_m i i_I
  have hm_tu : MeasurableSet (⋃ i ∈ I, t i) := by
    exact MeasurableSet.biUnion hc hm_ti
  have h_null : volume (⋃ i ∈ I, (s i \ t i)) = 0 := by
    exact (biUnion_null hc).mpr t_z
  have hv_s : volume (⋃ i ∈ I, s i) = volume (⋃ i ∈ I, t i) := by
    rw [h_st, union_volume_null hm_tu h_null]
  have hd_t : I.PairwiseDisjoint t := by
    refine PairwiseDisjoint.mono_on hd ?_
    exact t_s
  have hv_t : volume (⋃ i ∈ I, t i) = ∑' (i : ↑I), volume (t ↑i) := by
    exact measure_biUnion (μ := volume) hc hd_t hm_ti
  rw [hv_s, hv_t]
  refine tsum_congr ?_
  rintro ⟨i, i_I⟩
  rw [t_v i i_I]

/-- We now start constructing the Vitali set.

In the setoid vS, two reals in the interval [0,1] are equivalent
iff their difference is rational. -/
instance vS : Setoid { x : ℝ // x ∈ Icc 0 1 } where
  r := fun x y ↦ (↑ x : ℝ) - (↑ y) ∈ range ((↑) : ℚ → ℝ)
  iseqv := {
    refl := by
      intro x
      simp only [sub_self, mem_range, Rat.cast_eq_zero, exists_eq]
    symm := by
      intro x y
      simp only [mem_range]
      rintro ⟨t, h⟩
      use (-t)
      simp [h]
    trans := by
      intro x y z
      simp only [mem_range]
      rintro ⟨t1, h1⟩
      rintro ⟨t2, h2⟩
      use (t1 + t2)
      simp [h1, h2]
  }

/-- Make a quotient type vT from the setoid vS. -/
def vT : Type := Quotient vS

lemma vS_vT_surj : ∀ t : vT, ∃ x : { x : ℝ // x ∈ Icc 0 1 }, ⟦x⟧ = t := by
  intro t
  have ⟨x, eq⟩ := Quotient.mk_surjective t
  use x, eq

/-- Use Classical.choose to make a function vRep from vT to vS. -/
def vRep : vT → { x : ℝ // x ∈ Icc 0 1 } :=
  fun t ↦ Classical.choose (vS_vT_surj t)

lemma vRep_spec : ∀ t : vT, ⟦vRep t⟧ = t :=
  fun t ↦ Classical.choose_spec (vS_vT_surj t)

/-- The Vitali set is the image of vRep. -/
def vitaliSet : Set ℝ := { x : ℝ | ∃ t : vT, ↑(vRep t) = x }

/-- We now shift the Vitali set using rational numbers in the interval [-1,1]. -/
def vI : Set ℝ := Icc (-1) 1 ∩ range ((↑) : ℚ → ℝ)

def vitaliSet' (i : ℝ) : Set ℝ := (fun x ↦ x + i)''vitaliSet

/-- vitaliUnion is the union of all those shifted copies of vitaliSet. -/
def vitaliUnion : Set ℝ := ⋃ i ∈ vI, vitaliSet' i

/-- We now prove some results about the Vitali set and its shifts.

vitaliSet is a subset of [0,1]. -/
lemma vitaliSet_upper_bound : vitaliSet ⊆ Icc 0 1 := by
  rintro x ⟨t, ht⟩
  rw [← ht]
  exact (vRep t).property

/-- vitaliUnion is a subset of [-1,2]. -/
lemma vitaliUnion_upper_bound : vitaliUnion ⊆ Icc (-1) 2 := by
  refine iUnion₂_subset ?_
  intro i
  rw [vI, Set.mem_inter_iff]
  rintro ⟨h0, _⟩
  refine image_subset_iff.mpr ?_
  simp only [preimage_add_const_Icc]
  rw [mem_Icc] at h0
  have h1 : -1 - i ≤ 0 := by linarith
  have h2 : 1 ≤ 2 - i := by linarith
  have : Icc 0 1 ⊆ Icc (-1 - i) (2 - i) := Icc_subset_Icc h1 h2
  exact subset_trans vitaliSet_upper_bound this

/-- [0,1] is a subset of vitaliUnion. -/
lemma vitaliUnion_lower_bound : Icc 0 1 ⊆ vitaliUnion := by
  intro x h_x1
  have ⟨x', h_x2⟩ : ∃ x' : { x : ℝ // x ∈ Icc 0 1 }, ↑ x' = x := CanLift.prf x h_x1
  let y : ℝ := ↑(vRep ⟦x'⟧)
  have h_y1 : y ∈ Icc 0 1 := (vRep ⟦x'⟧).property
  have h_y2 : y ∈ vitaliSet := by
    simp [y, vitaliSet]
  have h_xy1 : x - y ∈ range ((↑) : ℚ → ℝ) := by
    have eq : vS.r x' (vRep ⟦x'⟧) := by
      refine Quotient.eq.mp ?_
      symm
      apply vRep_spec
    simp only [Setoid.r] at eq
    simpa [← h_x2]
  have h_xy2 : x - y ∈ Icc (-1) 1 := by
    simp only [mem_Icc] at h_x1 h_y1 ⊢
    constructor <;> linarith
  simp only [vitaliUnion, image_add_right, mem_iUnion, mem_preimage, exists_prop]
  use (x - y)
  constructor
  · rw [vI, mem_inter_iff]
    constructor <;> assumption
  · simpa [vitaliSet']

/-- Therefore, the volume of vitaliUnion is between 1 and 3 (inclusive). -/
lemma vitaliUnion_volume_range : 1 ≤ volume vitaliUnion ∧ volume vitaliUnion ≤ 3 := by
  have h1 : MeasureTheory.volume (Icc (0 : ℝ) 1) = 1 := by simp [volume_Icc]
  have h2 : MeasureTheory.volume (Icc (-1 : ℝ) 2) = 3 := by simp [volume_Icc] ; norm_num
  constructor
  · rw [← h1]
    exact volume_mono vitaliUnion_lower_bound
  · rw [← h2]
    exact volume_mono vitaliUnion_upper_bound

/-- The shifted copies of vitaliSet in vitaliUnion are pairwise disjoint. -/
lemma vitali_pairwise_disjoint : vI.PairwiseDisjoint vitaliSet' := by
  intro x x_vI y y_vI x_ne_y
  refine Set.disjoint_iff.mpr ?_
  intro z
  simp only [mem_inter_iff, mem_empty_iff_false, imp_false, not_and]
  intro z_x z_y
  simp only [vitaliSet', vitaliSet, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_x
  simp only [vitaliSet', vitaliSet, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_y
  have ⟨t_x, rep_x⟩ := z_x
  have ⟨t_y, rep_y⟩ := z_y
  have vRep_eq : vS.r (vRep t_x) (vRep t_y) := by
    simp only [vS, mem_range]
    simp only [rep_x, rep_y, add_sub_add_left_eq_sub, sub_neg_eq_add]
    have : x ∈ range ((↑) : ℚ → ℝ) := by exact mem_of_mem_inter_right x_vI
    have ⟨q_x, q_x_eq⟩ := mem_range.mp (mem_of_mem_inter_right x_vI)
    have ⟨q_y, q_y_eq⟩ := mem_range.mp (mem_of_mem_inter_right y_vI)
    use (-q_x + q_y)
    simp [← q_x_eq, ← q_y_eq]
  have vT_eq := Quotient.sound vRep_eq
  simp only [vRep_spec] at vT_eq
  have x_eq_y : x = y := by
    calc x = z - ↑(vRep t_x) := by { simp [rep_x] }
         _ = z - ↑(vRep t_y) := by { simp [vT_eq] }
         _ = y := by { simp [rep_y] }
  contradiction

/-- vI is a countable set. -/
lemma vI_countable : vI.Countable := by
  refine Countable.mono inter_subset_right ?_
  apply countable_range

/-- This is the main result that will lead to a contradiction:
if the vitaliSet is null-measurable, then the volume of vitaliUnion is
the sum of countably many copies of vitaliSet.  -/
lemma vitaliUnion_volume_sum (hm : NullMeasurableSet vitaliSet volume) :
    volume vitaliUnion = ∑' (_ : ↑vI), volume vitaliSet := by
  have hm' : ∀ i ∈ vI, NullMeasurableSet (vitaliSet' i) volume := by
    intro i i_vI
    rw [vitaliSet']
    apply shift_nullmeasurable hm
  rw [vitaliUnion, biUnion_volume vI_countable vitali_pairwise_disjoint hm']
  refine tsum_congr ?_
  intro i
  rw [vitaliSet', shift_volume]

/-- vI is an infinite set. -/
lemma vI_infinite : vI.Infinite := by
  let f : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have f_inj : f.Injective := by { intro m n ; simp [f] }
  have f_rng_inf : (range f).Infinite := infinite_range_of_injective f_inj
  refine Set.Infinite.mono ?_ f_rng_inf
  apply range_subset_iff.mpr
  intro n
  simp [f, vI]
  constructor
  · simp only [inv_eq_one_div]
    have h1 : (0 : ℝ) < ↑n + 1 := by
      have : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
      linarith
    constructor
    · rw [le_div_iff₀' h1]
      linarith
    · rw [div_le_iff₀' h1]
      linarith
  · use ((↑ n + 1)⁻¹)
    simp

/-- The following theorems are the main results.

vitaliSet is not null-measurable. -/
theorem vitaliSet_not_nullmeasurable : ¬ (NullMeasurableSet vitaliSet volume) := by
  intro hm
  rcases eq_or_ne (volume vitaliSet) 0 with hz | hnz
  · have hv : volume vitaliUnion = 0 := by
      rw [vitaliUnion_volume_sum hm, hz, tsum_zero]
    have := vitaliUnion_volume_range.1
    simp [hv] at this
  · have hv : volume vitaliUnion = ⊤ := by
      rw [vitaliUnion_volume_sum hm]
      have : Infinite ↑vI := vI_infinite.to_subtype
      exact ENNReal.tsum_const_eq_top_of_ne_zero hnz
    have := vitaliUnion_volume_range.2
    simp [hv] at this

/-- vitaliSet is not measurable. -/
theorem vitaliSet_not_measurable : ¬ (MeasurableSet vitaliSet) := by
  intro hm
  exact vitaliSet_not_nullmeasurable (measurable_nullmeasurable hm)

end
