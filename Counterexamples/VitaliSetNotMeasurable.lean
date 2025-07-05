/-
Copyright (c) 2024 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Violeta Hernández Palacios
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

/-- We first enumerate all measure theoretic results that we will need.  We do so
because we want to make clear exactly which properties of measurability and the volume
measure are used in the proof of the non-measurability of the Vitali set. -/

lemma nullmeasurable_measurable_null {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := h.exists_measurable_subset_ae_eq
  use t, t_sub_s, t_m
  constructor
  · exact measure_congr t_eq_s
  · exact ae_le_set.mp t_eq_s.symm.le

lemma shift_nullmeasurable {s : Set ℝ} (h : NullMeasurableSet s volume) (c : ℝ) :
    NullMeasurableSet ((· + c) '' s) volume := by
  rcases nullmeasurable_measurable_null h with ⟨t, ts, tm, vs, vt⟩
  rw [← union_diff_cancel ts, image_union]
  have := ((measurableEmbedding_addRight c).measurableSet_image).mpr tm
  apply (this.nullMeasurableSet (μ := volume)).union_null
  rwa [image_add_right, measure_preimage_add_right]

-- TODO: move to a better place, unless this already exists!
lemma measure_union_null {α : Type*} [MeasureSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (ht : μ t = 0) : μ (s ∪ t) = μ s := by
  have hz : μ (t \ s) = 0 := by
    apply (zero_le _).antisymm'
    rw [← ht]
    exact measure_mono diff_subset
  rw [union_diff_self.symm, measure_union' disjoint_sdiff_right hs, hz, add_zero]

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
      · left; use i, i_I
      · right; use i, i_I
        rw [mem_diff]
        constructor <;> assumption
    · refine union_subset ?_ ?_
      · exact biUnion_mono (subset_refl I) t_s
      · exact biUnion_mono (subset_refl I) (fun i _ ↦ diff_subset)
  have hm_tu : MeasurableSet (⋃ i ∈ I, t i) := MeasurableSet.biUnion hc t_m
  have hv_t : volume (⋃ i ∈ I, t i) = ∑' (i : ↑I), volume (t ↑i) :=
    measure_biUnion (μ := volume) hc (hd.mono_on t_s) t_m
  rw [h_st, measure_union_null hm_tu ((measure_biUnion_null_iff hc).mpr t_z), hv_t]
  congr; ext ⟨i, i_I⟩
  rw [t_v i i_I]

/-- We now start constructing the Vitali set.

In the setoid `vitaliSetoid`, two reals in the interval [0, 1] are equivalent iff their difference
is rational. -/
instance vitaliSetoid : Setoid (Icc (0 : ℝ) 1) where
  r := fun x y ↦ y.val - x ∈ range ((↑) : ℚ → ℝ)
  iseqv := {
    refl {x} := by simp
    symm {x y}:= fun ⟨t, h⟩ ↦ ⟨-t, by simp [h]⟩
    trans {x y z} := fun ⟨t1, h1⟩ ⟨t2, h2⟩ ↦ ⟨t1 + t2, by simp [h1, h2]⟩
  }

/-- The quotient type given by `vitaliSetoid`. -/
def vitaliType : Type := Quotient vitaliSetoid

/-- The Vitali set is the range of `Quotient.out` on `vitaliType`, i.e. the range of some
arbitrary choice function. -/
def vitaliSet : Set ℝ := Set.range fun x : vitaliType ↦ x.out.val

/-- The Vitali set, shifted by `i`. -/
def vitaliShift (i : ℝ) : Set ℝ := (fun x ↦ x + i) '' vitaliSet

theorem volume_vitaliShift (i : ℝ) : volume (vitaliShift i) = volume vitaliSet := by
  simp [vitaliShift]

/-- `vitaliUnion` is the union of copies of `vitaliSet`, shifted by all rationals between
`-1` and `1`. -/
def vitaliUnion : Set ℝ := ⋃ i : Icc (-1 : ℚ) 1, vitaliShift i

/-- We now prove some results about the Vitali set and its shifts.

`vitaliSet` is a subset of [0, 1]. -/
lemma vitaliSet_subset_Icc : vitaliSet ⊆ Icc 0 1 := by
  rintro x ⟨t, rfl⟩
  exact Subtype.coe_prop _

example {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc (-1) 1) : x + y ∈ Icc (-1) 2 := by
  rw [mem_Icc] at *
  constructor <;> linarith

private theorem cast_Icc {x : ℚ} : (x : ℝ) ∈ Icc (-1) 1 ↔ x ∈ Icc (-1) 1 := by
  rw [mem_Icc, mem_Icc, ← Rat.cast_one, ← Rat.cast_neg, Rat.cast_le, Rat.cast_le]

/-- `vitaliUnion` is a subset of [-1, 2]. -/
lemma vitaliUnion_subset_Icc : vitaliUnion ⊆ Icc (-1) 2 := by
  rintro x ⟨-, ⟨y, rfl⟩, ⟨x, hx, rfl⟩⟩
  have := vitaliSet_subset_Icc hx
  have := cast_Icc.2 y.2
  simp_rw [mem_Icc] at *
  constructor <;> linarith

/-- [0, 1] is a subset of `vitaliUnion`. -/
lemma Icc_subset_vitaliUnion : Icc 0 1 ⊆ vitaliUnion := by
  intro x hx
  let z : vitaliType := ⟦⟨x, hx⟩⟧
  obtain ⟨y, hy : y = x - z.out⟩ := Quotient.mk_out (s := vitaliSetoid) ⟨x, hx⟩
  rw [vitaliUnion, Set.mem_iUnion]
  refine ⟨⟨y, cast_Icc.1 ?_⟩, ?_⟩
  · have := z.out.prop
    rw [hy, mem_Icc] at *
    constructor <;> linarith
  · rw [vitaliShift, hy, image_add_right]
    use z
    simp

/-- Therefore, the volume of vitaliUnion is between 1 and 3 (inclusive). -/
lemma volume_vitaliUnion_mem : volume vitaliUnion ∈ Icc 1 3 := by
  have h1 : volume (Icc (0 : ℝ) 1) = 1 := by simp [volume_Icc]
  have h2 : volume (Icc (-1 : ℝ) 2) = 3 := by simp [volume_Icc]; norm_num
  rw [← h1, ← h2]
  constructor
  exacts [measure_mono Icc_subset_vitaliUnion, measure_mono vitaliUnion_subset_Icc]

/-- The shifted copies of vitaliSet in vitaliUnion are pairwise disjoint. -/
lemma vitali_pairwise_disjoint : vI.PairwiseDisjoint vitaliShift := by
  intro x x_vI y y_vI x_ne_y
  refine Set.disjoint_iff.mpr ?_
  intro z
  simp only [mem_inter_iff, mem_empty_iff_false, imp_false, not_and]
  intro z_x z_y
  simp only [vitaliSet', vitaliSet, image_add_right, preimage_setOf_eq, mem_setOf_eq] at z_x z_y
  have ⟨t_x, rep_x⟩ := z_x
  have ⟨t_y, rep_y⟩ := z_y
  have vRep_eq : vitaliSetoid.r (vRep t_x) (vRep t_y) := by
    simp only [vitaliSetoid, mem_range]
    simp only [rep_x, rep_y, add_sub_add_left_eq_sub, sub_neg_eq_add]
    have : x ∈ range ((↑) : ℚ → ℝ) := by exact mem_of_mem_inter_right x_vI
    have ⟨q_x, q_x_eq⟩ := mem_range.mp (mem_of_mem_inter_right x_vI)
    have ⟨q_y, q_y_eq⟩ := mem_range.mp (mem_of_mem_inter_right y_vI)
    use -q_x + q_y, by simp [← q_x_eq, ← q_y_eq]
  have vT_eq := Quotient.sound vRep_eq
  simp only [vRep_spec] at vT_eq
  have x_eq_y : x = y := by
    calc x = z - ↑(vRep t_x) := by { simp [rep_x] }
         _ = z - ↑(vRep t_y) := by { simp [vT_eq] }
         _ = y := by { simp [rep_y] }
  contradiction

/-- This is the main result that will lead to a contradiction:
if the vitaliSet is null-measurable, then the volume of vitaliUnion is
the sum of countably many copies of vitaliSet.  -/
lemma volume_vitaliUnion (hm : NullMeasurableSet vitaliSet volume) :
    volume vitaliUnion = ∑' _ : Icc (-1 : ℚ) 1, volume vitaliSet := by
  have hm' (i : Icc (-1 : ℚ) 1) : NullMeasurableSet (vitaliShift i) volume := by
    apply shift_nullmeasurable hm
  rw [vitaliUnion, measure_iUnion₀]
  · simp_rw [volume_vitaliShift]
  · sorry
  · intro i
    rw [vitaliShift, (measurableEmbedding_addRight _).measurableSet_image]
    simp
    apply measurable_shift
  refine tsum_congr fun i ↦ ?_
  rw [vitaliSet', image_add_right, measure_preimage_add_right]

#exit
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
theorem not_nullMeasurableSet_vitaliSet : ¬ NullMeasurableSet vitaliSet volume := by
  intro hm
  rcases eq_or_ne (volume vitaliSet) 0 with hz | hnz
  · have hv : volume vitaliUnion = 0 := by
      rw [volume_vitaliUnion hm, hz, tsum_zero]
    have := vitaliUnion_volume_range.1
    simp [hv] at this
  · have hv : volume vitaliUnion = ⊤ := by
      rw [volume_vitaliUnion hm]
      have : Infinite ↑vI := vI_infinite.to_subtype
      exact ENNReal.tsum_const_eq_top_of_ne_zero hnz
    have := vitaliUnion_volume_range.2
    simp [hv] at this

/-- vitaliSet is not measurable. -/
theorem not_measurableSet_vitaliSet : ¬ MeasurableSet vitaliSet :=
  fun hm ↦ not_nullMeasurableSet_vitaliSet hm.nullMeasurableSet

end
