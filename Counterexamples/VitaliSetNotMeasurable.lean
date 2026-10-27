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

/-- In the setoid `vitaliSetoid`, two reals in the interval `[0, 1]` are equivalent iff their
difference is rational. -/
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

/-! We now prove some results about the Vitali set and its shifts. -/

/-- If `vitaliSet` is null-measurable, then so are all of its shifts. -/
theorem nullMeasurableSet_vitaliShift (hm : NullMeasurableSet vitaliSet volume) (i : ℝ) :
    NullMeasurableSet (vitaliShift i) volume := by
  rw [vitaliShift, image_add_right]
  exact hm.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving

/-- `vitaliUnion` is the union of copies of `vitaliSet`, shifted by all rationals between
`-1` and `1`. -/
def vitaliUnion : Set ℝ := ⋃ i : Icc (-1 : ℚ) 1, vitaliShift i

/-- `vitaliSet` is a subset of `[0, 1]`. -/
lemma vitaliSet_subset_Icc : vitaliSet ⊆ Icc 0 1 := by
  rintro x ⟨t, rfl⟩
  exact Subtype.coe_prop _

private theorem cast_Icc {x : ℚ} : (x : ℝ) ∈ Icc (-1) 1 ↔ x ∈ Icc (-1) 1 := by
  rw [mem_Icc, mem_Icc, ← Rat.cast_one, ← Rat.cast_neg, Rat.cast_le, Rat.cast_le]

/-- `vitaliUnion` is a subset of `[-1, 2]`. -/
lemma vitaliUnion_subset_Icc : vitaliUnion ⊆ Icc (-1) 2 := by
  rintro x ⟨-, ⟨y, rfl⟩, ⟨x, hx, rfl⟩⟩
  have := vitaliSet_subset_Icc hx
  have := cast_Icc.2 y.2
  simp_rw [mem_Icc] at *
  constructor <;> linarith

/-- `[0, 1]` is a subset of `vitaliUnion`. -/
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

/-- The volume of `vitaliUnion` is between `1` and `3` (inclusive). -/
lemma volume_vitaliUnion_mem : volume vitaliUnion ∈ Icc 1 3 := by
  have h1 : volume (Icc (0 : ℝ) 1) = 1 := by simp [volume_Icc]
  have h2 : volume (Icc (-1 : ℝ) 2) = 3 := by simp [volume_Icc]; norm_num
  rw [← h1, ← h2]
  constructor
  exacts [measure_mono Icc_subset_vitaliUnion, measure_mono vitaliUnion_subset_Icc]

/-- Shifts of `vitaliSet` by distinct rationals are disjoint. -/
lemma disjoint_vitaliShift {i j : ℚ} (h : i ≠ j) :
    Disjoint (vitaliShift i) (vitaliShift j) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ ⟨_, ⟨b, rfl⟩, hb⟩
  obtain rfl : a = b := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    exact Quotient.sound ⟨i - j, by push_cast; linarith⟩
  exact h (by exact_mod_cast (add_left_cancel hb).symm)

/-- If `vitaliSet` is null-measurable, then the volume of `vitaliUnion` is the sum of countably
many copies of the volume of `vitaliSet`. -/
lemma volume_vitaliUnion (hm : NullMeasurableSet vitaliSet volume) :
    volume vitaliUnion = ∑' _ : Icc (-1 : ℚ) 1, volume vitaliSet := by
  rw [vitaliUnion, measure_iUnion₀]
  · simp_rw [volume_vitaliShift]
  · exact fun i j hij ↦ (disjoint_vitaliShift (Subtype.coe_injective.ne hij)).aedisjoint
  · exact fun i ↦ nullMeasurableSet_vitaliShift hm i

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
