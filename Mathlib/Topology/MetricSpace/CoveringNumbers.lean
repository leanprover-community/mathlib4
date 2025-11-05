/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Markus Himmel, Lorenzo Luccioli, Alessio Rondelli, Etienne Marion
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.MetricSpace.Cover

/-!
# Covering numbers

We define covering numbers of sets in a pseudo-metric space, which are minimal cardinalities of
`ε`-covers of sets. We also define the packing number, which is the maximal cardinality of
an `ε`-separated set.

We prove inequalities between these covering and packing numbers.

## Main definitions

* `IsCover`: a set `C` is an `ε`-cover of another set `A` if every point in `A` belongs to a ball
  with radius `ε` around a point of `C`.
* `externalCoveringNumber`: the extenal covering number of a set `A` for radius `ε` is the minimal
  cardinal of an `ε`cover.
* `coveringNumber`: the covering number(or internal covering number) of a set `A` for radius `ε` is
  the minimal cardinal of an `ε`cover contained in `A`.
* `packingNumber`: the packing number of a set `A` for radius `ε` is the maximal cardinal of
  an `ε`-separated set in `A`.

## Main statements

* `externalCoveringNumber_le_coveringNumber`: the external covering number is less than or equal to
  the covering number.
* `packingNumber_two_le_externalCoveringNumber`: the packing number with radius `2 * ε` is
  less than or equal to the external covering number for `ε`.

## References

* [R. Vershynin, *High-dimensional probability*][vershynin2018high]

-/

open EMetric Set
open scoped ENNReal NNReal

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X] {A B C : Set X} {ε δ : ℝ≥0} {x : X}

section IsCover

lemma isCover_singleton_of_ediam_le (hA : EMetric.diam A ≤ ε) (hx : x ∈ A) :
    IsCover ε A ({x} : Set X) :=
  fun _ h_mem ↦ ⟨x, by simp, (edist_le_diam_of_mem h_mem hx).trans hA⟩

lemma isCover_singleton_finset_of_ediam_le (hA : EMetric.diam A ≤ ε) (hx : x ∈ A) :
    IsCover ε A ({x} : Finset X) :=
  fun _ h_mem ↦ ⟨x, by simp, (edist_le_diam_of_mem h_mem hx).trans hA⟩

/-- A totally bounded set has finite `ε`-covers for all `ε > 0`. -/
lemma TotallyBounded.exists_isCover (hA : TotallyBounded A) (hε : 0 < ε) :
    ∃ C : Finset X, ↑C ⊆ A ∧ IsCover ε A (C : Set X) := by
  rw [EMetric.totallyBounded_iff'] at hA
  obtain ⟨C, hCA, hC_finite, hC⟩ := hA ε (mod_cast hε)
  simp only [isCover_iff_subset_iUnion_emetricClosedBall, Finset.mem_coe]
  refine ⟨Set.Finite.toFinset hC_finite, by simpa, ?_⟩
  · simp only [Set.Finite.mem_toFinset]
    refine hC.trans fun x hx ↦ ?_
    simp only [Set.mem_iUnion, EMetric.mem_ball, exists_prop, EMetric.mem_closedBall] at hx ⊢
    obtain ⟨y, hyC, hy⟩ := hx
    exact ⟨y, hyC, hy.le⟩

end IsCover

section CoveringNumber

section Definitions

/-- The extenal covering number of a set `A` in `X` for radius `ε` is the minimal cardinal of
an `ε`cover by points in `X` (not necessarily in `A`). -/
noncomputable
def externalCoveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Finset X) (_ : IsCover ε A C), C.card

/-- The covering number(or internal covering number) of a set `A` for radius `ε` is
the minimal cardinal of an `ε`cover contained in `A`. -/
noncomputable
def coveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Finset X) (_ : ↑C ⊆ A) (_ : IsCover ε A C), C.card

/-- The packing number of a set `A` for radius `ε` is the maximal cardinal of an `ε`-separated set
in `A`. -/
noncomputable
def packingNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨆ (C : Finset X) (_ : ↑C ⊆ A) (_ : IsSeparated ε (C : Set X)), C.card

end Definitions

@[simp]
lemma externalCoveringNumber_empty (ε : ℝ≥0) : externalCoveringNumber ε (∅ : Set X) = 0 := by
  simp [externalCoveringNumber]

@[simp]
lemma coveringNumber_empty (ε : ℝ≥0) : coveringNumber ε (∅ : Set X) = 0 := by simp [coveringNumber]

@[simp]
lemma externalCoveringNumber_eq_zero :
    externalCoveringNumber ε A = 0 ↔ A = ∅ := by simp [externalCoveringNumber]

@[simp]
lemma coveringNumber_eq_zero : coveringNumber ε A = 0 ↔ A = ∅ := by simp [coveringNumber]

lemma externalCoveringNumber_le_card {C : Finset X} (hC : IsCover ε A C) :
    externalCoveringNumber ε A ≤ C.card := iInf₂_le C hC

lemma coveringNumber_le_card {C : Finset X} (h_subset : ↑C ⊆ A) (hC : IsCover ε A C) :
    coveringNumber ε A ≤ C.card := (iInf₂_le C h_subset).trans (iInf_le _ hC)

lemma externalCoveringNumber_anti (h : ε ≤ δ) :
    externalCoveringNumber δ A ≤ externalCoveringNumber ε A := by
  simp_rw [externalCoveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover ↦ h_cover.mono_radius h)

lemma coveringNumber_anti (h : ε ≤ δ) : coveringNumber δ A ≤ coveringNumber ε A := by
  simp_rw [coveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover ↦ h_cover.mono_radius h)

lemma externalCoveringNumber_mono_set (h : A ⊆ B) :
    externalCoveringNumber ε A ≤ externalCoveringNumber ε B := by
  simp only [externalCoveringNumber, le_iInf_iff]
  exact fun C hC ↦ iInf_le_of_le C <| iInf_le_of_le (hC.anti h) le_rfl

lemma coveringNumber_eq_one_of_diam_le (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ ε) :
    coveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ ≤ ({a} : Finset X).card :=
        coveringNumber_le_card (by simp [ha]) (isCover_singleton_finset_of_ediam_le hA ha)
      _ ≤ 1 := by simp
  · by_contra! h
    rw [ENat.lt_one_iff_eq_zero] at h
    refine h_nonempty.ne_empty (by simpa using h)

lemma externalCoveringNumber_eq_one_of_diam_le (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ ε) :
    externalCoveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc externalCoveringNumber ε A
      _ ≤ ({a} : Finset X).card :=
        externalCoveringNumber_le_card (isCover_singleton_finset_of_ediam_le hA ha)
      _ ≤ 1 := by simp
  · by_contra! h
    rw [ENat.lt_one_iff_eq_zero] at h
    refine h_nonempty.ne_empty (by simpa using h)

lemma externalCoveringNumber_le_one_of_diam_le (hA : EMetric.diam A ≤ ε) :
    externalCoveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_diam_le h_nonempty hA).le

lemma coveringNumber_le_one_of_diam_le (hA : EMetric.diam A ≤ ε) : coveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← coveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (coveringNumber_eq_one_of_diam_le h_nonempty hA).le

section Comparisons

lemma externalCoveringNumber_le_coveringNumber (ε : ℝ≥0) (A : Set X) :
    externalCoveringNumber ε A ≤ coveringNumber ε A := by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover

theorem packingNumber_two_le_externalCoveringNumber (A : Set X) (hε : ε ≠ ∞) :
    packingNumber (2 * ε) A ≤ externalCoveringNumber ε A := by
  simp only [packingNumber, externalCoveringNumber, le_iInf_iff, iSup_le_iff, Nat.cast_le]
  intro C hC_cover D hD_subset hD_separated
  let f : D → C := fun x ↦
    ⟨(hC_cover (hD_subset x.2)).choose, (hC_cover (hD_subset x.2)).choose_spec.1⟩
  have hf' (x : D) : edist x.1 (f x) ≤ ε := (hC_cover (hD_subset x.2)).choose_spec.2
  suffices Function.Injective f from Finset.card_le_card_of_injective this
  intro x y hfxy
  by_contra hxy
  specialize hD_separated x.2 y.2 ?_
  · rwa [Subtype.ext_iff] at hxy
  suffices 0 < edist (f x) (f y) by simp [hfxy] at this
  have hx_ne_top : edist x.1 (f x) ≠ ∞ := ne_top_of_le_ne_top hε (hf' x)
  have hy_ne_top : edist y.1 (f y) ≠ ∞ := ne_top_of_le_ne_top hε (hf' y)
  calc 0
  _ ≤ 2 * ε - edist x.1 (f x) - edist y.1 (f y) := zero_le'
  _ < edist x y - edist x.1 (f x) - edist y.1 (f y) := by
    rw [lt_tsub_iff_left, lt_tsub_iff_left]
    refine lt_of_eq_of_lt ?_ hD_separated
    rw [add_comm (edist y.1 _), ENNReal.sub_add_eq_add_sub _ hy_ne_top,
      ENNReal.add_sub_cancel_right hy_ne_top, add_comm,
      ENNReal.sub_add_eq_add_sub _ hx_ne_top, ENNReal.add_sub_cancel_right hx_ne_top]
    · norm_cast
    · refine (hf' x).trans ?_
      rw [two_mul]
      exact le_self_add
    · refine ENNReal.le_sub_of_add_le_left hx_ne_top ?_
      rw [two_mul]
      gcongr
      · exact hf' x
      · exact hf' y
  _ ≤ (edist x.1 (f x) + edist (f x) (f y) + edist (f y : X) y.1)
      - edist x.1 (f x) - edist y.1 (f y) := by
    gcongr
    exact edist_triangle4 x.1 (f x) (f y) y.1
  _ = edist (f x) (f y) := by
    simp only [hfxy, edist_self, add_zero]
    rw [edist_comm (f y : X), add_comm, ENNReal.add_sub_cancel_right, tsub_self]
    rw [← hfxy]
    exact hx_ne_top

end Comparisons

end CoveringNumber

end Metric
