/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Markus Himmel, Lorenzo Luccioli, Alessio Rondelli, Etienne Marion
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Covering numbers

We define covering numbers of sets in a pseudo-metric space, which are minimal cardinalities of
`ε`-covers of sets by closed balls.
We also define the packing number, which is the maximal cardinality of an `ε`-separated set.

We prove inequalities between these covering and packing numbers.

## Main definitions

* `externalCoveringNumber`: the extenal covering number of a set `A` for radius `ε` is the minimal
  cardinality (in `ℕ∞`) of an `ε`-cover.
* `coveringNumber`: the covering number (or internal covering number) of a set `A` for radius `ε` is
  the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`.
* `packingNumber`: the packing number of a set `A` for radius `ε` is the maximal cardinality of
  an `ε`-separated set in `A`.

We define sets achieving these minimal/maximal cardinalities when they exist:
* `minimalCover`: a finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
* `maximalSeparatedSet`: a finite `ε`-separated subset of a set `A` with maximal cardinality.

## Main statements

We have the following inequalities between covering and packing numbers:
* `externalCoveringNumber_le_coveringNumber`: external covering number ≤ covering number.
* `packingNumber_two_mul_le_externalCoveringNumber`: packing number for `2 * ε` ≤ external covering
  number for `ε`.
* `coveringNumber_le_packingNumber`: covering number ≤ packing number.
* `coveringNumber_two_mul_le_externalCoveringNumber`: covering number for `2 * ε` ≤ external
  covering number for `ε`.

The covering number is not monotone for set inclusion (because the cover must be contained
in the set), but we have the following inequality:
* `coveringNumber_subset_le`: if `A ⊆ B`, then `coveringNumber ε A ≤ coveringNumber (ε / 2) B`.

## References

* [R. Vershynin, *High-dimensional probability*][vershynin2018high]

-/

@[expose] public section

open EMetric Set
open scoped ENNReal NNReal

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X] {A B C : Set X} {ε δ : ℝ≥0} {x : X}

section Definitions

/-- The external covering number of a set `A` in `X` for radius `ε` is the minimal cardinality
(in `ℕ∞`) of an `ε`-cover by points in `X` (not necessarily in `A`). -/
noncomputable
def externalCoveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

/-- The covering number (or internal covering number) of a set `A` for radius `ε` is
the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`. -/
noncomputable
def coveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : C ⊆ A) (_ : IsCover ε A C), C.encard

/-- The packing number of a set `A` for radius `ε` is the maximal cardinality (in `ℕ∞`)
of an `ε`-separated set in `A`. -/
noncomputable
def packingNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨆ (C : Set X) (_ : C ⊆ A) (_ : IsSeparated ε C), C.encard

end Definitions

@[simp]
lemma externalCoveringNumber_empty (ε : ℝ≥0) : externalCoveringNumber ε (∅ : Set X) = 0 := by
  simp [externalCoveringNumber]

@[simp]
lemma coveringNumber_empty (ε : ℝ≥0) : coveringNumber ε (∅ : Set X) = 0 := by simp [coveringNumber]

@[simp]
lemma packingNumber_empty (ε : ℝ≥0) : packingNumber ε (∅ : Set X) = 0 := by simp [packingNumber]

@[simp]
lemma externalCoveringNumber_eq_zero :
    externalCoveringNumber ε A = 0 ↔ A = ∅ := by simp [externalCoveringNumber]

@[simp]
lemma externalCoveringNumber_pos_iff : 0 < externalCoveringNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]
lemma coveringNumber_eq_zero : coveringNumber ε A = 0 ↔ A = ∅ := by simp [coveringNumber]

@[simp]
lemma coveringNumber_pos_iff : 0 < coveringNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]
lemma packingNumber_eq_zero : packingNumber ε A = 0 ↔ A = ∅ := by
  simp only [packingNumber, ENat.iSup_eq_zero, encard_eq_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra!
  obtain ⟨x, hx⟩ := this
  simpa using h {x} (by simp [hx]) (by simp)

@[simp]
lemma packingNumber_pos_iff : 0 < packingNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

lemma externalCoveringNumber_le_coveringNumber (ε : ℝ≥0) (A : Set X) :
    externalCoveringNumber ε A ≤ coveringNumber ε A := by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover

lemma IsCover.externalCoveringNumber_le_encard (hC : IsCover ε A C) :
    externalCoveringNumber ε A ≤ C.encard := iInf₂_le C hC

lemma IsCover.coveringNumber_le_encard (h_subset : C ⊆ A) (hC : IsCover ε A C) :
    coveringNumber ε A ≤ C.encard := (iInf₂_le C h_subset).trans (iInf_le _ hC)

lemma IsSeparated.encard_le_packingNumber (h_subset : C ⊆ A) (hC : IsSeparated ε C) :
    C.encard ≤ packingNumber ε A := le_iSup₂_of_le C h_subset (le_iSup_of_le hC le_rfl)

lemma externalCoveringNumber_le_encard_self (A : Set X) : externalCoveringNumber ε A ≤ A.encard :=
  IsCover.externalCoveringNumber_le_encard (by simp)

lemma coveringNumber_le_encard_self (A : Set X) : coveringNumber ε A ≤ A.encard :=
  IsCover.coveringNumber_le_encard (by simp) (by simp)

lemma packingNumber_le_encard_self (A : Set X) : packingNumber ε A ≤ A.encard := by
  simp only [packingNumber, iSup_le_iff]
  exact fun _ hC _ ↦ encard_le_encard hC

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

@[simp]
lemma externalCoveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    externalCoveringNumber 0 A = A.encard := by
  refine le_antisymm (externalCoveringNumber_le_encard_self A) ?_
  refine le_iInf fun C ↦ le_iInf fun hC₁ ↦ ?_
  rw [isCover_zero] at hC₁
  exact encard_le_encard hC₁

@[simp]
lemma coveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    coveringNumber 0 A = A.encard := by
  refine le_antisymm (coveringNumber_le_encard_self A) ?_
  rw [← externalCoveringNumber_zero]
  exact externalCoveringNumber_le_coveringNumber 0 A

@[simp]
lemma packingNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    packingNumber 0 A = A.encard :=
  le_antisymm (packingNumber_le_encard_self A) (le_iSup_of_le A (by simp))

lemma coveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : ediam A ≤ ε) :
    coveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ ≤ ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ ≤ 1 := by simp
  · simpa [Order.one_le_iff_pos]

lemma externalCoveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty)
    (hA : ediam A ≤ ε) :
    externalCoveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · simpa [Order.one_le_iff_pos]

lemma externalCoveringNumber_le_one_of_ediam_le (hA : ediam A ≤ ε) :
    externalCoveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_ediam_le h_nonempty hA).le

lemma coveringNumber_le_one_of_ediam_le (hA : ediam A ≤ ε) : coveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← coveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (coveringNumber_eq_one_of_ediam_le h_nonempty hA).le

@[simp]
lemma coveringNumber_singleton (ε : ℝ≥0) (x : X) : coveringNumber ε {x} = 1 :=
  coveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]
lemma externalCoveringNumber_singleton (ε : ℝ≥0) (x : X) : externalCoveringNumber ε {x} = 1 :=
  externalCoveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]
lemma packingNumber_singleton (ε : ℝ≥0) (x : X) : packingNumber ε {x} = 1 :=
  le_antisymm ((packingNumber_le_encard_self {x}).trans_eq (by simp)) <|
    le_iSup_of_le {x} <| le_iSup_of_le (by simp) <| le_iSup_of_le (by simp) (by simp)

section MinimalCover

lemma exists_set_encard_eq_coveringNumber (h : coveringNumber ε A ≠ ⊤) :
    ∃ C, C ⊆ A ∧ C.Finite ∧ IsCover ε A C ∧ C.encard = coveringNumber ε A := by
  simp only [coveringNumber, ne_eq, iInf_eq_top, encard_eq_top_iff, not_forall, not_infinite] at h
  obtain ⟨C', hC'_subset, hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // s ⊆ A ∧ IsCover ε A s } := ⟨C', hC'_subset, hC'_cover⟩
  let h := ENat.exists_eq_iInf (fun C : {s : Set X // s ⊆ A ∧ IsCover ε A s} ↦ (C : Set X).encard)
  obtain ⟨C, hC⟩ := h
  refine ⟨C, C.2.1, ?_, C.2.2, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C', ⟨hC'_subset, hC'_cover⟩, hC'_fin⟩
  · rw [hC]
    simp_rw [iInf_subtype, iInf_and]
    rfl

open Classical in
/-- A finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
It is defined as the empty set if no such finite cover exists. -/
noncomputable
def minimalCover (ε : ℝ≥0) (A : Set X) : Set X :=
  if h : coveringNumber ε A ≠ ⊤ then (exists_set_encard_eq_coveringNumber h).choose else ∅

lemma minimalCover_subset : minimalCover ε A ⊆ A := by grind [minimalCover]

lemma finite_minimalCover :
    (minimalCover ε A).Finite := by grind [minimalCover]

lemma isCover_minimalCover (h : coveringNumber ε A ≠ ⊤) :
    IsCover ε A (minimalCover ε A) := by grind [minimalCover]

lemma encard_minimalCover (h : coveringNumber ε A ≠ ⊤) :
    (minimalCover ε A).encard = coveringNumber ε A := by grind [minimalCover]

end MinimalCover

section MaximalSeparatedSet

lemma exists_set_encard_eq_packingNumber (h : packingNumber ε A ≠ ⊤) :
    ∃ C, C ⊆ A ∧ C.Finite ∧ IsSeparated ε C ∧ C.encard = packingNumber ε A := by
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · simp [hA, packingNumber]
  have : Nonempty { s : Set X // s ⊆ A ∧ IsSeparated ε s } := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨{a}, by simp [ha], by simp⟩⟩
  let h_exists := ENat.exists_eq_iSup_of_lt_top
    (f := fun C : { s : Set X // s ⊆ A ∧ IsSeparated ε s } ↦ (C : Set X).encard)
  simp_rw [packingNumber] at h ⊢
  simp_rw [iSup_subtype, iSup_and] at h_exists
  specialize h_exists h.lt_top
  obtain ⟨C, hC⟩ := h_exists
  refine ⟨C, C.2.1, ?_, C.2.2, ?_⟩
  · refine Set.encard_ne_top_iff.mp ?_
    rwa [hC]
  · rw [hC]

/-- A finite `ε`-separated subset of a set `A` with maximal cardinality.
It is defined as the empty set if no such finite subset exists. -/
noncomputable
def maximalSeparatedSet (ε : ℝ≥0) (A : Set X) : Set X :=
  if h : packingNumber ε A ≠ ⊤ then (exists_set_encard_eq_packingNumber h).choose else ∅

lemma maximalSeparatedSet_subset : maximalSeparatedSet ε A ⊆ A := by grind [maximalSeparatedSet]

lemma isSeparated_maximalSeparatedSet :
    IsSeparated ε (maximalSeparatedSet ε A : Set X) := by grind [maximalSeparatedSet]

lemma encard_maximalSeparatedSet (h : packingNumber ε A ≠ ⊤) :
    (maximalSeparatedSet ε A).encard = packingNumber ε A := by grind [maximalSeparatedSet]

lemma encard_le_of_isSeparated (h_subset : C ⊆ A)
    (h_sep : IsSeparated ε C) (h : packingNumber ε A ≠ ⊤) :
    C.encard ≤ (maximalSeparatedSet ε A).encard := by
  rw [encard_maximalSeparatedSet h]
  exact le_iSup_of_le C <| le_iSup_of_le h_subset <| le_iSup_of_le h_sep (by simp)

/-- The maximal separated set is a cover. -/
lemma isCover_maximalSeparatedSet (h : packingNumber ε A ≠ ⊤) :
    IsCover ε A (maximalSeparatedSet ε A) := by
  intro x hxA
  by_contra! h_dist
  let C := {x} ∪ maximalSeparatedSet ε A
  have hx_not_mem : x ∉ maximalSeparatedSet ε A := by simpa using h_dist x
  suffices C ⊆ A ∧ IsSeparated ε C by
    refine absurd (encard_le_of_isSeparated this.1 this.2 h) ?_
    simp [C, encard_insert_of_notMem hx_not_mem,
      ENat.lt_add_one_iff (encard_maximalSeparatedSet h ▸ h)]
  constructor
  · simp [C, hxA, maximalSeparatedSet_subset, Set.insert_subset]
  · exact isSeparated_insert_of_notMem hx_not_mem |>.mpr
      ⟨isSeparated_maximalSeparatedSet, by simpa using h_dist⟩

end MaximalSeparatedSet

section Comparisons

/-- The packing number of a set `A` for radius `2 * ε` is at most the external covering number
of `A` for radius `ε`. -/
theorem packingNumber_two_mul_le_externalCoveringNumber (ε : ℝ≥0) (A : Set X) :
    packingNumber (2 * ε) A ≤ externalCoveringNumber ε A := by
  simp only [packingNumber, ENNReal.coe_mul, ENNReal.coe_ofNat, externalCoveringNumber, le_iInf_iff,
    iSup_le_iff]
  intro C hC_cover D hD_subset hD_separated
  -- For each point in D, choose a point in C which is ε-close to it
  let f : D → C := fun x ↦
    ⟨(hC_cover (hD_subset x.2)).choose, (hC_cover (hD_subset x.2)).choose_spec.1⟩
  have hf' (x : D) : edist x.1 (f x) ≤ ε := (hC_cover (hD_subset x.2)).choose_spec.2
  -- `⊢ D.encard ≤ C.encard`
  -- It suffices to prove that `f` is injective
  simp only [← Set.toENat_cardinalMk]
  gcongr
  refine Cardinal.mk_le_of_injective (f := f) fun x y hxy ↦ Subtype.ext ?_
  apply Set.Pairwise.eq hD_separated x.2 y.2
  simp only [not_lt]
  calc
    edist (x : X) y ≤ edist (x : X) (f x) + edist (f x : X) y := edist_triangle ..
    _ ≤ 2 * ε := by
      rw [two_mul]
      gcongr
      · exact hf' x
      · simpa [edist_comm, hxy] using hf' y

theorem coveringNumber_le_packingNumber (ε : ℝ≥0) (A : Set X) :
    coveringNumber ε A ≤ packingNumber ε A := by
  by_cases! h_top : packingNumber ε A ≠ ⊤
  · rw [← encard_maximalSeparatedSet h_top]
    exact isCover_maximalSeparatedSet h_top |>.coveringNumber_le_encard maximalSeparatedSet_subset
  · simp [h_top]

theorem coveringNumber_two_mul_le_externalCoveringNumber (ε : ℝ≥0) (A : Set X) :
    coveringNumber (2 * ε) A ≤ externalCoveringNumber ε A := by
  rcases Set.eq_empty_or_nonempty A with rfl | h_nonempty
  · simp
  refine (coveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_mul_le_externalCoveringNumber ε A

lemma coveringNumber_subset_le (h : A ⊆ B) :
    coveringNumber ε A ≤ coveringNumber (ε / 2) B := calc
  coveringNumber ε A
  _ ≤ packingNumber ε A := coveringNumber_le_packingNumber ε A
  _ = packingNumber (2 * (ε / 2)) A := by ring_nf
  _ ≤ externalCoveringNumber (ε / 2) A :=
    packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
  _ ≤ externalCoveringNumber (ε / 2) B := externalCoveringNumber_mono_set h
  _ ≤ coveringNumber (ε / 2) B :=
    externalCoveringNumber_le_coveringNumber (ε / 2) B

end Comparisons

end Metric
