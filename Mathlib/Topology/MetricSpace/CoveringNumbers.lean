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

## Main statements

* `externalCoveringNumber_le_coveringNumber`: the external covering number is less than or equal to
  the covering number.
* `packingNumber_two_mul_le_externalCoveringNumber`: the packing number with radius `2 * ε` is
  less than or equal to the external covering number for `ε`.

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

lemma coveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ ε) :
    coveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ ≤ ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ ≤ 1 := by simp
  · simpa [Order.one_le_iff_pos]

lemma externalCoveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty)
    (hA : EMetric.diam A ≤ ε) :
    externalCoveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · simpa [Order.one_le_iff_pos]

lemma externalCoveringNumber_le_one_of_ediam_le (hA : EMetric.diam A ≤ ε) :
    externalCoveringNumber ε A ≤ 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_ediam_le h_nonempty hA).le

lemma coveringNumber_le_one_of_ediam_le (hA : EMetric.diam A ≤ ε) : coveringNumber ε A ≤ 1 := by
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

end Metric
