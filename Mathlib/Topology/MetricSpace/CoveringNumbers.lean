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
lemma externalCoveringNumber_eq_zero :
    externalCoveringNumber ε A = 0 ↔ A = ∅ := by simp [externalCoveringNumber]

@[simp]
lemma externalCoveringNumber_pos (hA : A.Nonempty) :
    0 < externalCoveringNumber ε A := Ne.bot_lt (by simpa using hA.ne_empty)

@[simp]
lemma coveringNumber_eq_zero : coveringNumber ε A = 0 ↔ A = ∅ := by simp [coveringNumber]

@[simp]
lemma coveringNumber_pos (hA : A.Nonempty) :
    0 < coveringNumber ε A := Ne.bot_lt (by simpa using hA.ne_empty)

lemma externalCoveringNumber_le_coveringNumber (ε : ℝ≥0) (A : Set X) :
    externalCoveringNumber ε A ≤ coveringNumber ε A := by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover ↦ iInf₂_le C hC_cover

lemma IsCover.externalCoveringNumber_le_encard (hC : IsCover ε A C) :
    externalCoveringNumber ε A ≤ C.encard := iInf₂_le C hC

lemma IsCover.coveringNumber_le_encard (h_subset : C ⊆ A) (hC : IsCover ε A C) :
    coveringNumber ε A ≤ C.encard := (iInf₂_le C h_subset).trans (iInf_le _ hC)

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

lemma coveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : EMetric.diam A ≤ ε) :
    coveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ ≤ ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ ≤ 1 := by simp
  · rw [Order.one_le_iff_pos]
    exact coveringNumber_pos h_nonempty

lemma externalCoveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty)
    (hA : EMetric.diam A ≤ ε) :
    externalCoveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · rw [Order.one_le_iff_pos]
    exact externalCoveringNumber_pos h_nonempty

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
