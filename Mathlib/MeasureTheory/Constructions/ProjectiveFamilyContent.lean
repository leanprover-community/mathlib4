/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.SetAlgebra

/-!
# Additive content built from a projective family of measures

Let `P` be a projective family of measures on a family of measurable spaces indexed by `ι`.
That is, for each finite set `I` of indices, `P I` is a measure on `Π j : I, α j`, and for `J ⊆ I`,
the projection from `Π i : I, α i` to `Π i : J, α i` maps `P I` to `P J`.

We build an additive content `projectiveFamilyContent` on the measurable cylinders, by setting
`projectiveFamilyContent s = P I S` for `s = cylinder I S`, where `I` is a finite set of indices
and `S` is a measurable set in `Π i : I, α i`.

This content will be used to define the projective limit of the family of measures `P`.
For a countable index set and a projective family given by a sequence of kernels,
the projective limit is given by the Ionescu-Tulcea theorem.
For an arbitrary index set but under topological conditions on the spaces, this is the result of
the Kolmogorov extension theorem.
(both results are not yet in Mathlib)

## Main definitions

* `projectiveFamilyContent`: additive content on the measurable cylinders, defined from a projective
  family of measures.

-/


open Finset

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)}
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)} {s t : Set (Π i, α i)} {I : Finset ι}
  {S : Set (Π i : I, α i)}

section MeasurableCylinders

lemma isSetAlgebra_measurableCylinders : IsSetAlgebra (measurableCylinders α) where
  empty_mem := empty_mem_measurableCylinders α
  compl_mem _ := compl_mem_measurableCylinders
  union_mem _ _ := union_mem_measurableCylinders

lemma isSetRing_measurableCylinders : IsSetRing (measurableCylinders α) :=
  isSetAlgebra_measurableCylinders.isSetRing

lemma isSetSemiring_measurableCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α) :=
  isSetRing_measurableCylinders.isSetSemiring

end MeasurableCylinders

section ProjectiveFamilyFun

open Classical in
/-- For `P` a family of measures, with `P J` a measure on `Π j : J, α j`, we define a function
`projectiveFamilyFun P s` by setting it to `P I S` if `s = cylinder I S` for a measurable `S` and
to 0 if `s` is not a measurable cylinder. -/
noncomputable def projectiveFamilyFun (P : ∀ J : Finset ι, Measure (Π j : J, α j))
    (s : Set (Π i, α i)) : ℝ≥0∞ :=
  if hs : s ∈ measurableCylinders α
    then P (measurableCylinders.finset hs) (measurableCylinders.set hs) else 0

lemma projectiveFamilyFun_congr (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    projectiveFamilyFun P s = P I S := by
  rw [projectiveFamilyFun, dif_pos hs]
  exact hP.congr_cylinder (measurableCylinders.measurableSet hs) hS
    ((measurableCylinders.eq_cylinder hs).symm.trans hs_eq)

lemma projectiveFamilyFun_empty (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyFun P ∅ = 0 := by
  rw [projectiveFamilyFun_congr hP (empty_mem_measurableCylinders α) (cylinder_empty ∅).symm
    MeasurableSet.empty, measure_empty]

lemma projectiveFamilyFun_union (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) (hst : Disjoint s t) :
    projectiveFamilyFun P (s ∪ t) = projectiveFamilyFun P s + projectiveFamilyFun P t := by
  obtain ⟨I, S, hS, hs_eq⟩ := (mem_measurableCylinders _).1 hs
  obtain ⟨J, T, hT, ht_eq⟩ := (mem_measurableCylinders _).1 ht
  classical
  let S' := restrict₂ (subset_union_left (s₂ := J)) ⁻¹' S
  let T' := restrict₂ (subset_union_right (s₁ := I)) ⁻¹' T
  have hS' : MeasurableSet S' := measurable_restrict₂ _ hS
  have hT' : MeasurableSet T' := measurable_restrict₂ _ hT
  have h_eq1 : s = cylinder (I ∪ J) S' := by rw [hs_eq]; exact cylinder_eq_cylinder_union I S J
  have h_eq2 : t = cylinder (I ∪ J) T' := by rw [ht_eq]; exact cylinder_eq_cylinder_union J T I
  have h_eq3 : s ∪ t = cylinder (I ∪ J) (S' ∪ T') := by
    rw [hs_eq, ht_eq]; exact union_cylinder _ _ _ _
  rw [projectiveFamilyFun_congr hP hs h_eq1 hS', projectiveFamilyFun_congr hP ht h_eq2 hT',
    projectiveFamilyFun_congr hP (union_mem_measurableCylinders hs ht) h_eq3 (hS'.union hT')]
  cases isEmpty_or_nonempty (Π i, α i) with
  | inl h => simp [hP.eq_zero_of_isEmpty]
  | inr h =>
    rw [measure_union _ hT']
    rwa [hs_eq, ht_eq, disjoint_cylinder_iff] at hst

end ProjectiveFamilyFun

section ProjectiveFamilyContent

/-- For `P` a projective family of measures, we define an additive content on the measurable
cylinders, by setting `projectiveFamilyContent s = P I S` for `s = cylinder I S`, where `I` is
a finite set of indices and `S` is a measurable set in `Π i : I, α i`. -/
noncomputable def projectiveFamilyContent (hP : IsProjectiveMeasureFamily P) :
    AddContent (measurableCylinders α) :=
  isSetRing_measurableCylinders.addContent_of_union (projectiveFamilyFun P)
    (projectiveFamilyFun_empty hP) (projectiveFamilyFun_union hP)

lemma projectiveFamilyContent_eq (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyContent hP s = projectiveFamilyFun P s := rfl

lemma projectiveFamilyContent_congr (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i))
    (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    projectiveFamilyContent hP s = P I S := by
  rw [projectiveFamilyContent_eq,
    projectiveFamilyFun_congr hP ((mem_measurableCylinders s).mpr ⟨I, S, hS, hs_eq⟩) hs_eq hS]

lemma projectiveFamilyContent_cylinder (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S) :
    projectiveFamilyContent hP (cylinder I S) = P I S := projectiveFamilyContent_congr _ _ rfl hS

lemma projectiveFamilyContent_mono (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) (hst : s ⊆ t) :
    projectiveFamilyContent hP s ≤ projectiveFamilyContent hP t :=
  addContent_mono isSetSemiring_measurableCylinders hs ht hst

lemma projectiveFamilyContent_iUnion_le (hP : IsProjectiveMeasureFamily P)
    {s : ℕ → Set (Π i : ι, α i)} (hs : ∀ n, s n ∈ measurableCylinders α) (n : ℕ) :
    projectiveFamilyContent hP (⋃ i ≤ n, s i)
      ≤ ∑ i ∈ range (n + 1), projectiveFamilyContent hP (s i) :=
  calc projectiveFamilyContent hP (⋃ i ≤ n, s i)
  _ = projectiveFamilyContent hP (⋃ i ∈ range (n + 1), s i) := by
    simp only [mem_range_succ_iff]
  _ ≤ ∑ i ∈ range (n + 1), projectiveFamilyContent hP (s i) :=
    addContent_biUnion_le isSetRing_measurableCylinders (fun i _ ↦ hs i)

lemma projectiveFamilyContent_ne_top [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyContent hP s ≠ ∞ := by
  rw [projectiveFamilyContent_eq hP, projectiveFamilyFun]
  split_ifs with hs <;> finiteness

lemma projectiveFamilyContent_diff (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) :
    projectiveFamilyContent hP s - projectiveFamilyContent hP t
      ≤ projectiveFamilyContent hP (s \ t) :=
  le_addContent_diff (projectiveFamilyContent hP) isSetRing_measurableCylinders hs ht

lemma projectiveFamilyContent_diff_of_subset [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) (hts : t ⊆ s) :
    projectiveFamilyContent hP (s \ t)
      = projectiveFamilyContent hP s - projectiveFamilyContent hP t :=
  addContent_diff_of_ne_top (projectiveFamilyContent hP) isSetRing_measurableCylinders
    (fun _ _ ↦ projectiveFamilyContent_ne_top hP) hs ht hts

end ProjectiveFamilyContent

end MeasureTheory
