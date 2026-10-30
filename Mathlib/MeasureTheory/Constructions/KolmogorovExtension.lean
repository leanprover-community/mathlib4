/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Measure.AddContent.CompactSystem
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Kolmogorov extension theorem

Given a projective family of finite measures `P J` on the finite products `Π j : J, α j`, we
construct its projective limit, a measure on `Π i, α i`, when the spaces `α i` are
second-countable and completely pseudo-metrizable (for example Polish spaces).

## Main definitions

* `projectiveLimit P hP`: the projective limit of a projective family of finite measures.

## Main statements

* `projectiveFamilyContent_iUnion_eq_tsum_of_innerRegular`: the content `projectiveFamilyContent hP`
  is σ-additive if the measures `P J` are inner regular with respect to compact closed sets.
* `isProjectiveLimit_projectiveLimit`: **Kolmogorov extension theorem**, `projectiveLimit P hP` is
  the projective limit of `P`.
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

section InnerRegular

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

/-- If the measures `P J` are inner regular with respect to compact closed sets, then the content
`projectiveFamilyContent hP` is inner regular with respect to cylinders with compact closed
bases. -/
lemma innerRegular_projectiveFamilyContent (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet)
    {s : Set (Π i, α i)} (hs : s ∈ measurableCylinders α) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K ∈ closedCompactCylinders α, K ⊆ s ∧ projectiveFamilyContent hP (s \ K) ≤ ε := by
  obtain ⟨J, A, hA, rfl⟩ := (mem_measurableCylinders s).mp hs
  obtain ⟨K, hKA, ⟨hK_compact, hK_closed⟩, hK⟩ := (hP_inner J).exists_subset_lt_add
    ⟨isCompact_empty, isClosed_empty⟩ hA (measure_ne_top _ _) hε.ne'
  refine ⟨cylinder J K, cylinder_mem_closedCompactCylinders _ _ hK_closed hK_compact,
    preimage_mono hKA, ?_⟩
  rw [sdiff_cylinder_same, projectiveFamilyContent_cylinder _ (hA.diff hK_closed.measurableSet)]
  exact (measure_sdiff_lt_of_lt_add hK_closed.nullMeasurableSet hKA (measure_ne_top _ _) hK).le

/-- If the measures `P J` are inner regular with respect to compact closed sets, then the content
`projectiveFamilyContent hP` is σ-additive. -/
theorem projectiveFamilyContent_iUnion_eq_tsum_of_innerRegular (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet)
    ⦃f : ℕ → Set (Π i, α i)⦄ (hf : ∀ i, f i ∈ measurableCylinders α)
    (hf_Union : (⋃ i, f i) ∈ measurableCylinders α)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    projectiveFamilyContent hP (⋃ i, f i) = ∑' i, projectiveFamilyContent hP (f i) :=
  addContent_iUnion_eq_sum_of_innerRegular isSetRing_measurableCylinders
    (projectiveFamilyContent hP) (fun _ _ ↦ projectiveFamilyContent_ne_top hP)
    (isCompactSystem_closedCompactCylinders α)
    (fun _ ↦ mem_measurableCylinders_of_mem_closedCompactCylinders)
    (fun _ ↦ innerRegular_projectiveFamilyContent hP hP_inner) hf hf_Union h_disj

/-- If the measures `P J` are inner regular with respect to compact closed sets, then the content
`projectiveFamilyContent hP` is σ-subadditive. -/
theorem isSigmaSubadditive_projectiveFamilyContent_of_innerRegular
    (hP : IsProjectiveMeasureFamily P)
    (hP_inner : ∀ J, (P J).InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet) :
    (projectiveFamilyContent hP).IsSigmaSubadditive :=
  isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders
    (projectiveFamilyContent_iUnion_eq_tsum_of_innerRegular hP hP_inner)

end InnerRegular

section CompletelyPseudoMetrizable

variable [∀ i, TopologicalSpace (α i)] [∀ i, SecondCountableTopology (α i)]
  [∀ i, TopologicalSpace.IsCompletelyPseudoMetrizableSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ I, IsFiniteMeasure (P I)]

/-- The content `projectiveFamilyContent hP` is σ-additive. -/
theorem projectiveFamilyContent_iUnion_eq_tsum (hP : IsProjectiveMeasureFamily P)
    ⦃f : ℕ → Set (Π i, α i)⦄
    (hf : ∀ i, f i ∈ measurableCylinders α) (hf_Union : (⋃ i, f i) ∈ measurableCylinders α)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    projectiveFamilyContent hP (⋃ i, f i) = ∑' i, projectiveFamilyContent hP (f i) :=
  projectiveFamilyContent_iUnion_eq_tsum_of_innerRegular hP
    (fun J ↦ innerRegular_isCompact_isClosed_measurableSet_of_finite (P J)) hf hf_Union h_disj

/-- The content `projectiveFamilyContent hP` is σ-subadditive. -/
theorem isSigmaSubadditive_projectiveFamilyContent (hP : IsProjectiveMeasureFamily P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive :=
  isSigmaSubadditive_projectiveFamilyContent_of_innerRegular hP
    fun J ↦ innerRegular_isCompact_isClosed_measurableSet_of_finite (P J)

/-- The projective limit of a projective family of finite measures on products of second-countable
completely pseudo-metrizable spaces (for example Polish spaces).
See `isProjectiveLimit_projectiveLimit`. -/
noncomputable def projectiveLimit (P : ∀ J : Finset ι, Measure (Π j : J, α j))
    [∀ i, IsFiniteMeasure (P i)] (hP : IsProjectiveMeasureFamily P) : Measure (Π i, α i) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.symm.le (isSigmaSubadditive_projectiveFamilyContent hP)

/-- **Kolmogorov extension theorem**: for any projective measure family `P`, there exists a measure
on `Π i, α i` which is the projective limit of `P`. That measure is given by
`projectiveLimit P hP`, where `hP : IsProjectiveMeasureFamily P`.
The projective limit is unique: see `IsProjectiveLimit.unique`. -/
theorem isProjectiveLimit_projectiveLimit (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit P hP) P := by
  intro J
  ext s hs
  rw [Measure.map_apply _ hs]
  swap; · exact J.measurable_restrict
  have h_mem : J.restrict ⁻¹' s ∈ measurableCylinders α :=
    (mem_measurableCylinders _).mpr ⟨J, s, hs, rfl⟩
  rw [projectiveLimit, AddContent.measure_eq _ _ _ _ h_mem,
    projectiveFamilyContent_congr hP (_ ⁻¹' _) rfl hs]
  exact generateFrom_measurableCylinders.symm

instance isFiniteMeasure_projectiveLimit (hP : IsProjectiveMeasureFamily P) :
    IsFiniteMeasure (projectiveLimit P hP) :=
  IsProjectiveLimit.isFiniteMeasure (isProjectiveLimit_projectiveLimit hP)

instance isProbabilityMeasure_projectiveLimit
    {P : ∀ J : Finset ι, Measure (Π j : J, α j)} [∀ i, IsProbabilityMeasure (P i)]
    (hP : IsProjectiveMeasureFamily P) : IsProbabilityMeasure (projectiveLimit P hP) := by
  constructor
  rw [← cylinder_univ (∅ : Finset ι),
    (isProjectiveLimit_projectiveLimit hP).measure_cylinder _ MeasurableSet.univ]
  exact measure_univ

end CompletelyPseudoMetrizable

end MeasureTheory
