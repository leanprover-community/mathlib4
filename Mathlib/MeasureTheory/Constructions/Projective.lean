/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Projective measure families

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Set

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}

def IsProjective [Preorder ι] (P : ∀ j : ι, α j) (π : ∀ {i j : ι}, j ≤ i → α i → α j) : Prop :=
  ∀ (i j) (hji : j ≤ i), P j = π hji (P i)

/-- A family of measures indexed by finite sets of `ι` is projective if, for finite sets `J ⊆ I`,
the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`. -/
def IsProjectiveMeasureFamily [∀ i, MeasurableSpace (α i)]
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  IsProjective P
    (fun I _ hJI μ => μ.map fun x : ∀ i : I, α i => fun j => x ⟨j, hJI j.2⟩ :
      ∀ (I J : Finset ι) (_ : J ⊆ I), Measure (∀ i : I, α i) → Measure (∀ j : J, α j))

/-- A measure `μ` is the projective limit of a family of measures indexed by finite sets of `ι` if
for all `I : Finset ι`, the projection from `∀ i, α i` to `∀ i : I, α i` maps `μ` to `P I`. -/
def IsProjectiveLimit [∀ i, MeasurableSpace (α i)] (μ : Measure (∀ i, α i))
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ I : Finset ι, (μ.map fun x : ∀ i, α i => fun i : I => x i) = P I

variable [∀ i, MeasurableSpace (α i)] {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

namespace IsProjectiveMeasureFamily

/-- Auxiliary lemma for `congr_cylinder`. -/
theorem congr_cylinder_aux [h_nonempty : Nonempty (∀ i, α i)]
    (hP : IsProjectiveMeasureFamily P) {I J : Finset ι} {S : Set (∀ i : I, α i)}
    {T : Set (∀ i : J, α i)} (hT : MeasurableSet T) (h_eq : cylinder I S = cylinder J T)
    (hJI : J ⊆ I) :
    P I S = P J T := by
  have : S = (fun f : ∀ i : I, α i => fun j : J => f ⟨j, hJI j.prop⟩) ⁻¹' T :=
    eq_of_cylinder_eq_of_subset h_eq hJI
  rw [hP I J hJI, Measure.map_apply _ hT, this]
  exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem congr_cylinder [h_nonempty : Nonempty (∀ i, α i)]
    (hP : IsProjectiveMeasureFamily P) {I J : Finset ι} {S : Set (∀ i : I, α i)}
    {T : Set (∀ i : J, α i)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) :
    P I S = P J T := by
  classical
  let U :=
    (fun f : ∀ i : (I ∪ J : Finset ι), α i
        => fun j : I => f ⟨j, Finset.mem_union_left J j.prop⟩) ⁻¹' S ∩
      (fun f => fun j : J => f ⟨j, Finset.mem_union_right I j.prop⟩) ⁻¹' T
  suffices : P (I ∪ J) U = P I S ∧ P (I ∪ J) U = P J T
  exact this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_aux hS h_eq_union.symm (Finset.subset_union_left _ _)
  · have h_eq_union : cylinder J T = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_aux hT h_eq_union.symm (Finset.subset_union_right _ _)

/-- Auxiliary lemma for `measure_univ_eq`. -/
theorem measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P)
    (I J : Finset ι) (hJI : J ⊆ I) :
    P I univ = P J univ := by
  classical
  have : (univ : Set (∀ i : I, α i)) =
      (fun x : ∀ i : I, α i => fun i : J => x ⟨i, hJI i.2⟩) ⁻¹' (univ : Set (∀ i : J, α i)) :=
    by rw [preimage_univ]
  rw [this, ← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem measure_univ_eq (hP : IsProjectiveMeasureFamily P) (I J : Finset ι) :
    P I univ = P J univ := by
  classical rw [← hP.measure_univ_eq_of_subset (I ∪ J) I (Finset.subset_union_left _ _), ←
    hP.measure_univ_eq_of_subset (I ∪ J) J (Finset.subset_union_right _ _)]

end IsProjectiveMeasureFamily

namespace IsProjectiveLimit

variable {μ ν : Measure (∀ i, α i)}

theorem measure_cylinder (h : IsProjectiveLimit μ P)
    (I : Finset ι) {s : Set (∀ i : I, α i)} (hs : MeasurableSet s) : μ (cylinder I s) = P I s := by
  rw [cylinder, ← Measure.map_apply _ hs, h I]
  exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)

theorem measure_univ_eq (hμ : IsProjectiveLimit μ P)
    (I : Finset ι) : μ univ = P I univ := by
  rw [← cylinder_univ I, hμ.measure_cylinder _ MeasurableSet.univ]

theorem measure_univ_unique [hι : Nonempty ι]
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ univ = ν univ := by
  rw [hμ.measure_univ_eq ({hι.some} : Finset ι), hν.measure_univ_eq ({hι.some} : Finset ι)]

theorem isFiniteMeasure [hι : Nonempty ι] [∀ i, IsFiniteMeasure (P i)]
    (hμ : IsProjectiveLimit μ P) :
    IsFiniteMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq ({hι.some} : Finset ι)]
  exact measure_lt_top _ _

theorem isProbabilityMeasure [hι : Nonempty ι] [∀ i, IsProbabilityMeasure (P i)]
    (hμ : IsProjectiveLimit μ P) :
    IsProbabilityMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq ({hι.some} : Finset ι)]
  exact measure_univ

/-- The projective limit is unique. -/
theorem unique [hι : Nonempty ι] [∀ i, IsFiniteMeasure (P i)]
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ = ν := by
  haveI : IsFiniteMeasure μ := hμ.isFiniteMeasure
  refine ext_of_generate_finite (measurableCylinders α) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs => ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [hμ.measure_cylinder _ hS, hν.measure_cylinder _ hS]

end IsProjectiveLimit

end MeasureTheory
