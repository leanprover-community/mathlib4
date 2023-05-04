/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measure.measure_space
! leanprover-community/mathlib commit 88fcb83fe7996142dfcfe7368d31304a9adc874a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.p3

/-!
# Measure spaces

The definition of a measure and a measure space are in `measure_theory.measure_space_def`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `measure_space_def`, and to
be available in `measure_space` (through `measurable_space`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

We introduce the following typeclasses for measures:

* `is_probability_measure μ`: `μ univ = 1`;
* `is_finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `is_locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/


noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace

open TopologicalSpace (SecondCountableTopology)

open Classical Topology BigOperators Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type _}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]

variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

section Inf

variable {m : Set (Measure α)}

theorem infₛ_caratheodory (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet[(infₛ (toOuterMeasure '' m)).caratheodory] s := by
  rw [OuterMeasure.infₛ_eq_boundedBy_infₛGen]
  refine' OuterMeasure.boundedBy_caratheodory fun t => _
  simp only [OuterMeasure.infₛGen, le_infᵢ_iff, ball_image_iff, coe_toOuterMeasure,
    measure_eq_infᵢ t]
  intro μ hμ u htu _hu
  have hm : ∀ {s t}, s ⊆ t → OuterMeasure.infₛGen (toOuterMeasure '' m) s ≤ μ t := by
    intro s t hst
    rw [OuterMeasure.infₛGen_def]
    refine' infᵢ_le_of_le μ.toOuterMeasure (infᵢ_le_of_le (mem_image_of_mem _ hμ) _)
    rw [toOuterMeasure_apply]
    refine' measure_mono hst
  rw [← measure_inter_add_diff u hs]
  refine' add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| diff_subset_diff_left htu)
#align measure_theory.measure.Inf_caratheodory MeasureTheory.Measure.infₛ_caratheodory

instance [MeasurableSpace α] : InfSet (Measure α) :=
  ⟨fun m => (infₛ (toOuterMeasure '' m)).toMeasure <| infₛ_caratheodory⟩

theorem infₛ_apply (hs : MeasurableSet s) : infₛ m s = infₛ (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.Inf_apply MeasureTheory.Measure.infₛ_apply

theorem measure_infₛ_le (h : μ ∈ m) : infₛ m ≤ μ :=
  have : infₛ (toOuterMeasure '' m) ≤ μ.toOuterMeasure := infₛ_le (mem_image_of_mem _ h)
  fun s hs => by rw [infₛ_apply hs, ← toOuterMeasure_apply]; exact this s
-- Porting note: private
--#align measure_theory.measure.measure_Inf_le MeasureTheory.Measure.measure_infₛ_le

theorem measure_le_infₛ (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ infₛ m :=
  have : μ.toOuterMeasure ≤ infₛ (toOuterMeasure '' m) :=
    le_infₛ <| ball_image_of_ball fun μ hμ => toOuterMeasure_le.2 <| h _ hμ
  fun s hs => by rw [infₛ_apply hs, ← toOuterMeasure_apply]; exact this s
-- Porting note: private
--#align measure_theory.measure.measure_le_Inf MeasureTheory.Measure.measure_le_infₛ

instance [MeasurableSpace α] : CompleteSemilatticeInf (Measure α) :=
  { (by infer_instance : PartialOrder (Measure α)),
    (by infer_instance :
      InfSet (Measure α)) with
    infₛ_le := fun _s _a => measure_infₛ_le
    le_infₛ := fun _s _a => measure_le_infₛ }

instance [MeasurableSpace α] : CompleteLattice (Measure α) :=
  {/- Adding an explicit `top` makes `leanchecker` fail, see lean#364, disable for now

        top := (⊤ : outer_measure α).to_measure (by rw [outer_measure.top_caratheodory]; exact le_top),
        le_top := λ a s hs,
          by cases s.eq_empty_or_nonempty with h  h;
            simp [h, to_measure_apply ⊤ _ hs, outer_measure.top_apply],
      -/
      completeLatticeOfCompleteSemilatticeInf
      (Measure α) with
    bot := 0
    bot_le := fun _a _s _hs => bot_le }

end Inf
