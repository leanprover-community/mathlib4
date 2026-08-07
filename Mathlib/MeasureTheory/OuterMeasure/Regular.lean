/-
Copyright (c) 2026 UW Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ignacio Tejeda, Theodore Meek, Annie Cao, Nathan Pao
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regular outer measures

This file defines several regularity conditions for outer measures on topological spaces.

## Main definitions

* `MeasureTheory.OuterMeasure.FiniteOnCompact`: an outer measure is finite on compact sets.
* `MeasureTheory.OuterMeasure.Borel`: all Borel sets are Carathéodory-measurable.
* `MeasureTheory.OuterMeasure.Regular`: every set is contained in a Carathéodory-measurable set
  with the same outer measure.
* `MeasureTheory.OuterMeasure.BorelRegular`: every set is contained in a Borel set with the same
  outer measure.
* `MeasureTheory.OuterMeasure.Radon`: a Borel regular outer measure whose associated Borel measure
  is regular.
* `MeasureTheory.OuterMeasure.support`: the support of an outer measure on a topological space.

## References

* V. I. Bogachev, *Measure Theory I*, Proposition 1.11.7
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ENNReal Topology Pointwise

namespace MeasureTheory
namespace OuterMeasure

variable {X : Type*}

/-- An outer measure on a topological space is finite on compact sets if it assigns finite measure
to every compact set. -/
class FiniteOnCompact [TopologicalSpace X]
    (μ : OuterMeasure X) : Prop where
  measure_lt_top_of_isCompact :
    ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞

/-- An outer measure `μ` on a topological space equipped with the Borel σ-algebra is Borel if all
Borel sets are Carathéodory-measurable for `μ`. -/
class Borel [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop where
  measurable_le_caratheodory : ‹MeasurableSpace X› ≤ μ.caratheodory


/-- An outer measure `μ` is regular if every set `E` is contained in a
Carathéodory-measurable set `F` with `μ E = μ F`. -/
class Regular (μ : OuterMeasure X) : Prop where
  exists_measurable_superset :
    ∀ E : Set X, ∃ F : Set X,
      μ.IsCaratheodory F ∧
      E ⊆ F ∧
      μ E = μ F

/-- An outer measure `μ` on a topological space equipped with the Borel σ-algebra is Borel regular
if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ E = μ F`. -/
class BorelRegular [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends Borel μ where
  exists_measurable_superset :
    ∀ E : Set X, ∃ F : Set X,
      MeasurableSet F ∧
      E ⊆ F ∧
      μ E = μ F

/-- Borel regular outer measures are regular. -/
instance BorelRegular.toRegular [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : OuterMeasure X) [BorelRegular μ] : Regular μ where
  exists_measurable_superset E := by
    obtain ⟨F, hF, hEF, hμF⟩ :=
      BorelRegular.exists_measurable_superset (μ := μ) E
    exact ⟨F, Borel.measurable_le_caratheodory (μ := μ) F hF, hEF, hμF⟩

/-- An outer measure `μ` on a topological space equipped with the Borel σ-algebra is Radon if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure via `toMeasure` satisfies `Measure.Regular`. -/
class Radon [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends BorelRegular μ where
  regular_toMeasure :
    (μ.toMeasure (Borel.measurable_le_caratheodory (μ := μ))).Regular

/-- The support of an outer measure `μ` on a topological space is the set of points `x` such that
every neighborhood of `x` has positive `μ`-measure. -/
def support [TopologicalSpace X] (μ : OuterMeasure X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, 0 < μ U}


/-!
## Basic facts about regular outer measures
-/

/-- The nontrivial direction of Bogachev's Proposition 1.11.7. -/
lemma isCaratheodory_of_measure_add_compl_eq_univ
    (μ : OuterMeasure X) [Regular μ]
    (hμ : μ univ < ∞) {A : Set X} (hA : μ A + μ Aᶜ = μ univ) :
    μ.IsCaratheodory A := by
  rcases Regular.exists_measurable_superset (μ := μ) A with ⟨F, hF, hAF, hμAF⟩
  have hfin (E : Set X) : μ E ≠ ∞ := ne_of_lt <| (measure_mono (subset_univ E)).trans_lt hμ
  have hAc : μ Aᶜ = μ Fᶜ := (ENNReal.add_right_inj (hfin F)).mp <| by
    simpa [hμAF, Set.sdiff_eq] using hA.trans (hF univ)
  have hFA : μ (F \ A) = 0 := (ENNReal.add_left_inj (hfin Fᶜ)).mp <| by
    simpa [hAc, Set.sdiff_eq, Set.compl_inter, Set.inter_assoc, Set.inter_comm,
      Set.inter_left_comm, inter_eq_self_of_subset_right (compl_subset_compl.mpr hAF)]
      using (hF Aᶜ).symm
  convert μ.isCaratheodory_sdiff hF (μ.isCaratheodory_of_measure_eq_zero hFA) using 1; aesop

/-- If `μ` is a finite regular outer measure, then a set is Carathéodory-measurable if and only if
the measure of the set plus the measure of its complement is the measure of the whole space.

This is Bogachev's Proposition 1.11.7. -/
lemma isCaratheodory_iff_measure_add_compl_eq_univ
    (μ : OuterMeasure X) [Regular μ]
    (hμ : μ univ < ∞) (A : Set X) :
    μ.IsCaratheodory A ↔ μ A + μ Aᶜ = μ univ := by
  exact ⟨fun hA => hA.measure_add_compl, isCaratheodory_of_measure_add_compl_eq_univ μ hμ⟩

end OuterMeasure
end MeasureTheory
