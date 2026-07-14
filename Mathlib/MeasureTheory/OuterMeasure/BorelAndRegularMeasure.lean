import Mathlib.MeasureTheory.Measure.Regular

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## This file contains notions of regularity for outer measures
-/

/- **Locally finite** outer measure: an outer measure on a topological space is
locally finite if it assigns finite measure to every compact set. -/
class IsFiniteOnCompactOuterMeasure {X : Type*} [TopologicalSpace X]
    (μ : OuterMeasure X) : Prop where
  measure_lt_top_of_isCompact :
    ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞

/- **Borel** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Borel outer measure if all Borel sets are measurable for `μ`. -/
class BorelOuterMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop where
  measurable_le_caratheodory : ‹MeasurableSpace X› ≤ μ.caratheodory


/- **TODO (Theo): regular** outer measure: an outer measure `μ` on a space `X` is regular if
for every set `E`, there exists a `μ`-measurable set `F ⊇ E` with `μ E = μ F`. -/
class RegularOuterMeasure {X : Type*}
    (μ : OuterMeasure X) : Prop where
  exists_measurable_superset :
    ∀ E : Set X, ∃ F : Set X,
      μ.IsCaratheodory F ∧
      E ⊆ F ∧
      μ E = μ F

/-- **Borel regular** outer measure: an outer measure `μ` on a topological space `X`
equipped with the Borel σ-algebra is Borel regular if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ E = μ F`. -/
class IsBorelRegular {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends BorelOuterMeasure μ where
  exists_measurable_superset :
    ∀ E : Set X, ∃ F : Set X,
      MeasurableSet F ∧
      E ⊆ F ∧
      μ E = μ F

/- **TODO:** describe what this instance is -/
instance IsBorelRegular.toRegularOuterMeasure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : OuterMeasure X) [IsBorelRegular μ] :
    RegularOuterMeasure μ where
  exists_measurable_superset E := by
    obtain ⟨F, hF, hEF, hμF⟩ :=
      IsBorelRegular.exists_measurable_superset (μ := μ) E
    exact ⟨F, BorelOuterMeasure.measurable_le_caratheodory (μ := μ) F hF, hEF, hμF⟩

/-- **Radon** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Radon outer measure if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure via `toMeasure` satisfies `Measure.Regular`. -/
class IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends IsBorelRegular μ where
  regular_toMeasure :
    (μ.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))).Regular

/-- **Support** of an outer measure: an outer measure `μ` on a topological space `X` has
support the set of points `x` such that every neighborhood of `x` has positive `μ`-measure.-/
def SupportOuterMeasure {X : Type*} [TopologicalSpace X]
    (μ : OuterMeasure X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, 0 < μ U}


/-!
## Basic facts about regular outer measures
-/

/- Lemma: If `μ` is a regular outer measure on a space `X` and
`A⊆X`, then `A` is `μ`-measurable if and only if `μ(A)+μ(X∖A)=μ(X)`.
Reference: Bogachev - Measure Theory I, Proposition 1.11.7-/

/- Preliminary lemma 1: sets with zero outer measure are Caratheodory measurable (I'm surprised
this is not in mathlib, we should double-check. If that is the case, this should probably go
in a different file) -/ 
lemma isCaratheodory_of_measure_eq_zero {X : Type*} {μ : OuterMeasure X} {A : Set X}
    (hA : μ A = 0) : μ.IsCaratheodory A := by
  rw [OuterMeasure.isCaratheodory_iff_le']; intro T
  simpa [measure_mono_null inter_subset_right hA] using
    (measure_mono (diff_subset : T \ A ⊆ T) : μ (T \ A) ≤ μ T)

/- Preliminary lemma 2: non-trivial direction of Bogachev's Proposition 1.11.7 -/
lemma isCaratheodory_of_measure_add_compl_eq_univ
    {X : Type*} (μ : OuterMeasure X) [RegularOuterMeasure μ]
    (hμ : μ univ < ∞) {A : Set X} (hA : μ A + μ Aᶜ = μ univ) :
    μ.IsCaratheodory A := by
  rcases RegularOuterMeasure.exists_measurable_superset (μ := μ) A with ⟨F, hF, hAF, hμAF⟩
  have hfin (E : Set X) : μ E ≠ ∞ := ne_of_lt <| (measure_mono (subset_univ E)).trans_lt hμ
  have hAc : μ Aᶜ = μ Fᶜ := (ENNReal.add_right_inj (hfin F)).mp <| by
    simpa [hμAF, Set.diff_eq] using hA.trans (hF univ)
  have hFA : μ (F \ A) = 0 := (ENNReal.add_left_inj (hfin Fᶜ)).mp <| by
    simpa [hAc, Set.diff_eq, Set.compl_inter, Set.inter_assoc, Set.inter_comm,
      Set.inter_left_comm, inter_eq_self_of_subset_right (compl_subset_compl.mpr hAF)]
      using (hF Aᶜ).symm
  convert μ.isCaratheodory_diff hF (isCaratheodory_of_measure_eq_zero hFA) using 1; aesop

/- Bogachev's Proposition 1.11.7 -/
lemma isCaratheodory_iff_measure_add_compl_eq_univ
    {X : Type*} (μ : OuterMeasure X) [RegularOuterMeasure μ]
    (hμ : μ univ < ∞) (A : Set X) :
    μ.IsCaratheodory A ↔ μ A + μ Aᶜ = μ univ := by
  refine ⟨fun hA => ?_, isCaratheodory_of_measure_add_compl_eq_univ μ hμ⟩
  simpa [Set.diff_eq] using (hA univ).symm
