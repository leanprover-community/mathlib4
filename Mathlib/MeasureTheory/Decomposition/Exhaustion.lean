/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Typeclasses

/-!
# Method of exhaustion

If `μ, μ` are two measures with `μ` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `μ t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT μ` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT μ)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT μ)ᶜ`, either `μ t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `μ` is not s-finite), we define
  `μ.sigmaFiniteSetWRT μ = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `μ`, for all sets `s`
  in `(sigmaFiniteSetWRT μ μ)ᶜ`, if `μ s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ μ)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ μ` and `μ` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT μ)ᶜ = ∞ • μ.restrict (μ.sigmaFiniteSetWRT μ)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}

/-! We prove that the condition in the definition of `sigmaFiniteSetWRT` is true for finite
measures. Since every s-finite measure is absolutely continuous with respect to a finite measure,
the condition will then also be true for s-finite measures. -/

/-- Let `p : Set α → Prop` be a predicate on sets and let `C` be the supremum of `μ s` over
all measurable sets `s` with property `p s`. `C` is finite since `μ` is a finite measure.
Then there exists a measurable set `t` with `p t` such that `μ t ≥ C - 1/n`. -/
lemma exists_set_measure_ge (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅) (n : ℕ) :
    ∃ t, MeasurableSet t ∧ p t
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s) - 1/n ≤ μ t := by
  by_cases hC_lt : 1/n < ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s ≤ μ Set.univ).trans_lt
        (measure_lt_top _ _)
      refine iSup_le (fun s ↦ ?_)
      exact iSup_le (fun _ ↦ iSup_le (fun _ ↦ measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne (ne_zero_of_lt hC_lt) (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s) - 1/n
        < ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s)
    have ht_meas : MeasurableSet t := by
      by_contra h_not_mem
      simp only [h_not_mem] at ht
      simp at ht
    have ht_mem : p t := by
      by_contra h_not_mem
      simp only [h_not_mem] at ht
      simp at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · refine ⟨∅, MeasurableSet.empty, hp_empty, ?_⟩
    rw [tsub_eq_zero_of_le (not_lt.mp hC_lt)]
    exact zero_le'

/-- A measurable set such that `p (μ.pSetGE μ n)` and for `C` the supremum of `μ s` over
all measurable sets `s` with `p s`, `μ (μ.pSetGE μ n) ≥ C - 1/n`. -/
def Measure.pSetGE (μ : Measure α) [IsFiniteMeasure μ] (p : Set α → Prop) (hp_empty : p ∅)
    (n : ℕ) : Set α :=
  (exists_set_measure_ge μ p hp_empty n).choose

lemma measurableSet_pSetGE (p : Set α → Prop) (hp_empty : p ∅) (n : ℕ) :
    MeasurableSet (μ.pSetGE p hp_empty n) :=
  (exists_set_measure_ge μ p hp_empty n).choose_spec.1

lemma prop_pSetGE (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅) (n : ℕ) :
    p (μ.pSetGE p hp_empty n) :=
  (exists_set_measure_ge μ p hp_empty n).choose_spec.2.1

lemma measure_pSetGE_le (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅) (n : ℕ) :
    μ (μ.pSetGE p hp_empty n) ≤ ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s := by
  refine (le_iSup (f := fun s ↦ _) (prop_pSetGE μ p hp_empty n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p s), μ s) (μ.pSetGE p hp_empty n)
    (measurableSet_pSetGE p hp_empty n)

lemma measure_pSetGE_ge (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅) (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s) - 1/n ≤ μ (μ.pSetGE p hp_empty n) :=
  (exists_set_measure_ge μ p hp_empty n).choose_spec.2.2

lemma tendsto_measure_pSetGE (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅) :
    Tendsto (fun n ↦ μ (μ.pSetGE p hp_empty n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_pSetGE_ge μ p hp_empty) (measure_pSetGE_le μ p hp_empty)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

/-- A measurable set such that `p (μ.maximalSet p hp_empty)` and the measure
`μ (μ.maximalSet p hp_empty)` is maximal among such sets. -/
def Measure.maximalSet (μ : Measure α) [IsFiniteMeasure μ] (p : Set α → Prop) (hp_empty : p ∅) :
    Set α :=
  ⋃ n, μ.pSetGE p hp_empty n

lemma measurableSet_maximalSet (p : Set α → Prop) (hp_empty : p ∅) :
    MeasurableSet (μ.maximalSet p hp_empty) :=
  MeasurableSet.iUnion (measurableSet_pSetGE p hp_empty)

lemma prop_maximalSet (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅)
    (hp_iUnion : ∀ (t : ℕ → Set α) (_ : ∀ n, MeasurableSet (t n)) (_ : ∀ n, p (t n)),
      p (⋃ n, t n)) :
    p (μ.maximalSet p hp_empty) :=
  hp_iUnion _ (measurableSet_pSetGE p hp_empty) (prop_pSetGE μ p hp_empty)

/-- `μ.maximalSet p hp_empty` has maximal `μ`-measure among all measurable sets `s` with `p s`. -/
lemma measure_maximalSet (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅)
    (hp_iUnion : ∀ (t : ℕ → Set α) (_ : ∀ n, MeasurableSet (t n)) (_ : ∀ n, p (t n)),
      p (⋃ n, t n)) :
    μ (μ.maximalSet p hp_empty) = ⨆ (s) (_ : MeasurableSet s) (_ : p s), μ s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (prop_maximalSet μ p hp_empty hp_iUnion)).trans ?_
    exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p s), μ s) (μ.maximalSet p hp_empty)
      (measurableSet_maximalSet p hp_empty)
  · exact le_of_tendsto' (tendsto_measure_pSetGE μ p hp_empty)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

lemma not_prop_of_subset_compl_maximalSet (μ : Measure α) [IsFiniteMeasure μ]
    (p : Set α → Prop) (hp_empty : p ∅)
    (hp_iUnion : ∀ (t : ℕ → Set α) (_ : ∀ n, MeasurableSet (t n)) (_ : ∀ n, p (t n)),
      p (⋃ n, t n))
    (hs : MeasurableSet s) (hs_subset : s ⊆ (μ.maximalSet p hp_empty)ᶜ) (hμs : μ s ≠ 0) :
    ¬ p s := by
  intro hsp
  have h_lt : μ (μ.maximalSet p hp_empty) < μ (μ.maximalSet p hp_empty ∪ s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right (measure_ne_top _ _) hμs
    · exact disjoint_compl_right.mono_right hs_subset
  have h_le : μ (μ.maximalSet p hp_empty ∪ s) ≤ μ (μ.maximalSet p hp_empty) := by
    conv_rhs => rw [measure_maximalSet _ _ hp_empty hp_iUnion]
    refine (le_iSup
      (f := fun (_ : p (μ.maximalSet p hp_empty ∪ s)) ↦ _) ?_).trans ?_
    · let t : ℕ → Set α := fun n ↦ if n = 0 then (μ.maximalSet p hp_empty) else s
      have : μ.maximalSet p hp_empty ∪ s = ⋃ n, t n := by
        simp only [t, Set.iUnion_ite, Set.iUnion_iUnion_eq_left]
        congr with x
        simp only [Set.mem_iUnion, exists_prop, exists_and_right, iff_and_self]
        exact fun _ ↦ ⟨1, by simp⟩
      rw [this]
      refine hp_iUnion t (fun n ↦ ?_) (fun n ↦ ?_)
      · cases n with
        | zero =>
          simp only [↓reduceIte, t]
          exact measurableSet_maximalSet p hp_empty
        | succ n =>
            simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, t]
            exact hs
      · cases n with
        | zero =>
          simp only [↓reduceIte, t]
          exact prop_maximalSet μ p hp_empty hp_iUnion
        | succ n =>
            simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, t]
            exact hsp
    · exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p _), μ s)
        (μ.maximalSet p hp_empty ∪ s) ((measurableSet_maximalSet p hp_empty).union hs)
  exact h_lt.not_le h_le

end MeasureTheory
