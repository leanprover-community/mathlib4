/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Lebesgue

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

open scoped ENNReal NNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {C : ℝ≥0} {g : α → ℝ≥0∞}

/-! We prove that the condition in the definition of `sigmaFiniteSetWRT` is true for finite
measures. Since every s-finite measure is absolutely continuous with respect to a finite measure,
the condition will then also be true for s-finite measures. -/

/-- Let `p : Set α → Prop` be a predicate on sets and let `C` be the supremum of `μ s` over
all measurable sets `s` with property `p s`. `C` is finite since `μ` is a finite measure.
Then there exists a measurable set `t` with `p t` such that `μ t ≥ C - 1/n`. -/
lemma exists_fun_lintegral_ge (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C)
    (n : ℕ) :
    ∃ f, Measurable f ∧ p f
      ∧ (⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ) - 1/n ≤ ∫⁻ x, f x ∂μ := by
  by_cases hC_lt : 1/n < ⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ
  · have h_lt_top : ⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ < ∞ := by
      refine (?_ : ⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C).trans_lt
        ENNReal.coe_lt_top
      refine iSup_le (fun g ↦ ?_)
      exact iSup_le (fun hg ↦ iSup_le (fun hgp ↦ hC _ hg hgp))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne (ne_zero_of_lt hC_lt) (by simp) :
          (⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ) - 1/n
        < ⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ)
    have ht_meas : Measurable t := by
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
  · refine ⟨0, measurable_const, hp_zero, ?_⟩
    rw [tsub_eq_zero_of_le (not_lt.mp hC_lt)]
    exact zero_le'

/-- A measurable set such that `p (μ.funGE μ n)` and for `C` the supremum of `μ s` over
all measurable sets `s` with `p s`, `μ (μ.funGE μ n) ≥ C - 1/n`. -/
noncomputable
def Measure.funGE (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C)
    (n : ℕ) :
    α → ℝ≥0∞ :=
  (exists_fun_lintegral_ge μ p hp_zero hC n).choose

lemma measurable_funGE (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) (n : ℕ) :
    Measurable (μ.funGE p hp_zero hC n) :=
  (exists_fun_lintegral_ge μ p hp_zero hC n).choose_spec.1

lemma prop_funGE (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) (n : ℕ) :
    p (μ.funGE p hp_zero hC n) :=
  (exists_fun_lintegral_ge μ p hp_zero hC n).choose_spec.2.1

lemma lintegral_funGE_le (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) (n : ℕ) :
    ∫⁻ x, μ.funGE p hp_zero hC n x ∂μ ≤ ⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ := by
  refine (le_iSup (f := fun s ↦ _) (prop_funGE μ p hp_zero hC n)).trans ?_
  exact le_iSup₂ (f := fun g _ ↦ ⨆ (_ : p g), ∫⁻ x, g x ∂μ) (μ.funGE p hp_zero hC n)
    (measurable_funGE p hp_zero hC n)

lemma lintegral_funGE_ge (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) (n : ℕ) :
    (⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ) - 1/n ≤ ∫⁻ x, μ.funGE p hp_zero hC n x ∂μ :=
  (exists_fun_lintegral_ge μ p hp_zero hC n).choose_spec.2.2

lemma tendsto_lintegral_funGE (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) :
    Tendsto (fun n ↦ ∫⁻ x, μ.funGE p hp_zero hC n x ∂μ) atTop
      (𝓝 (⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (lintegral_funGE_ge μ p hp_zero hC) (lintegral_funGE_le μ p hp_zero hC)
  nth_rewrite 2 [← tsub_zero (⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

/-- A measurable set such that `p (μ.maximalFun p hp_empty)` and the measure
`μ (μ.maximalFun p hp_empty)` is maximal among such sets. -/
noncomputable
def Measure.maximalFun (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) :
    α → ℝ≥0∞ :=
  fun a ↦ ⨆ n, μ.funGE p hp_zero hC n a

lemma measurable_maximalFun (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C) :
    Measurable (μ.maximalFun p hp_zero hC) :=
  Measurable.iSup (measurable_funGE p hp_zero hC)

lemma prop_maximalFun (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C)
    (hp_iUnion : ∀ (g : ℕ → α → ℝ≥0∞) (_ : ∀ n, Measurable (g n)) (_ : ∀ n, p (g n)),
      p (fun a ↦ ⨆ n, g n a)) :
    p (μ.maximalFun p hp_zero hC) :=
  hp_iUnion _ (measurable_funGE p hp_zero hC) (prop_funGE μ p hp_zero hC)

/-- `μ.maximalFun p hp_empty` has maximal `μ`-measure among all measurable sets `s` with `p s`. -/
lemma lintegral_maximalFun (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
    (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C)
    (hp_iUnion : ∀ (g : ℕ → α → ℝ≥0∞) (_ : ∀ n, Measurable (g n)) (_ : ∀ n, p (g n)),
      p (fun a ↦ ⨆ n, g n a)) :
    ∫⁻ x, μ.maximalFun p hp_zero hC x ∂μ = ⨆ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (prop_maximalFun μ p hp_zero hC hp_iUnion)).trans ?_
    exact le_iSup₂ (f := fun g _ ↦ ⨆ (_ : p g), ∫⁻ x, g x ∂μ) (μ.maximalFun p hp_zero hC)
      (measurable_maximalFun p hp_zero hC)
  · refine le_of_tendsto' (tendsto_lintegral_funGE μ p hp_zero hC) fun n ↦ ?_
    refine lintegral_mono fun a ↦ ?_
    exact le_iSup (fun n ↦ μ.funGE p hp_zero hC n a) n

-- lemma not_prop_of_subset_compl_maximalFun (μ : Measure α) (p : (α → ℝ≥0∞) → Prop) (hp_zero : p 0)
--     (hC : ∀ (g) (_ : Measurable g) (_ : p g), ∫⁻ x, g x ∂μ ≤ C)
--     (hp_iUnion : ∀ (g : ℕ → α → ℝ≥0∞) (_ : ∀ n, Measurable (g n)) (_ : ∀ n, p (g n)),
--       p (fun a ↦ ⨆ n, g n a))
--     (hg : Measurable g) (hs_subset : s ⊆ (μ.maximalFun p hp_zero hC)ᶜ) (hμs : μ s ≠ 0) :
--     ¬ p s := by
--   intro hsp
--   have h_lt : μ (μ.maximalFun p hp_zero hC) < μ (μ.maximalFun p hp_zero hC ∪ s) := by
--     rw [measure_union _ hs]
--     · exact ENNReal.lt_add_right (measure_ne_top _ _) hμs
--     · exact disjoint_compl_right.mono_right hs_subset
--   have h_le : μ (μ.maximalFun p hp_zero hC ∪ s) ≤ μ (μ.maximalFun p hp_zero hC) := by
--     conv_rhs => rw [lintegral_maximalFun _ _ hp_zero hC hp_iUnion]
--     refine (le_iSup
--       (f := fun (_ : p (μ.maximalFun p hp_zero hC ∪ s)) ↦ _) ?_).trans ?_
--     · let t : ℕ → Set α := fun n ↦ if n = 0 then (μ.maximalFun p hp_zero hC) else s
--       have : μ.maximalFun p hp_zero hC ∪ s = ⋃ n, t n := by
--         simp only [t, Set.iUnion_ite, Set.iUnion_iUnion_eq_left]
--         congr with x
--         simp only [Set.mem_iUnion, exists_prop, exists_and_right, iff_and_self]
--         exact fun _ ↦ ⟨1, by simp⟩
--       rw [this]
--       refine hp_iUnion t (fun n ↦ ?_) (fun n ↦ ?_)
--       · cases n with
--         | zero =>
--           simp only [↓reduceIte, t]
--           exact measurableSet_maximalFun p hp_empty
--         | succ n =>
--             simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, t]
--             exact hs
--       · cases n with
--         | zero =>
--           simp only [↓reduceIte, t]
--           exact prop_maximalFun μ p hp_empty hp_iUnion
--         | succ n =>
--             simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, t]
--             exact hsp
--     · exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : p _), μ s)
--         (μ.maximalFun p hp_zero hC ∪ s) ((measurableSet_maximalFun p hp_zero hC).union hs)
--   exact h_lt.not_le h_le

end MeasureTheory
