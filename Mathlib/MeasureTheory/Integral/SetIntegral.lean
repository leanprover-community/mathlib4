/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Filter.IndicatorFunction
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.ContinuousFunction.Compact

#align_import measure_theory.integral.set_integral from "leanprover-community/mathlib"@"24e0c85412ff6adbeca08022c25ba4876eedf37a"

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`integral_union`, `integral_empty`, `integral_univ`.

We use the property `IntegrableOn f s μ := Integrable f (μ.restrict s)`, defined in
`MeasureTheory.IntegrableOn`. We also defined in that same file a predicate
`IntegrableAtFilter (f : α → E) (l : Filter α) (μ : Measure α)` saying that `f` is integrable at
some set `s ∈ l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `Filter.Tendsto.integral_sub_linear_isLittleO_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ μ.ae`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.smallSets`, i.e. for any `ε>0` there exists `t ∈ l` such that
`‖∫ x in s, f x ∂μ - μ s • c‖ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ a in s, f a ∂μ` is `MeasureTheory.integral (μ.restrict s) f`
* `∫ a in s, f a` is `∫ a in s, f a ∂volume`

Note that the set notations are defined in the file `MeasureTheory/Integral/Bochner`,
but we reference them here because all theorems about set integrals are in this file.

-/


assert_not_exists InnerProductSpace

noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Classical Topology Interval BigOperators Filter ENNReal NNReal MeasureTheory

variable {α β E F : Type*} [MeasurableSpace α]

namespace MeasureTheory

section NormedAddCommGroup

variable [NormedAddCommGroup E] {f g : α → E} {s t : Set α} {μ ν : Measure α} {l l' : Filter α}

variable [NormedSpace ℝ E]

theorem set_integral_congr_ae₀ (hs : NullMeasurableSet s μ) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff'₀ hs).2 h)
#align measure_theory.set_integral_congr_ae₀ MeasureTheory.set_integral_congr_ae₀

theorem set_integral_congr_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff' hs).2 h)
#align measure_theory.set_integral_congr_ae MeasureTheory.set_integral_congr_ae

theorem set_integral_congr₀ (hs : NullMeasurableSet s μ) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  set_integral_congr_ae₀ hs <| eventually_of_forall h
#align measure_theory.set_integral_congr₀ MeasureTheory.set_integral_congr₀

theorem set_integral_congr (hs : MeasurableSet s) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  set_integral_congr_ae hs <| eventually_of_forall h
#align measure_theory.set_integral_congr MeasureTheory.set_integral_congr

theorem set_integral_congr_set_ae (hst : s =ᵐ[μ] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  rw [Measure.restrict_congr_set hst]
#align measure_theory.set_integral_congr_set_ae MeasureTheory.set_integral_congr_set_ae

theorem integral_union_ae (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ∫ x in s ∪ t, f x ∂μ = (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  simp only [IntegrableOn, Measure.restrict_union₀ hst ht, integral_add_measure hfs hft]
#align measure_theory.integral_union_ae MeasureTheory.integral_union_ae

theorem integral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : ∫ x in s ∪ t, f x ∂μ = (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ :=
  integral_union_ae hst.aedisjoint ht.nullMeasurableSet hfs hft
#align measure_theory.integral_union MeasureTheory.integral_union

theorem integral_diff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts : t ⊆ s) :
    ∫ x in s \ t, f x ∂μ = (∫ x in s, f x ∂μ) - ∫ x in t, f x ∂μ := by
  rw [eq_sub_iff_add_eq, ← integral_union, diff_union_of_subset hts]
  exacts [disjoint_sdiff_self_left, ht, hfs.mono_set (diff_subset _ _), hfs.mono_set hts]
#align measure_theory.integral_diff MeasureTheory.integral_diff

theorem integral_inter_add_diff₀ (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) :
    ((∫ x in s ∩ t, f x ∂μ) + ∫ x in s \ t, f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← Measure.restrict_inter_add_diff₀ s ht, integral_add_measure]
  · exact Integrable.mono_measure hfs (Measure.restrict_mono (inter_subset_left _ _) le_rfl)
  · exact Integrable.mono_measure hfs (Measure.restrict_mono (diff_subset _ _) le_rfl)
#align measure_theory.integral_inter_add_diff₀ MeasureTheory.integral_inter_add_diff₀

theorem integral_inter_add_diff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) :
    ((∫ x in s ∩ t, f x ∂μ) + ∫ x in s \ t, f x ∂μ) = ∫ x in s, f x ∂μ :=
  integral_inter_add_diff₀ ht.nullMeasurableSet hfs
#align measure_theory.integral_inter_add_diff MeasureTheory.integral_inter_add_diff

theorem integral_finset_biUnion {ι : Type*} (t : Finset ι) {s : ι → Set α}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i in t, ∫ x in s i, f x ∂μ := by
  induction' t using Finset.induction_on with a t hat IH hs h's
  · simp
  · simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [integral_union _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact Finset.measurableSet_biUnion _ hs.2
#align measure_theory.integral_finset_bUnion MeasureTheory.integral_finset_biUnion

theorem integral_fintype_iUnion {ι : Type*} [Fintype ι] {s : ι → Set α}
    (hs : ∀ i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : ∀ i, IntegrableOn f (s i) μ) : ∫ x in ⋃ i, s i, f x ∂μ = ∑ i, ∫ x in s i, f x ∂μ := by
  convert integral_finset_biUnion Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]
#align measure_theory.integral_fintype_Union MeasureTheory.integral_fintype_iUnion

theorem integral_empty : ∫ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, integral_zero_measure]
#align measure_theory.integral_empty MeasureTheory.integral_empty

theorem integral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [Measure.restrict_univ]
#align measure_theory.integral_univ MeasureTheory.integral_univ

theorem integral_add_compl₀ (hs : NullMeasurableSet s μ) (hfi : Integrable f μ) :
    ((∫ x in s, f x ∂μ) + ∫ x in sᶜ, f x ∂μ) = ∫ x, f x ∂μ := by
  rw [← integral_union_ae (@disjoint_compl_right (Set α) _ _).aedisjoint hs.compl hfi.integrableOn
      hfi.integrableOn,
    union_compl_self, integral_univ]
#align measure_theory.integral_add_compl₀ MeasureTheory.integral_add_compl₀

theorem integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ((∫ x in s, f x ∂μ) + ∫ x in sᶜ, f x ∂μ) = ∫ x, f x ∂μ :=
  integral_add_compl₀ hs.nullMeasurableSet hfi
#align measure_theory.integral_add_compl MeasureTheory.integral_add_compl

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases hfi : IntegrableOn f s μ; swap
  · rwa [integral_undef, integral_undef]
    rwa [integrable_indicator_iff hs]
  calc
    ∫ x, indicator s f x ∂μ = (∫ x in s, indicator s f x ∂μ) + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = (∫ x in s, f x ∂μ) + ∫ x in sᶜ, 0 ∂μ :=
      (congr_arg₂ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs)))
    _ = ∫ x in s, f x ∂μ := by simp
#align measure_theory.integral_indicator MeasureTheory.integral_indicator

theorem set_integral_indicator (ht : MeasurableSet t) :
    ∫ x in s, t.indicator f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [integral_indicator ht, Measure.restrict_restrict ht, Set.inter_comm]
#align measure_theory.set_integral_indicator MeasureTheory.set_integral_indicator

theorem ofReal_set_integral_one_of_measure_ne_top {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {s : Set α} (hs : μ s ≠ ∞) : ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = μ s :=
  calc
    ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = ENNReal.ofReal (∫ _ in s, ‖(1 : ℝ)‖ ∂μ) := by
      simp only [norm_one]
    _ = ∫⁻ _ in s, 1 ∂μ := by
      rw [ofReal_integral_norm_eq_lintegral_nnnorm (integrableOn_const.2 (Or.inr hs.lt_top))]
      simp only [nnnorm_one, ENNReal.coe_one]
    _ = μ s := set_lintegral_one _
#align measure_theory.of_real_set_integral_one_of_measure_ne_top MeasureTheory.ofReal_set_integral_one_of_measure_ne_top

theorem ofReal_set_integral_one {α : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] (s : Set α) : ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = μ s :=
  ofReal_set_integral_one_of_measure_ne_top (measure_ne_top μ s)
#align measure_theory.of_real_set_integral_one MeasureTheory.ofReal_set_integral_one

theorem integral_piecewise [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g sᶜ μ) :
    ∫ x, s.piecewise f g x ∂μ = (∫ x in s, f x ∂μ) + ∫ x in sᶜ, g x ∂μ := by
  rw [← Set.indicator_add_compl_eq_piecewise,
    integral_add' (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl),
    integral_indicator hs, integral_indicator hs.compl]
#align measure_theory.integral_piecewise MeasureTheory.integral_piecewise

theorem tendsto_set_integral_of_monotone {ι : Type*} [Countable ι] [SemilatticeSup ι]
    {s : ι → Set α} (hsm : ∀ i, MeasurableSet (s i)) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋃ n, s n, f a ∂μ)) := by
  have hfi' : (∫⁻ x in ⋃ n, s n, ‖f x‖₊ ∂μ) < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : MeasurableSet S := MeasurableSet.iUnion hsm
  have hsub : ∀ {i}, s i ⊆ S := @(subset_iUnion s)
  rw [← withDensity_apply _ hSm] at hfi'
  set ν := μ.withDensity fun x => ‖f x‖₊ with hν
  refine' Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε ε0 => _
  lift ε to ℝ≥0 using ε0.le
  have : ∀ᶠ i in atTop, ν (s i) ∈ Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_iUnion h_mono (ENNReal.Icc_mem_nhds hfi'.ne (ENNReal.coe_pos.2 ε0).ne')
  refine' this.mono fun i hi => _
  rw [mem_closedBall_iff_norm', ← integral_diff (hsm i) hfi hsub, ← coe_nnnorm, NNReal.coe_le_coe, ←
    ENNReal.coe_le_coe]
  refine' (ennnorm_integral_le_lintegral_ennnorm _).trans _
  rw [← withDensity_apply _ (hSm.diff (hsm _)), ← hν, measure_diff hsub (hsm _)]
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt <| ENNReal.add_lt_top.2 ⟨hfi', ENNReal.coe_lt_top⟩).ne]
#align measure_theory.tendsto_set_integral_of_monotone MeasureTheory.tendsto_set_integral_of_monotone

theorem hasSum_integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι → Set α}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ a in s n, f a ∂μ) (∫ a in ⋃ n, s n, f a ∂μ) := by
  simp only [IntegrableOn, Measure.restrict_iUnion_ae hd hm] at hfi ⊢
  exact hasSum_integral_measure hfi
#align measure_theory.has_sum_integral_Union_ae MeasureTheory.hasSum_integral_iUnion_ae

theorem hasSum_integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set α}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ a in s n, f a ∂μ) (∫ a in ⋃ n, s n, f a ∂μ) :=
  hasSum_integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (hd.mono fun _ _ h => h.aedisjoint)
    hfi
#align measure_theory.has_sum_integral_Union MeasureTheory.hasSum_integral_iUnion

theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set α} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    ∫ a in ⋃ n, s n, f a ∂μ = ∑' n, ∫ a in s n, f a ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion hm hd hfi)).symm
#align measure_theory.integral_Union MeasureTheory.integral_iUnion

theorem integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι → Set α}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) : ∫ a in ⋃ n, s n, f a ∂μ = ∑' n, ∫ a in s n, f a ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion_ae hm hd hfi)).symm
#align measure_theory.integral_Union_ae MeasureTheory.integral_iUnion_ae

theorem set_integral_eq_zero_of_ae_eq_zero (ht_eq : ∀ᵐ x ∂μ, x ∈ t → f x = 0) :
    ∫ x in t, f x ∂μ = 0 := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict t); swap
  · rw [integral_undef]
    contrapose! hf
    exact hf.1
  have : ∫ x in t, hf.mk f x ∂μ = 0 := by
    refine' integral_eq_zero_of_ae _
    rw [EventuallyEq,
      ae_restrict_iff (hf.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_zero)]
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  exact integral_congr_ae hf.ae_eq_mk
#align measure_theory.set_integral_eq_zero_of_ae_eq_zero MeasureTheory.set_integral_eq_zero_of_ae_eq_zero

theorem set_integral_eq_zero_of_forall_eq_zero (ht_eq : ∀ x ∈ t, f x = 0) :
    ∫ x in t, f x ∂μ = 0 :=
  set_integral_eq_zero_of_ae_eq_zero (eventually_of_forall ht_eq)
#align measure_theory.set_integral_eq_zero_of_forall_eq_zero MeasureTheory.set_integral_eq_zero_of_forall_eq_zero

theorem integral_union_eq_left_of_ae_aux (ht_eq : ∀ᵐ x ∂μ.restrict t, f x = 0)
    (haux : StronglyMeasurable f) (H : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  have h's : IntegrableOn f s μ := H.mono (subset_union_left _ _) le_rfl
  have A : ∀ u : Set α, ∫ x in u ∩ k, f x ∂μ = 0 := fun u =>
    set_integral_eq_zero_of_forall_eq_zero fun x hx => hx.2
  rw [← integral_inter_add_diff hk h's, ← integral_inter_add_diff hk H, A, A, zero_add, zero_add,
    union_diff_distrib, union_comm]
  apply set_integral_congr_set_ae
  rw [union_ae_eq_right]
  apply measure_mono_null (diff_subset _ _)
  rw [measure_zero_iff_ae_nmem]
  filter_upwards [ae_imp_of_ae_restrict ht_eq] with x hx h'x using h'x.2 (hx h'x.1)
#align measure_theory.integral_union_eq_left_of_ae_aux MeasureTheory.integral_union_eq_left_of_ae_aux

theorem integral_union_eq_left_of_ae (ht_eq : ∀ᵐ x ∂μ.restrict t, f x = 0) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  have ht : IntegrableOn f t μ := by apply integrableOn_zero.congr_fun_ae; symm; exact ht_eq
  by_cases H : IntegrableOn f (s ∪ t) μ; swap
  · rw [integral_undef H, integral_undef]; simpa [integrableOn_union, ht] using H
  let f' := H.1.mk f
  calc
    ∫ x : α in s ∪ t, f x ∂μ = ∫ x : α in s ∪ t, f' x ∂μ := integral_congr_ae H.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        integral_union_eq_left_of_ae_aux _ H.1.stronglyMeasurable_mk (H.congr_fun_ae H.1.ae_eq_mk)
      filter_upwards [ht_eq,
        ae_mono (Measure.restrict_mono (subset_union_right s t) le_rfl) H.1.ae_eq_mk] with x hx h'x
      rw [← h'x, hx]
    _ = ∫ x in s, f x ∂μ :=
      integral_congr_ae
        (ae_mono (Measure.restrict_mono (subset_union_left s t) le_rfl) H.1.ae_eq_mk.symm)
#align measure_theory.integral_union_eq_left_of_ae MeasureTheory.integral_union_eq_left_of_ae

theorem integral_union_eq_left_of_forall₀ {f : α → E} (ht : NullMeasurableSet t μ)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_ae ((ae_restrict_iff'₀ ht).2 (eventually_of_forall ht_eq))
#align measure_theory.integral_union_eq_left_of_forall₀ MeasureTheory.integral_union_eq_left_of_forall₀

theorem integral_union_eq_left_of_forall {f : α → E} (ht : MeasurableSet t)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_forall₀ ht.nullMeasurableSet ht_eq
#align measure_theory.integral_union_eq_left_of_forall MeasureTheory.integral_union_eq_left_of_forall

theorem set_integral_eq_of_subset_of_ae_diff_eq_zero_aux (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) (haux : StronglyMeasurable f)
    (h'aux : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  calc
    ∫ x in t, f x ∂μ = (∫ x in t ∩ k, f x ∂μ) + ∫ x in t \ k, f x ∂μ := by
      rw [integral_inter_add_diff hk h'aux]
    _ = ∫ x in t \ k, f x ∂μ := by
      rw [set_integral_eq_zero_of_forall_eq_zero fun x hx => ?_, zero_add]; exact hx.2
    _ = ∫ x in s \ k, f x ∂μ := by
      apply set_integral_congr_set_ae
      filter_upwards [h't] with x hx
      change (x ∈ t \ k) = (x ∈ s \ k)
      simp only [mem_preimage, mem_singleton_iff, eq_iff_iff, and_congr_left_iff, mem_diff]
      intro h'x
      by_cases xs : x ∈ s
      · simp only [xs, hts xs]
      · simp only [xs, iff_false_iff]
        intro xt
        exact h'x (hx ⟨xt, xs⟩)
    _ = (∫ x in s ∩ k, f x ∂μ) + ∫ x in s \ k, f x ∂μ := by
      have : ∀ x ∈ s ∩ k, f x = 0 := fun x hx => hx.2
      rw [set_integral_eq_zero_of_forall_eq_zero this, zero_add]
    _ = ∫ x in s, f x ∂μ := by rw [integral_inter_add_diff hk (h'aux.mono hts le_rfl)]
#align measure_theory.set_integral_eq_of_subset_of_ae_diff_eq_zero_aux MeasureTheory.set_integral_eq_of_subset_of_ae_diff_eq_zero_aux

/-- If a function vanishes almost everywhere on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is null-measurable. -/
theorem set_integral_eq_of_subset_of_ae_diff_eq_zero (ht : NullMeasurableSet t μ) (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases h : IntegrableOn f t μ; swap
  · have : ¬IntegrableOn f s μ := fun H => h (H.of_ae_diff_eq_zero ht h't)
    rw [integral_undef h, integral_undef this]
  let f' := h.1.mk f
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, f' x ∂μ := integral_congr_ae h.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        set_integral_eq_of_subset_of_ae_diff_eq_zero_aux hts _ h.1.stronglyMeasurable_mk
          (h.congr h.1.ae_eq_mk)
      filter_upwards [h't, ae_imp_of_ae_restrict h.1.ae_eq_mk] with x hx h'x h''x
      rw [← h'x h''x.1, hx h''x]
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      apply ae_restrict_of_ae_restrict_of_subset hts
      exact h.1.ae_eq_mk.symm

#align measure_theory.set_integral_eq_of_subset_of_ae_diff_eq_zero MeasureTheory.set_integral_eq_of_subset_of_ae_diff_eq_zero

/-- If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is measurable. -/
theorem set_integral_eq_of_subset_of_forall_diff_eq_zero (ht : MeasurableSet t) (hts : s ⊆ t)
    (h't : ∀ x ∈ t \ s, f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ :=
  set_integral_eq_of_subset_of_ae_diff_eq_zero ht.nullMeasurableSet hts
    (eventually_of_forall fun x hx => h't x hx)
#align measure_theory.set_integral_eq_of_subset_of_forall_diff_eq_zero MeasureTheory.set_integral_eq_of_subset_of_forall_diff_eq_zero

/-- If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space. -/
theorem set_integral_eq_integral_of_ae_compl_eq_zero (h : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  symm
  nth_rw 1 [← integral_univ]
  apply set_integral_eq_of_subset_of_ae_diff_eq_zero nullMeasurableSet_univ (subset_univ _)
  filter_upwards [h] with x hx h'x using hx h'x.2
#align measure_theory.set_integral_eq_integral_of_ae_compl_eq_zero MeasureTheory.set_integral_eq_integral_of_ae_compl_eq_zero

/-- If a function vanishes on `sᶜ`, then its integral on `s` coincides with its integral on the
whole space. -/
theorem set_integral_eq_integral_of_forall_compl_eq_zero (h : ∀ x, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ :=
  set_integral_eq_integral_of_ae_compl_eq_zero (eventually_of_forall h)
#align measure_theory.set_integral_eq_integral_of_forall_compl_eq_zero MeasureTheory.set_integral_eq_integral_of_forall_compl_eq_zero

theorem set_integral_neg_eq_set_integral_nonpos [LinearOrder E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x ≤ 0}, f x ∂μ := by
  have h_union : {x | f x ≤ 0} = {x | f x < 0} ∪ {x | f x = 0} := by
    ext; simp_rw [Set.mem_union, Set.mem_setOf_eq]; exact le_iff_lt_or_eq
  rw [h_union]
  have B : NullMeasurableSet {x | f x = 0} μ :=
    hf.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
  symm
  refine' integral_union_eq_left_of_ae _
  filter_upwards [ae_restrict_mem₀ B] with x hx using hx
#align measure_theory.set_integral_neg_eq_set_integral_nonpos MeasureTheory.set_integral_neg_eq_set_integral_nonpos

theorem integral_norm_eq_pos_sub_neg {f : α → ℝ} (hfi : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = (∫ x in {x | 0 ≤ f x}, f x ∂μ) - ∫ x in {x | f x ≤ 0}, f x ∂μ :=
  have h_meas : NullMeasurableSet {x | 0 ≤ f x} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le hfi.1
  calc
    ∫ x, ‖f x‖ ∂μ = (∫ x in {x | 0 ≤ f x}, ‖f x‖ ∂μ) + ∫ x in {x | 0 ≤ f x}ᶜ, ‖f x‖ ∂μ := by
      rw [← integral_add_compl₀ h_meas hfi.norm]
    _ = (∫ x in {x | 0 ≤ f x}, f x ∂μ) + ∫ x in {x | 0 ≤ f x}ᶜ, ‖f x‖ ∂μ := by
      congr 1
      refine' set_integral_congr₀ h_meas fun x hx => _
      dsimp only
      rw [Real.norm_eq_abs, abs_eq_self.mpr _]
      exact hx
    _ = (∫ x in {x | 0 ≤ f x}, f x ∂μ) - ∫ x in {x | 0 ≤ f x}ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine' set_integral_congr₀ h_meas.compl fun x hx => _
      dsimp only
      rw [Real.norm_eq_abs, abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff, Set.nmem_setOf_iff] at hx
      linarith
    _ = (∫ x in {x | 0 ≤ f x}, f x ∂μ) - ∫ x in {x | f x ≤ 0}, f x ∂μ := by
      rw [← set_integral_neg_eq_set_integral_nonpos hfi.1]; congr; ext1 x; simp
#align measure_theory.integral_norm_eq_pos_sub_neg MeasureTheory.integral_norm_eq_pos_sub_neg

theorem set_integral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = (μ s).toReal • c := by
  rw [integral_const, Measure.restrict_apply_univ]
#align measure_theory.set_integral_const MeasureTheory.set_integral_const

@[simp]
theorem integral_indicator_const [CompleteSpace E] (e : E) ⦃s : Set α⦄ (s_meas : MeasurableSet s) :
    (∫ a : α, s.indicator (fun _ : α => e) a ∂μ) = (μ s).toReal • e := by
  rw [integral_indicator s_meas, ← set_integral_const]
#align measure_theory.integral_indicator_const MeasureTheory.integral_indicator_const

@[simp]
theorem integral_indicator_one ⦃s : Set α⦄ (hs : MeasurableSet s) :
    ∫ a, s.indicator 1 a ∂μ = (μ s).toReal :=
  (integral_indicator_const 1 hs).trans ((smul_eq_mul _).trans (mul_one _))
#align measure_theory.integral_indicator_one MeasureTheory.integral_indicator_one

theorem set_integral_indicatorConstLp [CompleteSpace E]
    {p : ℝ≥0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (x : E) :
    ∫ a in s, indicatorConstLp p ht hμt x a ∂μ = (μ (t ∩ s)).toReal • x :=
  calc
    ∫ a in s, indicatorConstLp p ht hμt x a ∂μ = ∫ a in s, t.indicator (fun _ => x) a ∂μ := by
      rw [set_integral_congr_ae hs (indicatorConstLp_coeFn.mono fun x hx _ => hx)]
    _ = (μ (t ∩ s)).toReal • x := by rw [integral_indicator_const _ ht, Measure.restrict_apply ht]
set_option linter.uppercaseLean3 false in
#align measure_theory.set_integral_indicator_const_Lp MeasureTheory.set_integral_indicatorConstLp

theorem integral_indicatorConstLp [CompleteSpace E]
    {p : ℝ≥0∞} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (x : E) :
    ∫ a, indicatorConstLp p ht hμt x a ∂μ = (μ t).toReal • x :=
  calc
    ∫ a, indicatorConstLp p ht hμt x a ∂μ = ∫ a in univ, indicatorConstLp p ht hμt x a ∂μ := by
      rw [integral_univ]
    _ = (μ (t ∩ univ)).toReal • x := (set_integral_indicatorConstLp MeasurableSet.univ ht hμt x)
    _ = (μ t).toReal • x := by rw [inter_univ]
set_option linter.uppercaseLean3 false in
#align measure_theory.integral_indicator_const_Lp MeasureTheory.integral_indicatorConstLp

theorem set_integral_map {β} [MeasurableSpace β] {g : α → β} {f : β → E} {s : Set β}
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [Measure.restrict_map_of_aemeasurable hg hs,
    integral_map (hg.mono_measure Measure.restrict_le_self) (hf.mono_measure _)]
  exact Measure.map_mono_of_aemeasurable Measure.restrict_le_self hg
#align measure_theory.set_integral_map MeasureTheory.set_integral_map

theorem _root_.MeasurableEmbedding.set_integral_map {β} {_ : MeasurableSpace β} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → E) (s : Set β) :
    ∫ y in s, g y ∂Measure.map f μ = ∫ x in f ⁻¹' s, g (f x) ∂μ := by
  rw [hf.restrict_map, hf.integral_map]
#align measurable_embedding.set_integral_map MeasurableEmbedding.set_integral_map

theorem _root_.ClosedEmbedding.set_integral_map [TopologicalSpace α] [BorelSpace α] {β}
    [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] {g : α → β} {f : β → E} (s : Set β)
    (hg : ClosedEmbedding g) : ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
  hg.measurableEmbedding.set_integral_map _ _
#align closed_embedding.set_integral_map ClosedEmbedding.set_integral_map

theorem MeasurePreserving.set_integral_preimage_emb {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → E) (s : Set β) :
    (∫ x in f ⁻¹' s, g (f x) ∂μ) = ∫ y in s, g y ∂ν :=
  (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _
#align measure_theory.measure_preserving.set_integral_preimage_emb MeasureTheory.MeasurePreserving.set_integral_preimage_emb

theorem MeasurePreserving.set_integral_image_emb {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → E) (s : Set α) :
    ∫ y in f '' s, g y ∂ν = ∫ x in s, g (f x) ∂μ :=
  Eq.symm <| (h₁.restrict_image_emb h₂ s).integral_comp h₂ _
#align measure_theory.measure_preserving.set_integral_image_emb MeasureTheory.MeasurePreserving.set_integral_image_emb

theorem set_integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → E) (s : Set β) :
    ∫ y in s, f y ∂Measure.map e μ = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
  e.measurableEmbedding.set_integral_map f s
#align measure_theory.set_integral_map_equiv MeasureTheory.set_integral_map_equiv

theorem norm_set_integral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞)
    (hC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal := by
  rw [← Measure.restrict_apply_univ] at *
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨‹_›⟩
  exact norm_integral_le_of_norm_le_const hC
#align measure_theory.norm_set_integral_le_of_norm_le_const_ae MeasureTheory.norm_set_integral_le_of_norm_le_const_ae

theorem norm_set_integral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞)
    (hC : ∀ᵐ x ∂μ, x ∈ s → ‖f x‖ ≤ C) (hfm : AEStronglyMeasurable f (μ.restrict s)) :
    ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal := by
  apply norm_set_integral_le_of_norm_le_const_ae hs
  have A : ∀ᵐ x : α ∂μ, x ∈ s → ‖AEStronglyMeasurable.mk f hfm x‖ ≤ C := by
    filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
    rw [← h2 h3]
    exact h1 h3
  have B : MeasurableSet {x | ‖(hfm.mk f) x‖ ≤ C} :=
    hfm.stronglyMeasurable_mk.norm.measurable measurableSet_Iic
  filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
  rwa [h1]
#align measure_theory.norm_set_integral_le_of_norm_le_const_ae' MeasureTheory.norm_set_integral_le_of_norm_le_const_ae'

theorem norm_set_integral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
    (hC : ∀ᵐ x ∂μ, x ∈ s → ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae hs <| by
    rwa [ae_restrict_eq hsm, eventually_inf_principal]
#align measure_theory.norm_set_integral_le_of_norm_le_const_ae'' MeasureTheory.norm_set_integral_le_of_norm_le_const_ae''

theorem norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞) (hC : ∀ x ∈ s, ‖f x‖ ≤ C)
    (hfm : AEStronglyMeasurable f (μ.restrict s)) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae' hs (eventually_of_forall hC) hfm
#align measure_theory.norm_set_integral_le_of_norm_le_const MeasureTheory.norm_set_integral_le_of_norm_le_const

theorem norm_set_integral_le_of_norm_le_const' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal :=
  norm_set_integral_le_of_norm_le_const_ae'' hs hsm <| eventually_of_forall hC
#align measure_theory.norm_set_integral_le_of_norm_le_const' MeasureTheory.norm_set_integral_le_of_norm_le_const'

theorem set_integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi
#align measure_theory.set_integral_eq_zero_iff_of_nonneg_ae MeasureTheory.set_integral_eq_zero_iff_of_nonneg_ae

theorem set_integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ 0 < μ (support f ∩ s) := by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, Measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl
#align measure_theory.set_integral_pos_iff_support_of_nonneg_ae MeasureTheory.set_integral_pos_iff_support_of_nonneg_ae

theorem set_integral_gt_gt {R : ℝ} {f : α → ℝ} (hR : 0 ≤ R) (hfm : Measurable f)
    (hfint : IntegrableOn f {x | ↑R < f x} μ) (hμ : μ {x | ↑R < f x} ≠ 0) :
    (μ {x | ↑R < f x}).toReal * R < ∫ x in {x | ↑R < f x}, f x ∂μ := by
  have : IntegrableOn (fun _ => R) {x | ↑R < f x} μ := by
    refine' ⟨aestronglyMeasurable_const, lt_of_le_of_lt _ hfint.2⟩
    refine'
      set_lintegral_mono (Measurable.nnnorm _).coe_nnreal_ennreal hfm.nnnorm.coe_nnreal_ennreal
        fun x hx => _
    · exact measurable_const
    · simp only [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg hR,
        Real.nnnorm_of_nonneg (hR.trans <| le_of_lt hx), Subtype.mk_le_mk]
      exact le_of_lt hx
  rw [← sub_pos, ← smul_eq_mul, ← set_integral_const, ← integral_sub hfint this,
    set_integral_pos_iff_support_of_nonneg_ae]
  · rw [← zero_lt_iff] at hμ
    rwa [Set.inter_eq_self_of_subset_right]
    exact fun x hx => Ne.symm (ne_of_lt <| sub_pos.2 hx)
  · change ∀ᵐ x ∂μ.restrict _, _
    rw [ae_restrict_iff]
    · exact eventually_of_forall fun x hx => sub_nonneg.2 <| le_of_lt hx
    · exact measurableSet_le measurable_zero (hfm.sub measurable_const)
  · exact Integrable.sub hfint this
#align measure_theory.set_integral_gt_gt MeasureTheory.set_integral_gt_gt

theorem set_integral_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0) {f : α → E}
    (hf_meas : StronglyMeasurable[m] f) {s : Set α} (hs : MeasurableSet[m] s) :
    ∫ x in s, f x ∂μ = ∫ x in s, f x ∂μ.trim hm := by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]
#align measure_theory.set_integral_trim MeasureTheory.set_integral_trim

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the endpoint having zero measure, while the
unprimed ones use `[NoAtoms μ]`.
-/


section PartialOrder

variable [PartialOrder α] {a b : α}

theorem integral_Icc_eq_integral_Ioc' (ha : μ {a} = 0) :
    ∫ t in Icc a b, f t ∂μ = ∫ t in Ioc a b, f t ∂μ :=
  set_integral_congr_set_ae (Ioc_ae_eq_Icc' ha).symm
#align measure_theory.integral_Icc_eq_integral_Ioc' MeasureTheory.integral_Icc_eq_integral_Ioc'

theorem integral_Icc_eq_integral_Ico' (hb : μ {b} = 0) :
    ∫ t in Icc a b, f t ∂μ = ∫ t in Ico a b, f t ∂μ :=
  set_integral_congr_set_ae (Ico_ae_eq_Icc' hb).symm
#align measure_theory.integral_Icc_eq_integral_Ico' MeasureTheory.integral_Icc_eq_integral_Ico'

theorem integral_Ioc_eq_integral_Ioo' (hb : μ {b} = 0) :
    ∫ t in Ioc a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
  set_integral_congr_set_ae (Ioo_ae_eq_Ioc' hb).symm
#align measure_theory.integral_Ioc_eq_integral_Ioo' MeasureTheory.integral_Ioc_eq_integral_Ioo'

theorem integral_Ico_eq_integral_Ioo' (ha : μ {a} = 0) :
    ∫ t in Ico a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
  set_integral_congr_set_ae (Ioo_ae_eq_Ico' ha).symm
#align measure_theory.integral_Ico_eq_integral_Ioo' MeasureTheory.integral_Ico_eq_integral_Ioo'

theorem integral_Icc_eq_integral_Ioo' (ha : μ {a} = 0) (hb : μ {b} = 0) :
    ∫ t in Icc a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
  set_integral_congr_set_ae (Ioo_ae_eq_Icc' ha hb).symm
#align measure_theory.integral_Icc_eq_integral_Ioo' MeasureTheory.integral_Icc_eq_integral_Ioo'

theorem integral_Iic_eq_integral_Iio' (ha : μ {a} = 0) :
    ∫ t in Iic a, f t ∂μ = ∫ t in Iio a, f t ∂μ :=
  set_integral_congr_set_ae (Iio_ae_eq_Iic' ha).symm
#align measure_theory.integral_Iic_eq_integral_Iio' MeasureTheory.integral_Iic_eq_integral_Iio'

theorem integral_Ici_eq_integral_Ioi' (ha : μ {a} = 0) :
    ∫ t in Ici a, f t ∂μ = ∫ t in Ioi a, f t ∂μ :=
  set_integral_congr_set_ae (Ioi_ae_eq_Ici' ha).symm
#align measure_theory.integral_Ici_eq_integral_Ioi' MeasureTheory.integral_Ici_eq_integral_Ioi'

variable [NoAtoms μ]

theorem integral_Icc_eq_integral_Ioc : ∫ t in Icc a b, f t ∂μ = ∫ t in Ioc a b, f t ∂μ :=
  integral_Icc_eq_integral_Ioc' <| measure_singleton a
#align measure_theory.integral_Icc_eq_integral_Ioc MeasureTheory.integral_Icc_eq_integral_Ioc

theorem integral_Icc_eq_integral_Ico : ∫ t in Icc a b, f t ∂μ = ∫ t in Ico a b, f t ∂μ :=
  integral_Icc_eq_integral_Ico' <| measure_singleton b
#align measure_theory.integral_Icc_eq_integral_Ico MeasureTheory.integral_Icc_eq_integral_Ico

theorem integral_Ioc_eq_integral_Ioo : ∫ t in Ioc a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
  integral_Ioc_eq_integral_Ioo' <| measure_singleton b
#align measure_theory.integral_Ioc_eq_integral_Ioo MeasureTheory.integral_Ioc_eq_integral_Ioo

theorem integral_Ico_eq_integral_Ioo : ∫ t in Ico a b, f t ∂μ = ∫ t in Ioo a b, f t ∂μ :=
  integral_Ico_eq_integral_Ioo' <| measure_singleton a
#align measure_theory.integral_Ico_eq_integral_Ioo MeasureTheory.integral_Ico_eq_integral_Ioo

theorem integral_Icc_eq_integral_Ioo : ∫ t in Icc a b, f t ∂μ = ∫ t in Ico a b, f t ∂μ := by
  rw [integral_Icc_eq_integral_Ico, integral_Ico_eq_integral_Ioo]
#align measure_theory.integral_Icc_eq_integral_Ioo MeasureTheory.integral_Icc_eq_integral_Ioo

theorem integral_Iic_eq_integral_Iio : ∫ t in Iic a, f t ∂μ = ∫ t in Iio a, f t ∂μ :=
  integral_Iic_eq_integral_Iio' <| measure_singleton a
#align measure_theory.integral_Iic_eq_integral_Iio MeasureTheory.integral_Iic_eq_integral_Iio

theorem integral_Ici_eq_integral_Ioi : ∫ t in Ici a, f t ∂μ = ∫ t in Ioi a, f t ∂μ :=
  integral_Ici_eq_integral_Ioi' <| measure_singleton a
#align measure_theory.integral_Ici_eq_integral_Ioi MeasureTheory.integral_Ici_eq_integral_Ioi

end PartialOrder

end NormedAddCommGroup

section Mono

variable {μ : Measure α} {f g : α → ℝ} {s t : Set α} (hf : IntegrableOn f s μ)
  (hg : IntegrableOn g s μ)

theorem set_integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) :
    (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  integral_mono_ae hf hg h
#align measure_theory.set_integral_mono_ae_restrict MeasureTheory.set_integral_mono_ae_restrict

theorem set_integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  set_integral_mono_ae_restrict hf hg (ae_restrict_of_ae h)
#align measure_theory.set_integral_mono_ae MeasureTheory.set_integral_mono_ae

theorem set_integral_mono_on (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) :
    (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  set_integral_mono_ae_restrict hf hg
    (by simp [hs, EventuallyLE, eventually_inf_principal, ae_of_all _ h])
#align measure_theory.set_integral_mono_on MeasureTheory.set_integral_mono_on

theorem set_integral_mono_on_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ := by
  refine' set_integral_mono_ae_restrict hf hg _; rwa [EventuallyLE, ae_restrict_iff' hs]
#align measure_theory.set_integral_mono_on_ae MeasureTheory.set_integral_mono_on_ae

theorem set_integral_mono (h : f ≤ g) : (∫ a in s, f a ∂μ) ≤ ∫ a in s, g a ∂μ :=
  integral_mono hf hg h
#align measure_theory.set_integral_mono MeasureTheory.set_integral_mono

theorem set_integral_mono_set (hfi : IntegrableOn f t μ) (hf : 0 ≤ᵐ[μ.restrict t] f)
    (hst : s ≤ᵐ[μ] t) : (∫ x in s, f x ∂μ) ≤ ∫ x in t, f x ∂μ :=
  integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi
#align measure_theory.set_integral_mono_set MeasureTheory.set_integral_mono_set

theorem set_integral_le_integral (hfi : Integrable f μ) (hf : 0 ≤ᵐ[μ] f) :
    (∫ x in s, f x ∂μ) ≤ ∫ x, f x ∂μ :=
  integral_mono_measure (Measure.restrict_le_self) hf hfi

theorem set_integral_ge_of_const_le {c : ℝ} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : ∀ x ∈ s, c ≤ f x) (hfint : IntegrableOn (fun x : α => f x) s μ) :
    c * (μ s).toReal ≤ ∫ x in s, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← set_integral_const c]
  exact set_integral_mono_on (integrableOn_const.2 (Or.inr hμs.lt_top)) hfint hs hf
#align measure_theory.set_integral_ge_of_const_le MeasureTheory.set_integral_ge_of_const_le

end Mono

section Nonneg

variable {μ : Measure α} {f : α → ℝ} {s : Set α}

theorem set_integral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) : 0 ≤ ∫ a in s, f a ∂μ :=
  integral_nonneg_of_ae hf
#align measure_theory.set_integral_nonneg_of_ae_restrict MeasureTheory.set_integral_nonneg_of_ae_restrict

theorem set_integral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)
#align measure_theory.set_integral_nonneg_of_ae MeasureTheory.set_integral_nonneg_of_ae

theorem set_integral_nonneg (hs : MeasurableSet s) (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    0 ≤ ∫ a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))
#align measure_theory.set_integral_nonneg MeasureTheory.set_integral_nonneg

theorem set_integral_nonneg_ae (hs : MeasurableSet s) (hf : ∀ᵐ a ∂μ, a ∈ s → 0 ≤ f a) :
    0 ≤ ∫ a in s, f a ∂μ :=
  set_integral_nonneg_of_ae_restrict <| by rwa [EventuallyLE, ae_restrict_iff' hs]
#align measure_theory.set_integral_nonneg_ae MeasureTheory.set_integral_nonneg_ae

theorem set_integral_le_nonneg {s : Set α} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : (∫ x in s, f x ∂μ) ≤ ∫ x in {y | 0 ≤ f y}, f x ∂μ := by
  rw [← integral_indicator hs, ←
    integral_indicator (stronglyMeasurable_const.measurableSet_le hf)]
  exact
    integral_mono (hfi.indicator hs)
      (hfi.indicator (stronglyMeasurable_const.measurableSet_le hf))
      (indicator_le_indicator_nonneg s f)
#align measure_theory.set_integral_le_nonneg MeasureTheory.set_integral_le_nonneg

theorem set_integral_nonpos_of_ae_restrict (hf : f ≤ᵐ[μ.restrict s] 0) : (∫ a in s, f a ∂μ) ≤ 0 :=
  integral_nonpos_of_ae hf
#align measure_theory.set_integral_nonpos_of_ae_restrict MeasureTheory.set_integral_nonpos_of_ae_restrict

theorem set_integral_nonpos_of_ae (hf : f ≤ᵐ[μ] 0) : (∫ a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)
#align measure_theory.set_integral_nonpos_of_ae MeasureTheory.set_integral_nonpos_of_ae

theorem set_integral_nonpos (hs : MeasurableSet s) (hf : ∀ a, a ∈ s → f a ≤ 0) :
    (∫ a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))
#align measure_theory.set_integral_nonpos MeasureTheory.set_integral_nonpos

theorem set_integral_nonpos_ae (hs : MeasurableSet s) (hf : ∀ᵐ a ∂μ, a ∈ s → f a ≤ 0) :
    (∫ a in s, f a ∂μ) ≤ 0 :=
  set_integral_nonpos_of_ae_restrict <| by rwa [EventuallyLE, ae_restrict_iff' hs]
#align measure_theory.set_integral_nonpos_ae MeasureTheory.set_integral_nonpos_ae

theorem set_integral_nonpos_le {s : Set α} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : (∫ x in {y | f y ≤ 0}, f x ∂μ) ≤ ∫ x in s, f x ∂μ := by
  rw [← integral_indicator hs, ←
    integral_indicator (hf.measurableSet_le stronglyMeasurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurableSet_le stronglyMeasurable_const))
      (hfi.indicator hs) (indicator_nonpos_le_indicator s f)
#align measure_theory.set_integral_nonpos_le MeasureTheory.set_integral_nonpos_le

end Nonneg

section IntegrableUnion

variable {μ : Measure α} [NormedAddCommGroup E] [Countable β]

theorem integrableOn_iUnion_of_summable_integral_norm {f : α → E} {s : β → Set α}
    (hs : ∀ b : β, MeasurableSet (s b)) (hi : ∀ b : β, IntegrableOn f (s b) μ)
    (h : Summable fun b : β => ∫ a : α in s b, ‖f a‖ ∂μ) : IntegrableOn f (iUnion s) μ := by
  refine' ⟨AEStronglyMeasurable.iUnion fun i => (hi i).1, (lintegral_iUnion_le _ _).trans_lt _⟩
  have B := fun b : β => lintegral_coe_eq_integral (fun a : α => ‖f a‖₊) (hi b).norm
  rw [tsum_congr B]
  have S' :
    Summable fun b : β =>
      (⟨∫ a : α in s b, ‖f a‖₊ ∂μ, set_integral_nonneg (hs b) fun a _ => NNReal.coe_nonneg _⟩ :
        NNReal) :=
    by rw [← NNReal.summable_coe]; exact h
  have S'' := ENNReal.tsum_coe_eq S'.hasSum
  simp_rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, coe_nnnorm] at S''
  convert ENNReal.ofReal_lt_top
#align measure_theory.integrable_on_Union_of_summable_integral_norm MeasureTheory.integrableOn_iUnion_of_summable_integral_norm

variable [TopologicalSpace α] [BorelSpace α] [MetrizableSpace α] [IsLocallyFiniteMeasure μ]

/-- If `s` is a countable family of compact sets, `f` is a continuous function, and the sequence
`‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable on the union of the `s i`. -/
theorem integrableOn_iUnion_of_summable_norm_restrict {f : C(α, E)} {s : β → Compacts α}
    (hf : Summable fun i : β => ‖f.restrict (s i)‖ * ENNReal.toReal (μ <| s i)) :
    IntegrableOn f (⋃ i : β, s i) μ := by
  refine'
    integrableOn_iUnion_of_summable_integral_norm (fun i => (s i).isCompact.isClosed.measurableSet)
      (fun i => (map_continuous f).continuousOn.integrableOn_compact (s i).isCompact)
      (summable_of_nonneg_of_le (fun ι => integral_nonneg fun x => norm_nonneg _) (fun i => _) hf)
  rw [← (Real.norm_of_nonneg (integral_nonneg fun a => norm_nonneg _) : ‖_‖ = ∫ x in s i, ‖f x‖ ∂μ)]
  exact
    norm_set_integral_le_of_norm_le_const' (s i).isCompact.measure_lt_top
      (s i).isCompact.isClosed.measurableSet fun x hx =>
      (norm_norm (f x)).symm ▸ (f.restrict (s i : Set α)).norm_coe_le_norm ⟨x, hx⟩
#align measure_theory.integrable_on_Union_of_summable_norm_restrict MeasureTheory.integrableOn_iUnion_of_summable_norm_restrict

/-- If `s` is a countable family of compact sets covering `α`, `f` is a continuous function, and
the sequence `‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable. -/
theorem integrable_of_summable_norm_restrict {f : C(α, E)} {s : β → Compacts α}
    (hf : Summable fun i : β => ‖f.restrict (s i)‖ * ENNReal.toReal (μ <| s i))
    (hs : ⋃ i : β, ↑(s i) = (univ : Set α)) : Integrable f μ := by
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_norm_restrict hf
#align measure_theory.integrable_of_summable_norm_restrict MeasureTheory.integrable_of_summable_norm_restrict

end IntegrableUnion

section TendstoMono

variable {μ : Measure α} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E] {s : ℕ → Set α}
  {f : α → E}

theorem _root_.Antitone.tendsto_set_integral (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α → ℝ := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine' tendsto_integral_of_dominated_convergence bound _ _ _ _
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti (zero_le n))).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine' fun n => eventually_of_forall fun x => _
    exact indicator_le_indicator_of_subset (h_anti (zero_le n)) (fun a => norm_nonneg _) _
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)
#align antitone.tendsto_set_integral Antitone.tendsto_set_integral

end TendstoMono

/-! ### Continuity of the set integral

We prove that for any set `s`, the function
`fun f : α →₁[μ] E => ∫ x in s, f x ∂μ` is continuous. -/


section ContinuousSetIntegral

variable [NormedAddCommGroup E] {𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {p : ℝ≥0∞} {μ : Measure α}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memℒp f).restrict s).toLp f`. This map is additive. -/
theorem Lp_toLp_restrict_add (f g : Lp E p μ) (s : Set α) :
    ((Lp.memℒp (f + g)).restrict s).toLp (⇑(f + g)) =
      ((Lp.memℒp f).restrict s).toLp f + ((Lp.memℒp g).restrict s).toLp g := by
  ext1
  refine' (ae_restrict_of_ae (Lp.coeFn_add f g)).mp _
  refine'
    (Lp.coeFn_add (Memℒp.toLp f ((Lp.memℒp f).restrict s))
          (Memℒp.toLp g ((Lp.memℒp g).restrict s))).mp _
  refine' (Memℒp.coeFn_toLp ((Lp.memℒp f).restrict s)).mp _
  refine' (Memℒp.coeFn_toLp ((Lp.memℒp g).restrict s)).mp _
  refine' (Memℒp.coeFn_toLp ((Lp.memℒp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => _
  rw [hx4, hx1, Pi.add_apply, hx2, hx3, hx5, Pi.add_apply]
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_to_Lp_restrict_add MeasureTheory.Lp_toLp_restrict_add

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memℒp f).restrict s).toLp f`. This map commutes with scalar multiplication. -/
theorem Lp_toLp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : Set α) :
    ((Lp.memℒp (c • f)).restrict s).toLp (⇑(c • f)) = c • ((Lp.memℒp f).restrict s).toLp f := by
  ext1
  refine' (ae_restrict_of_ae (Lp.coeFn_smul c f)).mp _
  refine' (Memℒp.coeFn_toLp ((Lp.memℒp f).restrict s)).mp _
  refine' (Memℒp.coeFn_toLp ((Lp.memℒp (c • f)).restrict s)).mp _
  refine'
    (Lp.coeFn_smul c (Memℒp.toLp f ((Lp.memℒp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => _
  rw [hx2, hx1, Pi.smul_apply, hx3, hx4, Pi.smul_apply]
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_to_Lp_restrict_smul MeasureTheory.Lp_toLp_restrict_smul

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memℒp f).restrict s).toLp f`. This map is non-expansive. -/
theorem norm_Lp_toLp_restrict_le (s : Set α) (f : Lp E p μ) :
    ‖((Lp.memℒp f).restrict s).toLp f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, ENNReal.toReal_le_toReal (Lp.snorm_ne_top _) (Lp.snorm_ne_top _)]
  refine' (le_of_eq _).trans (snorm_mono_measure _ Measure.restrict_le_self)
  exact snorm_congr_ae (Memℒp.coeFn_toLp _)
set_option linter.uppercaseLean3 false in
#align measure_theory.norm_Lp_to_Lp_restrict_le MeasureTheory.norm_Lp_toLp_restrict_le

variable (α F 𝕜)

/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def LpToLpRestrictCLM (μ : Measure α) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (s : Set α) :
    Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
  @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨⟨fun f => Memℒp.toLp f ((Lp.memℒp f).restrict s), fun f g => Lp_toLp_restrict_add f g s⟩,
      fun c f => Lp_toLp_restrict_smul c f s⟩
    1 (by intro f; rw [one_mul]; exact norm_Lp_toLp_restrict_le s f)
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_to_Lp_restrict_clm MeasureTheory.LpToLpRestrictCLM

variable {α F 𝕜}

variable (𝕜)

theorem LpToLpRestrictCLM_coeFn [Fact (1 ≤ p)] (s : Set α) (f : Lp F p μ) :
    LpToLpRestrictCLM α F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
  Memℒp.coeFn_toLp ((Lp.memℒp f).restrict s)
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_to_Lp_restrict_clm_coe_fn MeasureTheory.LpToLpRestrictCLM_coeFn

variable {𝕜}

@[continuity]
theorem continuous_set_integral [NormedSpace ℝ E] (s : Set α) :
    Continuous fun f : α →₁[μ] E => ∫ x in s, f x ∂μ := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : α →₁[μ] E => ∫ x in s, f x ∂μ) =
      integral (μ.restrict s) ∘ fun f => LpToLpRestrictCLM α E ℝ μ 1 s f := by
    ext1 f
    rw [Function.comp_apply, integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s f)]
  rw [h_comp]
  exact continuous_integral.comp (LpToLpRestrictCLM α E ℝ μ 1 s).continuous
#align measure_theory.continuous_set_integral MeasureTheory.continuous_set_integral

end ContinuousSetIntegral

end MeasureTheory

open MeasureTheory Asymptotics Metric

variable {ι : Type*} [NormedAddCommGroup E]

/-- Fundamental theorem of calculus for set integrals: if `μ` is a measure that is finite at a
filter `l` and `f` is a measurable function that has a finite limit `b` at `l ⊓ μ.ae`, then `∫ x in
s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that `s i` tends to `l.small_sets`
along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).toReal` in the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem Filter.Tendsto.integral_sub_linear_isLittleO_ae [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {l : Filter α} [l.IsMeasurablyGenerated] {f : α → E} {b : E}
    (h : Tendsto f (l ⊓ μ.ae) (𝓝 b)) (hfm : StronglyMeasurableAtFilter f l μ)
    (hμ : μ.FiniteAtFilter l) {s : ι → Set α} {li : Filter ι} (hs : Tendsto s li l.smallSets)
    (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • b) =o[li] m := by
  suffices : (fun s => (∫ x in s, f x ∂μ) - (μ s).toReal • b) =o[l.smallSets] fun s => (μ s).toReal
  exact (this.comp_tendsto hs).congr'
    (hsμ.mono fun a ha => by dsimp only [Function.comp_apply] at ha ⊢; rw [ha]) hsμ
  refine' isLittleO_iff.2 fun ε ε₀ => _
  have : ∀ᶠ s in l.smallSets, ∀ᶠ x in μ.ae, x ∈ s → f x ∈ closedBall b ε :=
    eventually_smallSets_eventually.2 (h.eventually <| closedBall_mem_nhds _ ε₀)
  filter_upwards [hμ.eventually, (hμ.integrableAtFilter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this]
  simp only [mem_closedBall, dist_eq_norm]
  intro s hμs h_integrable hfm h_norm
  rw [← set_integral_const, ← integral_sub h_integrable (integrableOn_const.2 <| Or.inr hμs),
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact norm_set_integral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub aestronglyMeasurable_const)
#align filter.tendsto.integral_sub_linear_is_o_ae Filter.Tendsto.integral_sub_linear_isLittleO_ae

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).toReal` in the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem ContinuousWithinAt.integral_sub_linear_isLittleO_ae [TopologicalSpace α]
    [OpensMeasurableSpace α] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α}
    [IsLocallyFiniteMeasure μ] {a : α} {t : Set α} {f : α → E} (ha : ContinuousWithinAt f t a)
    (ht : MeasurableSet t) (hfm : StronglyMeasurableAtFilter f (𝓝[t] a) μ) {s : ι → Set α}
    {li : Filter ι} (hs : Tendsto s li (𝓝[t] a).smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f a) =o[li] m :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (ha.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhdsWithin a t) hs m
    hsμ
#align continuous_within_at.integral_sub_linear_is_o_ae ContinuousWithinAt.integral_sub_linear_isLittleO_ae

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to
`(𝓝 a).smallSets` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).toReal` in
the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem ContinuousAt.integral_sub_linear_isLittleO_ae [TopologicalSpace α] [OpensMeasurableSpace α]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} [IsLocallyFiniteMeasure μ] {a : α}
    {f : α → E} (ha : ContinuousAt f a) (hfm : StronglyMeasurableAtFilter f (𝓝 a) μ) {s : ι → Set α}
    {li : Filter ι} (hs : Tendsto s li (𝓝 a).smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f a) =o[li] m :=
  (ha.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhds a) hs m hsμ
#align continuous_at.integral_sub_linear_is_o_ae ContinuousAt.integral_sub_linear_isLittleO_ae

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).toReal` in the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem ContinuousOn.integral_sub_linear_isLittleO_ae [TopologicalSpace α] [OpensMeasurableSpace α]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopologyEither α E] {μ : Measure α}
    [IsLocallyFiniteMeasure μ] {a : α} {t : Set α} {f : α → E} (hft : ContinuousOn f t) (ha : a ∈ t)
    (ht : MeasurableSet t) {s : ι → Set α} {li : Filter ι} (hs : Tendsto s li (𝓝[t] a).smallSets)
    (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f a) =o[li] m :=
  (hft a ha).integral_sub_linear_isLittleO_ae ht
    ⟨t, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩ hs m hsμ
#align continuous_on.integral_sub_linear_is_o_ae ContinuousOn.integral_sub_linear_isLittleO_ae

section

/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `ContinuousLinearMap.compLp`. We take advantage of this construction here.
-/


open scoped ComplexConjugate

variable {μ : Measure α} {𝕜 : Type*} [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {p : ENNReal}

namespace ContinuousLinearMap

variable [CompleteSpace F] [NormedSpace ℝ F]

theorem integral_compLp (L : E →L[𝕜] F) (φ : Lp E p μ) :
    (∫ a, (L.compLp φ) a ∂μ) = ∫ a, L (φ a) ∂μ :=
  integral_congr_ae <| coeFn_compLp _ _
set_option linter.uppercaseLean3 false in
#align continuous_linear_map.integral_comp_Lp ContinuousLinearMap.integral_compLp

theorem set_integral_compLp (L : E →L[𝕜] F) (φ : Lp E p μ) {s : Set α} (hs : MeasurableSet s) :
    (∫ a in s, (L.compLp φ) a ∂μ) = ∫ a in s, L (φ a) ∂μ :=
  set_integral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)
set_option linter.uppercaseLean3 false in
#align continuous_linear_map.set_integral_comp_Lp ContinuousLinearMap.set_integral_compLp

theorem continuous_integral_comp_L1 (L : E →L[𝕜] F) :
    Continuous fun φ : α →₁[μ] E => ∫ a : α, L (φ a) ∂μ := by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous
set_option linter.uppercaseLean3 false in
#align continuous_linear_map.continuous_integral_comp_L1 ContinuousLinearMap.continuous_integral_comp_L1

variable [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E →L[𝕜] F) {φ : α → E} (φ_int : Integrable φ μ) :
    (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) := by
  apply Integrable.induction (P := fun φ => (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas, ← @smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ s).toReal e,
      ContinuousLinearMap.map_smul, @smul_one_smul F ℝ 𝕜 _ _ _ _ _ (μ s).toReal (L e), ←
      integral_indicator_const (L e) s_meas]
    congr 1 with a
    erw [Set.indicator_comp_of_zero L.map_zero]
    rfl
  · intro f g _ f_int g_int hf hg
    simp [L.map_add, integral_add (μ := μ) f_int g_int,
      integral_add (μ := μ) (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg]
  · exact isClosed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
  · intro f g hfg _ hf
    convert hf using 1 <;> clear hf
    · exact integral_congr_ae (hfg.fun_comp L).symm
    · rw [integral_congr_ae hfg.symm]
  all_goals assumption
#align continuous_linear_map.integral_comp_comm ContinuousLinearMap.integral_comp_comm

theorem integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : α → H →L[𝕜] E}
    (φ_int : Integrable φ μ) (v : H) : (∫ a, φ a ∂μ) v = ∫ a, φ a v ∂μ :=
  ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
#align continuous_linear_map.integral_apply ContinuousLinearMap.integral_apply

theorem integral_comp_comm' (L : E →L[𝕜] F) {K} (hL : AntilipschitzWith K L) (φ : α → E) :
    (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) := by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun a => L (φ a)) μ := by
    erw [LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
    assumption
  simp [integral_undef, h, this]
#align continuous_linear_map.integral_comp_comm' ContinuousLinearMap.integral_comp_comm'

theorem integral_comp_L1_comm (L : E →L[𝕜] F) (φ : α →₁[μ] E) :
    (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) :=
  L.integral_comp_comm (L1.integrable_coeFn φ)
set_option linter.uppercaseLean3 false in
#align continuous_linear_map.integral_comp_L1_comm ContinuousLinearMap.integral_comp_L1_comm

end ContinuousLinearMap

namespace LinearIsometry

variable [CompleteSpace F] [NormedSpace ℝ F] [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : α → E) : (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
#align linear_isometry.integral_comp_comm LinearIsometry.integral_comp_comm

end LinearIsometry

namespace ContinuousLinearEquiv

variable [CompleteSpace F] [NormedSpace ℝ F] [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E ≃L[𝕜] F) (φ : α → E) : (∫ a, L (φ a) ∂μ) = L (∫ a, φ a ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
#align continuous_linear_equiv.integral_comp_comm ContinuousLinearEquiv.integral_comp_comm

end ContinuousLinearEquiv

variable [CompleteSpace E] [NormedSpace ℝ E] [CompleteSpace F] [NormedSpace ℝ F]

@[norm_cast]
theorem integral_ofReal {f : α → ℝ} : (∫ a, (f a : 𝕜) ∂μ) = ↑(∫ a, f a ∂μ) :=
  (@IsROrC.ofRealLi 𝕜 _).integral_comp_comm f
#align integral_of_real integral_ofReal

theorem integral_re {f : α → 𝕜} (hf : Integrable f μ) :
    (∫ a, IsROrC.re (f a) ∂μ) = IsROrC.re (∫ a, f a ∂μ) :=
  (@IsROrC.reClm 𝕜 _).integral_comp_comm hf
#align integral_re integral_re

theorem integral_im {f : α → 𝕜} (hf : Integrable f μ) :
    (∫ a, IsROrC.im (f a) ∂μ) = IsROrC.im (∫ a, f a ∂μ) :=
  (@IsROrC.imClm 𝕜 _).integral_comp_comm hf
#align integral_im integral_im

theorem integral_conj {f : α → 𝕜} : (∫ a, conj (f a) ∂μ) = conj (∫ a, f a ∂μ) :=
  (@IsROrC.conjLie 𝕜 _).toLinearIsometry.integral_comp_comm f
#align integral_conj integral_conj

theorem integral_coe_re_add_coe_im {f : α → 𝕜} (hf : Integrable f μ) :
    (∫ x, (IsROrC.re (f x) : 𝕜) ∂μ) + (∫ x, (IsROrC.im (f x) : 𝕜) ∂μ) * IsROrC.I = ∫ x, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← integral_smul, ← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul, mul_comm, IsROrC.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) IsROrC.I
#align integral_coe_re_add_coe_im integral_coe_re_add_coe_im

theorem integral_re_add_im {f : α → 𝕜} (hf : Integrable f μ) :
    ((∫ x, IsROrC.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x, IsROrC.im (f x) ∂μ : ℝ) * IsROrC.I =
      ∫ x, f x ∂μ := by
  rw [← integral_ofReal, ← integral_ofReal, integral_coe_re_add_coe_im hf]
#align integral_re_add_im integral_re_add_im

theorem set_integral_re_add_im {f : α → 𝕜} {i : Set α} (hf : IntegrableOn f i μ) :
    ((∫ x in i, IsROrC.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x in i, IsROrC.im (f x) ∂μ : ℝ) * IsROrC.I =
      ∫ x in i, f x ∂μ :=
  integral_re_add_im hf
#align set_integral_re_add_im set_integral_re_add_im

theorem fst_integral {f : α → E × F} (hf : Integrable f μ) : (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ :=
  ((ContinuousLinearMap.fst ℝ E F).integral_comp_comm hf).symm
#align fst_integral fst_integral

theorem snd_integral {f : α → E × F} (hf : Integrable f μ) : (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ :=
  ((ContinuousLinearMap.snd ℝ E F).integral_comp_comm hf).symm
#align snd_integral snd_integral

theorem integral_pair {f : α → E} {g : α → F} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (f x, g x) ∂μ) = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
  have := hf.prod_mk hg
  Prod.ext (fst_integral this) (snd_integral this)
#align integral_pair integral_pair

theorem integral_smul_const {𝕜 : Type*} [IsROrC 𝕜] [NormedSpace 𝕜 E] (f : α → 𝕜) (c : E) :
    ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c := by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 →L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp only [hc, integral_zero, smul_zero]
    rw [integral_undef hf, integral_undef, zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf]
#align integral_smul_const integral_smul_const

theorem integral_withDensity_eq_integral_smul {f : α → ℝ≥0} (f_meas : Measurable f) (g : α → E) :
    ∫ a, g a ∂μ.withDensity (fun x => f x) = ∫ a, f a • g a ∂μ := by
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine' Integrable.induction
    (P := fun g => ∫ a, g a ∂μ.withDensity (fun x => f x) = ∫ a, f a • g a ∂μ) _ _ _ _ hg
  · intro c s s_meas hs
    rw [integral_indicator s_meas]
    simp_rw [← indicator_smul_apply, integral_indicator s_meas]
    simp only [s_meas, integral_const, Measure.restrict_apply', univ_inter, withDensity_apply]
    rw [lintegral_coe_eq_integral, ENNReal.toReal_ofReal, ← integral_smul_const]
    · rfl
    · exact integral_nonneg fun x => NNReal.coe_nonneg _
    · refine' ⟨f_meas.coe_nnreal_real.aemeasurable.aestronglyMeasurable, _⟩
      rw [withDensity_apply _ s_meas] at hs
      rw [HasFiniteIntegral]
      convert hs with x
      simp only [NNReal.nnnorm_eq]
  · intro u u' _ u_int u'_int h h'
    change
      (∫ a : α, u a + u' a ∂μ.withDensity fun x : α => ↑(f x)) = ∫ a : α, f a • (u a + u' a) ∂μ
    simp_rw [smul_add]
    rw [integral_add u_int u'_int, h, h', integral_add]
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u_int
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u'_int
  · have C1 :
      Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) =>
        ∫ x, u x ∂μ.withDensity fun x => f x :=
      continuous_integral
    have C2 : Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) => ∫ x, f x • u x ∂μ := by
      have : Continuous ((fun u : Lp E 1 μ => ∫ x, u x ∂μ) ∘ withDensitySMulLI (E := E) μ f_meas) :=
        continuous_integral.comp (withDensitySMulLI (E := E) μ f_meas).continuous
      convert this with u
      simp only [Function.comp_apply, withDensitySMulLI_apply]
      exact integral_congr_ae (memℒ1_smul_of_L1_withDensity f_meas u).coeFn_toLp.symm
    exact isClosed_eq C1 C2
  · intro u v huv _ hu
    rw [← integral_congr_ae huv, hu]
    apply integral_congr_ae
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 huv] with x hx
    rcases eq_or_ne (f x) 0 with (h'x | h'x)
    · simp only [h'x, zero_smul]
    · rw [hx _]
      simpa only [Ne.def, ENNReal.coe_eq_zero] using h'x
#align integral_with_density_eq_integral_smul integral_withDensity_eq_integral_smul

theorem integral_withDensity_eq_integral_smul₀ {f : α → ℝ≥0} (hf : AEMeasurable f μ) (g : α → E) :
    ∫ a, g a ∂μ.withDensity (fun x => f x) = ∫ a, f a • g a ∂μ := by
  let f' := hf.mk _
  calc
    ∫ a, g a ∂μ.withDensity (fun x => f x) = ∫ a, g a ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ a, f' a • g a ∂μ := (integral_withDensity_eq_integral_smul hf.measurable_mk _)
    _ = ∫ a, f a • g a ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
#align integral_with_density_eq_integral_smul₀ integral_withDensity_eq_integral_smul₀

theorem set_integral_withDensity_eq_set_integral_smul {f : α → ℝ≥0} (f_meas : Measurable f)
    (g : α → E) {s : Set α} (hs : MeasurableSet s) :
    ∫ a in s, g a ∂μ.withDensity (fun x => f x) = ∫ a in s, f a • g a ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_smul f_meas]
#align set_integral_with_density_eq_set_integral_smul set_integral_withDensity_eq_set_integral_smul

theorem set_integral_withDensity_eq_set_integral_smul₀ {f : α → ℝ≥0} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (g : α → E) (hs : MeasurableSet s) :
    ∫ a in s, g a ∂μ.withDensity (fun x => f x) = ∫ a in s, f a • g a ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_smul₀ hf]
#align set_integral_with_density_eq_set_integral_smul₀ set_integral_withDensity_eq_set_integral_smul₀

end

section thickenedIndicator

variable [PseudoEMetricSpace α]

theorem measure_le_lintegral_thickenedIndicatorAux (μ : Measure α) {E : Set α}
    (E_mble : MeasurableSet E) (δ : ℝ) : μ E ≤ ∫⁻ a, (thickenedIndicatorAux δ E a : ℝ≥0∞) ∂μ := by
  convert_to lintegral μ (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator _ E_mble]
    simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  · apply lintegral_mono
    apply indicator_le_thickenedIndicatorAux
#align measure_le_lintegral_thickened_indicator_aux measure_le_lintegral_thickenedIndicatorAux

theorem measure_le_lintegral_thickenedIndicator (μ : Measure α) {E : Set α}
    (E_mble : MeasurableSet E) {δ : ℝ} (δ_pos : 0 < δ) :
    μ E ≤ ∫⁻ a, (thickenedIndicator δ_pos E a : ℝ≥0∞) ∂μ := by
  convert measure_le_lintegral_thickenedIndicatorAux μ E_mble δ
  dsimp
  simp only [thickenedIndicatorAux_lt_top.ne, ENNReal.coe_toNNReal, Ne.def, not_false_iff]
#align measure_le_lintegral_thickened_indicator measure_le_lintegral_thickenedIndicator

end thickenedIndicator

section BilinearMap

namespace MeasureTheory

variable {f : β → ℝ} {m m0 : MeasurableSpace β} {μ : Measure β}

theorem Integrable.simpleFunc_mul (g : SimpleFunc β ℝ) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  refine'
    SimpleFunc.induction (fun c s hs => _)
      (fun g₁ g₂ _ h_int₁ h_int₂ =>
        (h_int₁.add h_int₂).congr (by rw [SimpleFunc.coe_add, add_mul]))
      g
  simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
  have : Set.indicator s (Function.const β c) * f = s.indicator (c • f) := by
    ext1 x
    by_cases hx : x ∈ s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, Algebra.id.smul_eq_mul,
        ← Function.const_def]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_not_mem, not_false_iff, MulZeroClass.zero_mul]
  rw [this, integrable_indicator_iff hs]
  exact (hf.smul c).integrableOn
#align measure_theory.integrable.simple_func_mul MeasureTheory.Integrable.simpleFunc_mul

theorem Integrable.simpleFunc_mul' (hm : m ≤ m0) (g : @SimpleFunc β m ℝ) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  rw [← SimpleFunc.coe_toLargerSpace_eq hm g]; exact hf.simpleFunc_mul (g.toLargerSpace hm)
#align measure_theory.integrable.simple_func_mul' MeasureTheory.Integrable.simpleFunc_mul'

end MeasureTheory

end BilinearMap
