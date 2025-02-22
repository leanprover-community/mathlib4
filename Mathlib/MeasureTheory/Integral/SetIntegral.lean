/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`setIntegral_union`, `setIntegral_empty`, `setIntegral_univ`.

We use the property `IntegrableOn f s μ := Integrable f (μ.restrict s)`, defined in
`MeasureTheory.IntegrableOn`. We also defined in that same file a predicate
`IntegrableAtFilter (f : X → E) (l : Filter X) (μ : Measure X)` saying that `f` is integrable at
some set `s ∈ l`.

Finally, we prove a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integral, see `Filter.Tendsto.integral_sub_linear_isLittleO_ae` and its corollaries.
Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ ae μ`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.smallSets`, i.e. for any `ε>0` there exists `t ∈ l` such that
`‖∫ x in s, f x ∂μ - μ s • c‖ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ x in s, f x ∂μ` is `MeasureTheory.integral (μ.restrict s) f`
* `∫ x in s, f x` is `∫ x in s, f x ∂volume`

Note that the set notations are defined in the file `Mathlib/MeasureTheory/Integral/Bochner.lean`,
but we reference them here because all theorems about set integrals are in this file.

-/


assert_not_exists InnerProductSpace

noncomputable section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal

variable {X Y E F : Type*}

namespace MeasureTheory

variable [MeasurableSpace X]

section NormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : X → E} {s t : Set X} {μ : Measure X}

theorem setIntegral_congr_ae₀ (hs : NullMeasurableSet s μ) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff'₀ hs).2 h)

theorem setIntegral_congr_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff' hs).2 h)

theorem setIntegral_congr_fun₀ (hs : NullMeasurableSet s μ) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_ae₀ hs <| Eventually.of_forall h

@[deprecated (since := "2024-10-12")]
alias setIntegral_congr₀ := setIntegral_congr_fun₀

theorem setIntegral_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_ae hs <| Eventually.of_forall h

@[deprecated (since := "2024-10-12")]
alias setIntegral_congr := setIntegral_congr_fun

theorem setIntegral_congr_set (hst : s =ᵐ[μ] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  rw [Measure.restrict_congr_set hst]

@[deprecated (since := "2024-10-12")]
alias setIntegral_congr_set_ae := setIntegral_congr_set

theorem integral_union_ae (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ := by
  simp only [IntegrableOn, Measure.restrict_union₀ hst ht, integral_add_measure hfs hft]

theorem setIntegral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
  integral_union_ae hst.aedisjoint ht.nullMeasurableSet hfs hft

@[deprecated (since := "2024-10-12")]
alias integral_union := setIntegral_union

theorem integral_diff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts : t ⊆ s) :
    ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union, diff_union_of_subset hts]
  exacts [disjoint_sdiff_self_left, ht, hfs.mono_set diff_subset, hfs.mono_set hts]

theorem integral_inter_add_diff₀ (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) :
    ∫ x in s ∩ t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← Measure.restrict_inter_add_diff₀ s ht, integral_add_measure]
  · exact Integrable.mono_measure hfs (Measure.restrict_mono inter_subset_left le_rfl)
  · exact Integrable.mono_measure hfs (Measure.restrict_mono diff_subset le_rfl)

theorem integral_inter_add_diff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) :
    ∫ x in s ∩ t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_inter_add_diff₀ ht.nullMeasurableSet hfs

theorem integral_finset_biUnion {ι : Type*} (t : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction' t using Finset.induction_on with a t hat IH hs h's
  · simp
  · simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact Finset.measurableSet_biUnion _ hs.2

theorem integral_fintype_iUnion {ι : Type*} [Fintype ι] {s : ι → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : ∀ i, IntegrableOn f (s i) μ) : ∫ x in ⋃ i, s i, f x ∂μ = ∑ i, ∫ x in s i, f x ∂μ := by
  convert integral_finset_biUnion Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

theorem setIntegral_empty : ∫ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, integral_zero_measure]

@[deprecated (since := "2024-10-12")]
alias integral_empty := setIntegral_empty

theorem setIntegral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [Measure.restrict_univ]

@[deprecated (since := "2024-10-12")]
alias integral_univ := setIntegral_univ

theorem integral_add_compl₀ (hs : NullMeasurableSet s μ) (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ := by
  rw [
    ← integral_union_ae disjoint_compl_right.aedisjoint hs.compl hfi.integrableOn hfi.integrableOn,
    union_compl_self, setIntegral_univ]

theorem integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
  integral_add_compl₀ hs.nullMeasurableSet hfi

theorem setIntegral_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ := by
  rw [← integral_add_compl (μ := μ) hs hfi, add_sub_cancel_left]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases hfi : IntegrableOn f s μ; swap
  · rw [integral_undef hfi, integral_undef]
    rwa [integrable_indicator_iff hs]
  calc
    ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :=
      (congr_arg₂ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs)))
    _ = ∫ x in s, f x ∂μ := by simp

theorem setIntegral_indicator (ht : MeasurableSet t) :
    ∫ x in s, t.indicator f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [integral_indicator ht, Measure.restrict_restrict ht, Set.inter_comm]

theorem ofReal_setIntegral_one_of_measure_ne_top {X : Type*} {m : MeasurableSpace X}
    {μ : Measure X} {s : Set X} (hs : μ s ≠ ∞) : ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = μ s :=
  calc
    ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = ENNReal.ofReal (∫ _ in s, ‖(1 : ℝ)‖ ∂μ) := by
      simp only [norm_one]
    _ = ∫⁻ _ in s, 1 ∂μ := by
      simpa [ofReal_integral_norm_eq_lintegral_enorm (integrableOn_const.2 (.inr hs.lt_top))]
    _ = μ s := setLIntegral_one _

theorem ofReal_setIntegral_one {X : Type*} {_ : MeasurableSpace X} (μ : Measure X)
    [IsFiniteMeasure μ] (s : Set X) : ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = μ s :=
  ofReal_setIntegral_one_of_measure_ne_top (measure_ne_top μ s)

theorem integral_piecewise [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g sᶜ μ) :
    ∫ x, s.piecewise f g x ∂μ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, g x ∂μ := by
  rw [← Set.indicator_add_compl_eq_piecewise,
    integral_add' (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl),
    integral_indicator hs, integral_indicator hs.compl]

theorem tendsto_setIntegral_of_monotone
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι → Set X} (hsm : ∀ i, MeasurableSet (s i)) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ)) := by
  refine .of_neBot_imp fun hne ↦ ?_
  have := (atTop_neBot_iff.mp hne).2
  have hfi' : ∫⁻ x in ⋃ n, s n, ‖f x‖₊ ∂μ < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : MeasurableSet S := MeasurableSet.iUnion_of_monotone h_mono hsm
  have hsub {i} : s i ⊆ S := subset_iUnion s i
  rw [← withDensity_apply _ hSm] at hfi'
  set ν := μ.withDensity (‖f ·‖ₑ) with hν
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le
  have : ∀ᶠ i in atTop, ν (s i) ∈ Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_iUnion_atTop h_mono (ENNReal.Icc_mem_nhds hfi'.ne (ENNReal.coe_pos.2 ε0).ne')
  filter_upwards [this] with i hi
  rw [mem_closedBall_iff_norm', ← integral_diff (hsm i) hfi hsub, ← coe_nnnorm, NNReal.coe_le_coe, ←
    ENNReal.coe_le_coe]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← withDensity_apply _ (hSm.diff (hsm _)), ← hν, measure_diff hsub (hsm _).nullMeasurableSet]
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt <| ENNReal.add_lt_top.2 ⟨hfi', ENNReal.coe_lt_top⟩).ne]

theorem tendsto_setIntegral_of_antitone
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι → Set X} (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : ∃ i, IntegrableOn f (s i) μ) :
    Tendsto (fun i ↦ ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋂ n, s n, f x ∂μ)) := by
  refine .of_neBot_imp fun hne ↦ ?_
  have := (atTop_neBot_iff.mp hne).2
  rcases hfi with ⟨i₀, hi₀⟩
  suffices Tendsto (∫ x in s i₀, f x ∂μ - ∫ x in s i₀ \ s ·, f x ∂μ) atTop
      (𝓝 (∫ x in s i₀, f x ∂μ - ∫ x in ⋃ i, s i₀ \ s i, f x ∂μ)) by
    convert this.congr' <| (eventually_ge_atTop i₀).mono fun i hi ↦ ?_
    · rw [← diff_iInter, integral_diff _ hi₀ (iInter_subset _ _), sub_sub_cancel]
      exact .iInter_of_antitone h_anti hsm
    · rw [integral_diff (hsm i) hi₀ (h_anti hi), sub_sub_cancel]
  apply tendsto_const_nhds.sub
  refine tendsto_setIntegral_of_monotone (by measurability) ?_ ?_
  · exact fun i j h ↦ diff_subset_diff_right (h_anti h)
  · rw [← diff_iInter]
    exact hi₀.mono_set diff_subset

theorem hasSum_integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ) := by
  simp only [IntegrableOn, Measure.restrict_iUnion_ae hd hm] at hfi ⊢
  exact hasSum_integral_measure hfi

theorem hasSum_integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ) :=
  hasSum_integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (hd.mono fun _ _ h => h.aedisjoint)
    hfi

theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion hm hd hfi)).symm

theorem integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) : ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion_ae hm hd hfi)).symm

theorem setIntegral_eq_zero_of_ae_eq_zero (ht_eq : ∀ᵐ x ∂μ, x ∈ t → f x = 0) :
    ∫ x in t, f x ∂μ = 0 := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict t); swap
  · rw [integral_undef]
    contrapose! hf
    exact hf.1
  have : ∫ x in t, hf.mk f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq,
      ae_restrict_iff (hf.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_zero)]
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  exact integral_congr_ae hf.ae_eq_mk

theorem setIntegral_eq_zero_of_forall_eq_zero (ht_eq : ∀ x ∈ t, f x = 0) :
    ∫ x in t, f x ∂μ = 0 :=
  setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)

theorem integral_union_eq_left_of_ae_aux (ht_eq : ∀ᵐ x ∂μ.restrict t, f x = 0)
    (haux : StronglyMeasurable f) (H : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  have h's : IntegrableOn f s μ := H.mono subset_union_left le_rfl
  have A : ∀ u : Set X, ∫ x in u ∩ k, f x ∂μ = 0 := fun u =>
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx.2
  rw [← integral_inter_add_diff hk h's, ← integral_inter_add_diff hk H, A, A, zero_add, zero_add,
    union_diff_distrib, union_comm]
  apply setIntegral_congr_set
  rw [union_ae_eq_right]
  apply measure_mono_null diff_subset
  rw [measure_zero_iff_ae_nmem]
  filter_upwards [ae_imp_of_ae_restrict ht_eq] with x hx h'x using h'x.2 (hx h'x.1)

theorem integral_union_eq_left_of_ae (ht_eq : ∀ᵐ x ∂μ.restrict t, f x = 0) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  have ht : IntegrableOn f t μ := by apply integrableOn_zero.congr_fun_ae; symm; exact ht_eq
  by_cases H : IntegrableOn f (s ∪ t) μ; swap
  · rw [integral_undef H, integral_undef]; simpa [integrableOn_union, ht] using H
  let f' := H.1.mk f
  calc
    ∫ x : X in s ∪ t, f x ∂μ = ∫ x : X in s ∪ t, f' x ∂μ := integral_congr_ae H.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        integral_union_eq_left_of_ae_aux _ H.1.stronglyMeasurable_mk (H.congr_fun_ae H.1.ae_eq_mk)
      filter_upwards [ht_eq,
        ae_mono (Measure.restrict_mono subset_union_right le_rfl) H.1.ae_eq_mk] with x hx h'x
      rw [← h'x, hx]
    _ = ∫ x in s, f x ∂μ :=
      integral_congr_ae
        (ae_mono (Measure.restrict_mono subset_union_left le_rfl) H.1.ae_eq_mk.symm)

theorem integral_union_eq_left_of_forall₀ {f : X → E} (ht : NullMeasurableSet t μ)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_ae ((ae_restrict_iff'₀ ht).2 (Eventually.of_forall ht_eq))

theorem integral_union_eq_left_of_forall {f : X → E} (ht : MeasurableSet t)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_forall₀ ht.nullMeasurableSet ht_eq

theorem setIntegral_eq_of_subset_of_ae_diff_eq_zero_aux (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) (haux : StronglyMeasurable f)
    (h'aux : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  calc
    ∫ x in t, f x ∂μ = ∫ x in t ∩ k, f x ∂μ + ∫ x in t \ k, f x ∂μ := by
      rw [integral_inter_add_diff hk h'aux]
    _ = ∫ x in t \ k, f x ∂μ := by
      rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_, zero_add]; exact hx.2
    _ = ∫ x in s \ k, f x ∂μ := by
      apply setIntegral_congr_set
      filter_upwards [h't] with x hx
      change (x ∈ t \ k) = (x ∈ s \ k)
      simp only [mem_preimage, mem_singleton_iff, eq_iff_iff, and_congr_left_iff, mem_diff]
      intro h'x
      by_cases xs : x ∈ s
      · simp only [xs, hts xs]
      · simp only [xs, iff_false]
        intro xt
        exact h'x (hx ⟨xt, xs⟩)
    _ = ∫ x in s ∩ k, f x ∂μ + ∫ x in s \ k, f x ∂μ := by
      have : ∀ x ∈ s ∩ k, f x = 0 := fun x hx => hx.2
      rw [setIntegral_eq_zero_of_forall_eq_zero this, zero_add]
    _ = ∫ x in s, f x ∂μ := by rw [integral_inter_add_diff hk (h'aux.mono hts le_rfl)]

/-- If a function vanishes almost everywhere on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is null-measurable. -/
theorem setIntegral_eq_of_subset_of_ae_diff_eq_zero (ht : NullMeasurableSet t μ) (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases h : IntegrableOn f t μ; swap
  · have : ¬IntegrableOn f s μ := fun H => h (H.of_ae_diff_eq_zero ht h't)
    rw [integral_undef h, integral_undef this]
  let f' := h.1.mk f
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, f' x ∂μ := integral_congr_ae h.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        setIntegral_eq_of_subset_of_ae_diff_eq_zero_aux hts _ h.1.stronglyMeasurable_mk
          (h.congr h.1.ae_eq_mk)
      filter_upwards [h't, ae_imp_of_ae_restrict h.1.ae_eq_mk] with x hx h'x h''x
      rw [← h'x h''x.1, hx h''x]
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      apply ae_restrict_of_ae_restrict_of_subset hts
      exact h.1.ae_eq_mk.symm

/-- If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is measurable. -/
theorem setIntegral_eq_of_subset_of_forall_diff_eq_zero (ht : MeasurableSet t) (hts : s ⊆ t)
    (h't : ∀ x ∈ t \ s, f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ :=
  setIntegral_eq_of_subset_of_ae_diff_eq_zero ht.nullMeasurableSet hts
    (Eventually.of_forall fun x hx => h't x hx)

/-- If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space. -/
theorem setIntegral_eq_integral_of_ae_compl_eq_zero (h : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_diff_eq_zero nullMeasurableSet_univ (subset_univ _)
  filter_upwards [h] with x hx h'x using hx h'x.2

/-- If a function vanishes on `sᶜ`, then its integral on `s` coincides with its integral on the
whole space. -/
theorem setIntegral_eq_integral_of_forall_compl_eq_zero (h : ∀ x, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ :=
  setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall h)

theorem setIntegral_neg_eq_setIntegral_nonpos [PartialOrder E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x ≤ 0}, f x ∂μ := by
  have h_union : {x | f x ≤ 0} = {x | f x < 0} ∪ {x | f x = 0} := by
    simp_rw [le_iff_lt_or_eq, setOf_or]
  rw [h_union]
  have B : NullMeasurableSet {x | f x = 0} μ :=
    hf.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
  symm
  refine integral_union_eq_left_of_ae ?_
  filter_upwards [ae_restrict_mem₀ B] with x hx using hx

theorem integral_norm_eq_pos_sub_neg {f : X → ℝ} (hfi : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ :=
  have h_meas : NullMeasurableSet {x | 0 ≤ f x} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le hfi.1
  calc
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 ≤ f x}, ‖f x‖ ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ‖f x‖ ∂μ := by
      rw [← integral_add_compl₀ h_meas hfi.norm]
    _ = ∫ x in {x | 0 ≤ f x}, f x ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ‖f x‖ ∂μ := by
      congr 1
      refine setIntegral_congr_fun₀ h_meas fun x hx => ?_
      dsimp only
      rw [Real.norm_eq_abs, abs_eq_self.mpr _]
      exact hx
    _ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | 0 ≤ f x}ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine setIntegral_congr_fun₀ h_meas.compl fun x hx => ?_
      dsimp only
      rw [Real.norm_eq_abs, abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff, Set.nmem_setOf_iff] at hx
      linarith
    _ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ := by
      rw [← setIntegral_neg_eq_setIntegral_nonpos hfi.1, compl_setOf]; simp only [not_le]

theorem setIntegral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = (μ s).toReal • c := by
  rw [integral_const, Measure.restrict_apply_univ]

@[simp]
theorem integral_indicator_const [CompleteSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) :
    ∫ x : X, s.indicator (fun _ : X => e) x ∂μ = (μ s).toReal • e := by
  rw [integral_indicator s_meas, ← setIntegral_const]

@[simp]
theorem integral_indicator_one ⦃s : Set X⦄ (hs : MeasurableSet s) :
    ∫ x, s.indicator 1 x ∂μ = (μ s).toReal :=
  (integral_indicator_const 1 hs).trans ((smul_eq_mul _).trans (mul_one _))

theorem setIntegral_indicatorConstLp [CompleteSpace E]
    {p : ℝ≥0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (e : E) :
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = (μ (t ∩ s)).toReal • e :=
  calc
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = ∫ x in s, t.indicator (fun _ => e) x ∂μ := by
      rw [setIntegral_congr_ae hs (indicatorConstLp_coeFn.mono fun x hx _ => hx)]
    _ = (μ (t ∩ s)).toReal • e := by rw [integral_indicator_const _ ht, Measure.restrict_apply ht]

theorem integral_indicatorConstLp [CompleteSpace E]
    {p : ℝ≥0∞} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (e : E) :
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = (μ t).toReal • e :=
  calc
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = ∫ x in univ, indicatorConstLp p ht hμt e x ∂μ := by
      rw [setIntegral_univ]
    _ = (μ (t ∩ univ)).toReal • e := setIntegral_indicatorConstLp MeasurableSet.univ ht hμt e
    _ = (μ t).toReal • e := by rw [inter_univ]

theorem setIntegral_map {Y} [MeasurableSpace Y] {g : X → Y} {f : Y → E} {s : Set Y}
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [Measure.restrict_map_of_aemeasurable hg hs,
    integral_map (hg.mono_measure Measure.restrict_le_self) (hf.mono_measure _)]
  exact Measure.map_mono_of_aemeasurable Measure.restrict_le_self hg

theorem _root_.MeasurableEmbedding.setIntegral_map {Y} {_ : MeasurableSpace Y} {f : X → Y}
    (hf : MeasurableEmbedding f) (g : Y → E) (s : Set Y) :
    ∫ y in s, g y ∂Measure.map f μ = ∫ x in f ⁻¹' s, g (f x) ∂μ := by
  rw [hf.restrict_map, hf.integral_map]

theorem _root_.Topology.IsClosedEmbedding.setIntegral_map [TopologicalSpace X] [BorelSpace X] {Y}
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] {g : X → Y} {f : Y → E} (s : Set Y)
    (hg : IsClosedEmbedding g) : ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
  hg.measurableEmbedding.setIntegral_map _ _

@[deprecated (since := "2024-10-20")]
alias _root_.ClosedEmbedding.setIntegral_map := IsClosedEmbedding.setIntegral_map

theorem MeasurePreserving.setIntegral_preimage_emb {Y} {_ : MeasurableSpace Y} {f : X → Y} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : Y → E) (s : Set Y) :
    ∫ x in f ⁻¹' s, g (f x) ∂μ = ∫ y in s, g y ∂ν :=
  (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

theorem MeasurePreserving.setIntegral_image_emb {Y} {_ : MeasurableSpace Y} {f : X → Y} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : Y → E) (s : Set X) :
    ∫ y in f '' s, g y ∂ν = ∫ x in s, g (f x) ∂μ :=
  Eq.symm <| (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

theorem setIntegral_map_equiv {Y} [MeasurableSpace Y] (e : X ≃ᵐ Y) (f : Y → E) (s : Set Y) :
    ∫ y in s, f y ∂Measure.map e μ = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
  e.measurableEmbedding.setIntegral_map f s

theorem norm_setIntegral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞)
    (hC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal := by
  rw [← Measure.restrict_apply_univ] at *
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨hs⟩
  exact norm_integral_le_of_norm_le_const hC

theorem norm_setIntegral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞)
    (hC : ∀ᵐ x ∂μ, x ∈ s → ‖f x‖ ≤ C) (hfm : AEStronglyMeasurable f (μ.restrict s)) :
    ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal := by
  apply norm_setIntegral_le_of_norm_le_const_ae hs
  have A : ∀ᵐ x : X ∂μ, x ∈ s → ‖AEStronglyMeasurable.mk f hfm x‖ ≤ C := by
    filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
    rw [← h2 h3]
    exact h1 h3
  have B : MeasurableSet {x | ‖hfm.mk f x‖ ≤ C} :=
    hfm.stronglyMeasurable_mk.norm.measurable measurableSet_Iic
  filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
  rwa [h1]

theorem norm_setIntegral_le_of_norm_le_const_ae'' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
    (hC : ∀ᵐ x ∂μ, x ∈ s → ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal :=
  norm_setIntegral_le_of_norm_le_const_ae hs <| by
    rwa [ae_restrict_eq hsm, eventually_inf_principal]

theorem norm_setIntegral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞) (hC : ∀ x ∈ s, ‖f x‖ ≤ C)
    (hfm : AEStronglyMeasurable f (μ.restrict s)) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal :=
  norm_setIntegral_le_of_norm_le_const_ae' hs (Eventually.of_forall hC) hfm

theorem norm_setIntegral_le_of_norm_le_const' {C : ℝ} (hs : μ s < ∞) (hsm : MeasurableSet s)
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * (μ s).toReal :=
  norm_setIntegral_le_of_norm_le_const_ae'' hs hsm <| Eventually.of_forall hC

theorem setIntegral_eq_zero_iff_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi

theorem setIntegral_pos_iff_support_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ 0 < μ (support f ∩ s) := by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, Measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl

theorem setIntegral_gt_gt {R : ℝ} {f : X → ℝ} (hR : 0 ≤ R)
    (hfint : IntegrableOn f {x | ↑R < f x} μ) (hμ : μ {x | ↑R < f x} ≠ 0) :
    (μ {x | ↑R < f x}).toReal * R < ∫ x in {x | ↑R < f x}, f x ∂μ := by
  have : IntegrableOn (fun _ => R) {x | ↑R < f x} μ := by
    refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_ hfint.2⟩
    refine setLIntegral_mono_ae hfint.1.enorm <| ae_of_all _ fun x hx => ?_
    simp only [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg hR, enorm_eq_nnnorm,
      Real.nnnorm_of_nonneg (hR.trans <| le_of_lt hx), Subtype.mk_le_mk]
    exact le_of_lt hx
  rw [← sub_pos, ← smul_eq_mul, ← setIntegral_const, ← integral_sub hfint this,
    setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [← zero_lt_iff] at hμ
    rwa [Set.inter_eq_self_of_subset_right]
    exact fun x hx => Ne.symm (ne_of_lt <| sub_pos.2 hx)
  · rw [Pi.zero_def, EventuallyLE, ae_restrict_iff₀]
    · exact Eventually.of_forall fun x hx => sub_nonneg.2 <| le_of_lt hx
    · exact nullMeasurableSet_le aemeasurable_zero (hfint.1.aemeasurable.sub aemeasurable_const)
  · exact Integrable.sub hfint this

theorem setIntegral_trim {X} {m m0 : MeasurableSpace X} {μ : Measure X} (hm : m ≤ m0) {f : X → E}
    (hf_meas : StronglyMeasurable[m] f) {s : Set X} (hs : MeasurableSet[m] s) :
    ∫ x in s, f x ∂μ = ∫ x in s, f x ∂μ.trim hm := by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the endpoint having zero measure, while the
unprimed ones use `[NoAtoms μ]`.
-/

section PartialOrder

variable [PartialOrder X] {x y : X}

theorem integral_Icc_eq_integral_Ioc' (hx : μ {x} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
  setIntegral_congr_set (Ioc_ae_eq_Icc' hx).symm

theorem integral_Icc_eq_integral_Ico' (hy : μ {y} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ :=
  setIntegral_congr_set (Ico_ae_eq_Icc' hy).symm

theorem integral_Ioc_eq_integral_Ioo' (hy : μ {y} = 0) :
    ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Ioc' hy).symm

theorem integral_Ico_eq_integral_Ioo' (hx : μ {x} = 0) :
    ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Ico' hx).symm

theorem integral_Icc_eq_integral_Ioo' (hx : μ {x} = 0) (hy : μ {y} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Icc' hx hy).symm

theorem integral_Iic_eq_integral_Iio' (hx : μ {x} = 0) :
    ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ :=
  setIntegral_congr_set (Iio_ae_eq_Iic' hx).symm

theorem integral_Ici_eq_integral_Ioi' (hx : μ {x} = 0) :
    ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ :=
  setIntegral_congr_set (Ioi_ae_eq_Ici' hx).symm

variable [NoAtoms μ]

theorem integral_Icc_eq_integral_Ioc : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
  integral_Icc_eq_integral_Ioc' <| measure_singleton x

theorem integral_Icc_eq_integral_Ico : ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ :=
  integral_Icc_eq_integral_Ico' <| measure_singleton y

theorem integral_Ioc_eq_integral_Ioo : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  integral_Ioc_eq_integral_Ioo' <| measure_singleton y

theorem integral_Ico_eq_integral_Ioo : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  integral_Ico_eq_integral_Ioo' <| measure_singleton x

theorem integral_Icc_eq_integral_Ioo : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ := by
  rw [integral_Icc_eq_integral_Ico, integral_Ico_eq_integral_Ioo]

theorem integral_Iic_eq_integral_Iio : ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ :=
  integral_Iic_eq_integral_Iio' <| measure_singleton x

theorem integral_Ici_eq_integral_Ioi : ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ :=
  integral_Ici_eq_integral_Ioi' <| measure_singleton x

end PartialOrder

end NormedAddCommGroup

section Mono

variable {μ : Measure X} {f g : X → ℝ} {s t : Set X}

section
variable (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
include hf hg

theorem setIntegral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  integral_mono_ae hf hg h

theorem setIntegral_mono_ae (h : f ≤ᵐ[μ] g) : ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  setIntegral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

theorem setIntegral_mono_on (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  setIntegral_mono_ae_restrict hf hg
    (by simp [hs, EventuallyLE, eventually_inf_principal, ae_of_all _ h])

theorem setIntegral_mono_on_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  refine setIntegral_mono_ae_restrict hf hg ?_; rwa [EventuallyLE, ae_restrict_iff' hs]

theorem setIntegral_mono (h : f ≤ g) : ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  integral_mono hf hg h

end

theorem setIntegral_mono_set (hfi : IntegrableOn f t μ) (hf : 0 ≤ᵐ[μ.restrict t] f)
    (hst : s ≤ᵐ[μ] t) : ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
  integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi

theorem setIntegral_le_integral (hfi : Integrable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫ x in s, f x ∂μ ≤ ∫ x, f x ∂μ :=
  integral_mono_measure (Measure.restrict_le_self) hf hfi

theorem setIntegral_ge_of_const_le {c : ℝ} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : ∀ x ∈ s, c ≤ f x) (hfint : IntegrableOn (fun x : X => f x) s μ) :
    c * (μ s).toReal ≤ ∫ x in s, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← setIntegral_const c]
  exact setIntegral_mono_on (integrableOn_const.2 (Or.inr hμs.lt_top)) hfint hs hf

end Mono

section Nonneg

variable {μ : Measure X} {f : X → ℝ} {s : Set X}

theorem setIntegral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) : 0 ≤ ∫ x in s, f x ∂μ :=
  integral_nonneg_of_ae hf

theorem setIntegral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

theorem setIntegral_nonneg (hs : MeasurableSet s) (hf : ∀ x, x ∈ s → 0 ≤ f x) :
    0 ≤ ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

theorem setIntegral_nonneg_ae (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → 0 ≤ f x) :
    0 ≤ ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict <| by rwa [EventuallyLE, ae_restrict_iff' hs]

theorem setIntegral_le_nonneg {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : ∫ x in s, f x ∂μ ≤ ∫ x in {y | 0 ≤ f y}, f x ∂μ := by
  rw [← integral_indicator hs, ←
    integral_indicator (stronglyMeasurable_const.measurableSet_le hf)]
  exact
    integral_mono (hfi.indicator hs)
      (hfi.indicator (stronglyMeasurable_const.measurableSet_le hf))
      (indicator_le_indicator_nonneg s f)

theorem setIntegral_nonpos_of_ae_restrict (hf : f ≤ᵐ[μ.restrict s] 0) : ∫ x in s, f x ∂μ ≤ 0 :=
  integral_nonpos_of_ae hf

theorem setIntegral_nonpos_of_ae (hf : f ≤ᵐ[μ] 0) : ∫ x in s, f x ∂μ ≤ 0 :=
  setIntegral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

theorem setIntegral_nonpos_ae (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → f x ≤ 0) :
    ∫ x in s, f x ∂μ ≤ 0 :=
  setIntegral_nonpos_of_ae_restrict <| by rwa [EventuallyLE, ae_restrict_iff' hs]

theorem setIntegral_nonpos (hs : MeasurableSet s) (hf : ∀ x, x ∈ s → f x ≤ 0) :
    ∫ x in s, f x ∂μ ≤ 0 :=
  setIntegral_nonpos_ae hs <| ae_of_all μ hf

theorem setIntegral_nonpos_le {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : ∫ x in {y | f y ≤ 0}, f x ∂μ ≤ ∫ x in s, f x ∂μ := by
  rw [← integral_indicator hs, ←
    integral_indicator (hf.measurableSet_le stronglyMeasurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurableSet_le stronglyMeasurable_const))
      (hfi.indicator hs) (indicator_nonpos_le_indicator s f)

lemma Integrable.measure_le_integral {f : X → ℝ} (f_int : Integrable f μ) (f_nonneg : 0 ≤ᵐ[μ] f)
    {s : Set X} (hs : ∀ x ∈ s, 1 ≤ f x) :
    μ s ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal f_int f_nonneg]
  apply meas_le_lintegral₀
  · exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable f_int.1.aemeasurable
  · intro x hx
    simpa using ENNReal.ofReal_le_ofReal (hs x hx)

lemma integral_le_measure {f : X → ℝ} {s : Set X}
    (hs : ∀ x ∈ s, f x ≤ 1) (h's : ∀ x ∈ sᶜ, f x ≤ 0) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ s := by
  by_cases H : Integrable f μ; swap
  · simp [integral_undef H]
  let g x := max (f x) 0
  have g_int : Integrable g μ := H.pos_part
  have : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono H g_int (fun x ↦ le_max_left _ _)
  apply this.trans
  rw [ofReal_integral_eq_lintegral_ofReal g_int (Eventually.of_forall (fun x ↦ le_max_right _ _))]
  apply lintegral_le_meas
  · intro x
    apply ENNReal.ofReal_le_of_le_toReal
    by_cases H : x ∈ s
    · simpa [g] using hs x H
    · apply le_trans _ zero_le_one
      simpa [g] using h's x H
  · intro x hx
    simpa [g] using h's x hx

end Nonneg

section IntegrableUnion

variable {ι : Type*} [Countable ι] {μ : Measure X} [NormedAddCommGroup E]

theorem integrableOn_iUnion_of_summable_integral_norm {f : X → E} {s : ι → Set X}
    (hs : ∀ i : ι, MeasurableSet (s i)) (hi : ∀ i : ι, IntegrableOn f (s i) μ)
    (h : Summable fun i : ι => ∫ x : X in s i, ‖f x‖ ∂μ) : IntegrableOn f (iUnion s) μ := by
  refine ⟨AEStronglyMeasurable.iUnion fun i => (hi i).1, (lintegral_iUnion_le _ _).trans_lt ?_⟩
  have B := fun i => lintegral_coe_eq_integral (fun x : X => ‖f x‖₊) (hi i).norm
  simp_rw [enorm_eq_nnnorm, tsum_congr B]
  have S' :
    Summable fun i : ι =>
      (⟨∫ x : X in s i, ‖f x‖₊ ∂μ, setIntegral_nonneg (hs i) fun x _ => NNReal.coe_nonneg _⟩ :
        NNReal) := by
    rw [← NNReal.summable_coe]; exact h
  have S'' := ENNReal.tsum_coe_eq S'.hasSum
  simp_rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, coe_nnnorm] at S''
  convert ENNReal.ofReal_lt_top

variable [TopologicalSpace X] [BorelSpace X] [MetrizableSpace X] [IsLocallyFiniteMeasure μ]

/-- If `s` is a countable family of compact sets, `f` is a continuous function, and the sequence
`‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable on the union of the `s i`. -/
theorem integrableOn_iUnion_of_summable_norm_restrict {f : C(X, E)} {s : ι → Compacts X}
    (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * ENNReal.toReal (μ <| s i)) :
    IntegrableOn f (⋃ i : ι, s i) μ := by
  refine
    integrableOn_iUnion_of_summable_integral_norm (fun i => (s i).isCompact.isClosed.measurableSet)
      (fun i => (map_continuous f).continuousOn.integrableOn_compact (s i).isCompact)
      (.of_nonneg_of_le (fun ι => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hf)
  rw [← (Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _) : ‖_‖ = ∫ x in s i, ‖f x‖ ∂μ)]
  exact
    norm_setIntegral_le_of_norm_le_const' (s i).isCompact.measure_lt_top
      (s i).isCompact.isClosed.measurableSet fun x hx =>
      (norm_norm (f x)).symm ▸ (f.restrict (s i : Set X)).norm_coe_le_norm ⟨x, hx⟩

/-- If `s` is a countable family of compact sets covering `X`, `f` is a continuous function, and
the sequence `‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable. -/
theorem integrable_of_summable_norm_restrict {f : C(X, E)} {s : ι → Compacts X}
    (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * ENNReal.toReal (μ <| s i))
    (hs : ⋃ i : ι, ↑(s i) = (univ : Set X)) : Integrable f μ := by
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_norm_restrict hf

end IntegrableUnion

/-! ### Continuity of the set integral

We prove that for any set `s`, the function
`fun f : X →₁[μ] E => ∫ x in s, f x ∂μ` is continuous. -/


section ContinuousSetIntegral

variable [NormedAddCommGroup E]
  {𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p : ℝ≥0∞} {μ : Measure X}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memℒp f).restrict s).toLp f`. This map is additive. -/
theorem Lp_toLp_restrict_add (f g : Lp E p μ) (s : Set X) :
    ((Lp.memℒp (f + g)).restrict s).toLp (⇑(f + g)) =
      ((Lp.memℒp f).restrict s).toLp f + ((Lp.memℒp g).restrict s).toLp g := by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_add f g)).mp ?_
  refine
    (Lp.coeFn_add (Memℒp.toLp f ((Lp.memℒp f).restrict s))
          (Memℒp.toLp g ((Lp.memℒp g).restrict s))).mp ?_
  refine (Memℒp.coeFn_toLp ((Lp.memℒp f).restrict s)).mp ?_
  refine (Memℒp.coeFn_toLp ((Lp.memℒp g).restrict s)).mp ?_
  refine (Memℒp.coeFn_toLp ((Lp.memℒp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => ?_
  rw [hx4, hx1, Pi.add_apply, hx2, hx3, hx5, Pi.add_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memℒp f).restrict s).toLp f`. This map commutes with scalar multiplication. -/
theorem Lp_toLp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : Set X) :
    ((Lp.memℒp (c • f)).restrict s).toLp (⇑(c • f)) = c • ((Lp.memℒp f).restrict s).toLp f := by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_smul c f)).mp ?_
  refine (Memℒp.coeFn_toLp ((Lp.memℒp f).restrict s)).mp ?_
  refine (Memℒp.coeFn_toLp ((Lp.memℒp (c • f)).restrict s)).mp ?_
  refine
    (Lp.coeFn_smul c (Memℒp.toLp f ((Lp.memℒp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => ?_
  simp only [hx2, hx1, hx3, hx4, Pi.smul_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memℒp f).restrict s).toLp f`. This map is non-expansive. -/
theorem norm_Lp_toLp_restrict_le (s : Set X) (f : Lp E p μ) :
    ‖((Lp.memℒp f).restrict s).toLp f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Memℒp.coeFn_toLp _)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

variable (X F 𝕜) in
/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def LpToLpRestrictCLM (μ : Measure X) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (s : Set X) :
    Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
  @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨⟨fun f => Memℒp.toLp f ((Lp.memℒp f).restrict s), fun f g => Lp_toLp_restrict_add f g s⟩,
      fun c f => Lp_toLp_restrict_smul c f s⟩
    1 (by intro f; rw [one_mul]; exact norm_Lp_toLp_restrict_le s f)

variable (𝕜) in
theorem LpToLpRestrictCLM_coeFn [Fact (1 ≤ p)] (s : Set X) (f : Lp F p μ) :
    LpToLpRestrictCLM X F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
  Memℒp.coeFn_toLp ((Lp.memℒp f).restrict s)

@[continuity]
theorem continuous_setIntegral [NormedSpace ℝ E] (s : Set X) :
    Continuous fun f : X →₁[μ] E => ∫ x in s, f x ∂μ := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : X →₁[μ] E => ∫ x in s, f x ∂μ) =
      integral (μ.restrict s) ∘ fun f => LpToLpRestrictCLM X E ℝ μ 1 s f := by
    ext1 f
    rw [Function.comp_apply, integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s f)]
  rw [h_comp]
  exact continuous_integral.comp (LpToLpRestrictCLM X E ℝ μ 1 s).continuous

end ContinuousSetIntegral

end MeasureTheory

section OpenPos

open Measure

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsOpenPosMeasure μ]

theorem Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ]
    {f : X → ℝ} {x : X} (f_cont : Continuous f) (f_comp : HasCompactSupport f) (f_nonneg : 0 ≤ f)
    (f_x : f x ≠ 0) : 0 < ∫ x, f x ∂μ :=
  integral_pos_of_integrable_nonneg_nonzero f_cont (f_cont.integrable_of_hasCompactSupport f_comp)
    f_nonneg f_x

end OpenPos

section Support

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {mX : MeasurableSpace X}
  {ν : Measure X} {F : X → M}

theorem MeasureTheory.setIntegral_support : ∫ x in support F, F x ∂ν = ∫ x, F x ∂ν := by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ (subset_univ (support F))]
  exact fun _ hx => nmem_support.mp <| not_mem_of_mem_diff hx

theorem MeasureTheory.setIntegral_tsupport [TopologicalSpace X] :
    ∫ x in tsupport F, F x ∂ν = ∫ x, F x ∂ν := by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ (subset_univ (tsupport F))]
  exact fun _ hx => image_eq_zero_of_nmem_tsupport <| not_mem_of_mem_diff hx

end Support

/-! Fundamental theorem of calculus for set integrals -/
section FTC

open MeasureTheory Asymptotics Metric

variable [MeasurableSpace X] {ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fundamental theorem of calculus for set integrals:
if `μ` is a measure that is finite at a filter `l` and
`f` is a measurable function that has a finite limit `b` at `l ⊓ ae μ`, then
`∫ x in s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that
`s i` tends to `l.smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).toReal` in the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem Filter.Tendsto.integral_sub_linear_isLittleO_ae
    {μ : Measure X} {l : Filter X} [l.IsMeasurablyGenerated] {f : X → E} {b : E}
    (h : Tendsto f (l ⊓ ae μ) (𝓝 b)) (hfm : StronglyMeasurableAtFilter f l μ)
    (hμ : μ.FiniteAtFilter l) {s : ι → Set X} {li : Filter ι} (hs : Tendsto s li l.smallSets)
    (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • b) =o[li] m := by
  suffices
      (fun s => (∫ x in s, f x ∂μ) - (μ s).toReal • b) =o[l.smallSets] fun s => (μ s).toReal from
    (this.comp_tendsto hs).congr'
      (hsμ.mono fun a ha => by dsimp only [Function.comp_apply] at ha ⊢; rw [ha]) hsμ
  refine isLittleO_iff.2 fun ε ε₀ => ?_
  have : ∀ᶠ s in l.smallSets, ∀ᵐ x ∂μ, x ∈ s → f x ∈ closedBall b ε :=
    eventually_smallSets_eventually.2 (h.eventually <| closedBall_mem_nhds _ ε₀)
  filter_upwards [hμ.eventually, (hμ.integrableAtFilter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this]
  simp only [mem_closedBall, dist_eq_norm]
  intro s hμs h_integrable hfm h_norm
  rw [← setIntegral_const, ← integral_sub h_integrable (integrableOn_const.2 <| Or.inr hμs),
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact norm_setIntegral_le_of_norm_le_const_ae' hμs h_norm (hfm.sub aestronglyMeasurable_const)

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `(μ (s i)).toReal` in the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem ContinuousWithinAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X}
    [IsLocallyFiniteMeasure μ] {x : X} {t : Set X} {f : X → E} (hx : ContinuousWithinAt f t x)
    (ht : MeasurableSet t) (hfm : StronglyMeasurableAtFilter f (𝓝[t] x) μ) {s : ι → Set X}
    {li : Filter ι} (hs : Tendsto s li (𝓝[t] x).smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  haveI : (𝓝[t] x).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hx.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhdsWithin x t) hs m
    hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to
`(𝓝 a).smallSets` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).toReal` in
the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem ContinuousAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X}
    {f : X → E} (hx : ContinuousAt f x) (hfm : StronglyMeasurableAtFilter f (𝓝 x) μ) {s : ι → Set X}
    {li : Filter ι} (hs : Tendsto s li (𝓝 x).smallSets) (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  (hx.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhds x) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `(μ (s i)).toReal` in the actual statement.

Often there is a good formula for `(μ (s i)).toReal`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => (μ (s i)).toReal) =ᶠ[li] m`. Without these
arguments, `m i = (μ (s i)).toReal` is used in the output. -/
theorem ContinuousOn.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X E] {μ : Measure X}
    [IsLocallyFiniteMeasure μ] {x : X} {t : Set X} {f : X → E} (hft : ContinuousOn f t) (hx : x ∈ t)
    (ht : MeasurableSet t) {s : ι → Set X} {li : Filter ι} (hs : Tendsto s li (𝓝[t] x).smallSets)
    (m : ι → ℝ := fun i => (μ (s i)).toReal)
    (hsμ : (fun i => (μ (s i)).toReal) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  (hft x hx).integral_sub_linear_isLittleO_ae ht
    ⟨t, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩ hs m hsμ

end FTC

section

variable [MeasurableSpace X]

/-! ### Continuous linear maps composed with integration

The goal of this section is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `ContinuousLinearMap.compLp`. We take advantage of this construction here.
-/

open scoped ComplexConjugate

variable {μ : Measure X} {𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p : ENNReal}

namespace ContinuousLinearMap

variable [NormedSpace ℝ F]

theorem integral_compLp (L : E →L[𝕜] F) (φ : Lp E p μ) :
    ∫ x, (L.compLp φ) x ∂μ = ∫ x, L (φ x) ∂μ :=
  integral_congr_ae <| coeFn_compLp _ _

theorem setIntegral_compLp (L : E →L[𝕜] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, (L.compLp φ) x ∂μ = ∫ x in s, L (φ x) ∂μ :=
  setIntegral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)

theorem continuous_integral_comp_L1 (L : E →L[𝕜] F) :
    Continuous fun φ : X →₁[μ] E => ∫ x : X, L (φ x) ∂μ := by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous

variable [CompleteSpace F] [NormedSpace ℝ E]

theorem integral_comp_comm [CompleteSpace E] (L : E →L[𝕜] F) {φ : X → E} (φ_int : Integrable φ μ) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  apply φ_int.induction (P := fun φ => ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas, ← @smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ s).toReal e,
      ContinuousLinearMap.map_smul, @smul_one_smul F ℝ 𝕜 _ _ _ _ _ (μ s).toReal (L e), ←
      integral_indicator_const (L e) s_meas]
    congr 1 with a
    rw [← Function.comp_def L, Set.indicator_comp_of_zero L.map_zero, Function.comp_apply]
  · intro f g _ f_int g_int hf hg
    simp [L.map_add, integral_add (μ := μ) f_int g_int,
      integral_add (μ := μ) (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg]
  · exact isClosed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
  · intro f g hfg _ hf
    convert hf using 1 <;> clear hf
    · exact integral_congr_ae (hfg.fun_comp L).symm
    · rw [integral_congr_ae hfg.symm]

theorem integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X → H →L[𝕜] E}
    (φ_int : Integrable φ μ) (v : H) : (∫ x, φ x ∂μ) v = ∫ x, φ x v ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
  · rcases subsingleton_or_nontrivial H with hH|hH
    · simp [Subsingleton.eq_zero v]
    · have : ¬(CompleteSpace (H →L[𝕜] E)) := by
        rwa [SeparatingDual.completeSpace_continuousLinearMap_iff]
      simp [integral, hE, this]

theorem _root_.ContinuousMultilinearMap.integral_apply {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
    {φ : X → ContinuousMultilinearMap 𝕜 M E} (φ_int : Integrable φ μ) (m : ∀ i, M i) :
    (∫ x, φ x ∂μ) m = ∫ x, φ x m ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousMultilinearMap.apply 𝕜 M E m).integral_comp_comm φ_int).symm
  · by_cases hm : ∀ i, m i ≠ 0
    · have : ¬ CompleteSpace (ContinuousMultilinearMap 𝕜 M E) := by
        rwa [SeparatingDual.completeSpace_continuousMultilinearMap_iff _ _ hm]
      simp [integral, hE, this]
    · push_neg at hm
      rcases hm with ⟨i, hi⟩
      simp [ContinuousMultilinearMap.map_coord_zero _ i hi]

variable [CompleteSpace E]

theorem integral_comp_comm' (L : E →L[𝕜] F) {K} (hL : AntilipschitzWith K L) (φ : X → E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun x => L (φ x)) μ := by
    rwa [← Function.comp_def,
      LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [integral_undef, h, this]

theorem integral_comp_L1_comm (L : E →L[𝕜] F) (φ : X →₁[μ] E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.integral_comp_comm (L1.integrable_coeFn φ)

end ContinuousLinearMap

namespace LinearIsometry

variable [CompleteSpace F] [NormedSpace ℝ F] [CompleteSpace E] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

end LinearIsometry

namespace ContinuousLinearEquiv

variable [NormedSpace ℝ F] [NormedSpace ℝ E]

theorem integral_comp_comm (L : E ≃L[𝕜] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  have : CompleteSpace E ↔ CompleteSpace F :=
    completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding
  obtain ⟨_, _⟩|⟨_, _⟩ := iff_iff_and_or_not_and_not.mp this
  · exact L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
  · simp [integral, *]

end ContinuousLinearEquiv

section ContinuousMap

variable [TopologicalSpace Y] [CompactSpace Y]

lemma ContinuousMap.integral_apply [NormedSpace ℝ E] [CompleteSpace E] {f : X → C(Y, E)}
    (hf : Integrable f μ) (y : Y) : (∫ x, f x ∂μ) y = ∫ x, f x y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMap.evalCLM ℝ y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMap.evalCLM ℝ y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

open scoped ContinuousMapZero in
theorem ContinuousMapZero.integral_apply {R : Type*} [NormedCommRing R] [Zero Y]
    [NormedAlgebra ℝ R] [CompleteSpace R] {f : X → C(Y, R)₀}
    (hf : MeasureTheory.Integrable f μ) (y : Y) :
    (∫ (x : X), f x ∂μ) y = ∫ (x : X), (f x) y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMapZero.evalCLM ℝ y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMapZero.evalCLM ℝ y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

end ContinuousMap

@[norm_cast]
theorem integral_ofReal {f : X → ℝ} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ) :=
  (@RCLike.ofRealLI 𝕜 _).integral_comp_comm f

theorem integral_complex_ofReal {f : X → ℝ} : ∫ x, (f x : ℂ) ∂μ = ∫ x, f x ∂μ := integral_ofReal

theorem integral_re {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ) :=
  (@RCLike.reCLM 𝕜 _).integral_comp_comm hf

theorem integral_im {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.im (f x) ∂μ = RCLike.im (∫ x, f x ∂μ) :=
  (@RCLike.imCLM 𝕜 _).integral_comp_comm hf

theorem integral_conj {f : X → 𝕜} : ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ) :=
  (@RCLike.conjLIE 𝕜 _).toLinearIsometry.integral_comp_comm f

theorem integral_coe_re_add_coe_im {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, (re (f x) : 𝕜) ∂μ + (∫ x, (im (f x) : 𝕜) ∂μ) * RCLike.I = ∫ x, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← integral_smul, ← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul, mul_comm, RCLike.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) RCLike.I

theorem integral_re_add_im {f : X → 𝕜} (hf : Integrable f μ) :
    ((∫ x, RCLike.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x, RCLike.im (f x) ∂μ : ℝ) * RCLike.I =
      ∫ x, f x ∂μ := by
  rw [← integral_ofReal, ← integral_ofReal, integral_coe_re_add_coe_im hf]

theorem setIntegral_re_add_im {f : X → 𝕜} {i : Set X} (hf : IntegrableOn f i μ) :
    ((∫ x in i, RCLike.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x in i, RCLike.im (f x) ∂μ : ℝ) * RCLike.I =
      ∫ x in i, f x ∂μ :=
  integral_re_add_im hf

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma swap_integral (f : X → E × F) : (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ :=
  .symm <| (ContinuousLinearEquiv.prodComm ℝ E F).integral_comp_comm f

theorem fst_integral [CompleteSpace F] {f : X → E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.fst ℝ E F).integral_comp_comm hf).symm
  · have : ¬(CompleteSpace (E × F)) := fun h ↦ hE <| .fst_of_prod (β := F)
    simp [integral, *]

theorem snd_integral [CompleteSpace E] {f : X → E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ := by
  rw [← Prod.fst_swap, swap_integral]
  exact fst_integral <| hf.snd.prod_mk hf.fst

theorem integral_pair [CompleteSpace E] [CompleteSpace F] {f : X → E} {g : X → F}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
  have := hf.prod_mk hg
  Prod.ext (fst_integral this) (snd_integral this)

theorem integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    (f : X → 𝕜) (c : E) :
    ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c := by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 →L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp [hc, integral_zero, smul_zero]
    rw [integral_undef hf, integral_undef, zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf, not_false_eq_true]

theorem integral_withDensity_eq_integral_smul {f : X → ℝ≥0} (f_meas : Measurable f) (g : X → E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine Integrable.induction
    (P := fun g => ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ) ?_ ?_ ?_ ?_ hg
  · intro c s s_meas hs
    rw [integral_indicator s_meas]
    simp_rw [← indicator_smul_apply, integral_indicator s_meas]
    simp only [s_meas, integral_const, Measure.restrict_apply', univ_inter, withDensity_apply]
    rw [lintegral_coe_eq_integral, ENNReal.toReal_ofReal, ← integral_smul_const]
    · rfl
    · exact integral_nonneg fun x => NNReal.coe_nonneg _
    · refine ⟨f_meas.coe_nnreal_real.aemeasurable.aestronglyMeasurable, ?_⟩
      simpa [withDensity_apply _ s_meas, hasFiniteIntegral_iff_enorm] using hs
  · intro u u' _ u_int u'_int h h'
    change
      (∫ x : X, u x + u' x ∂μ.withDensity fun x : X => ↑(f x)) = ∫ x : X, f x • (u x + u' x) ∂μ
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
      simpa only [Ne, ENNReal.coe_eq_zero] using h'x

theorem integral_withDensity_eq_integral_smul₀ {f : X → ℝ≥0} (hf : AEMeasurable f μ) (g : X → E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  let f' := hf.mk _
  calc
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, g x ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ x, f' x • g x ∂μ := integral_withDensity_eq_integral_smul hf.measurable_mk _
    _ = ∫ x, f x • g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]

theorem setIntegral_withDensity_eq_setIntegral_smul {f : X → ℝ≥0} (f_meas : Measurable f)
    (g : X → E) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_smul f_meas]

theorem setIntegral_withDensity_eq_setIntegral_smul₀ {f : X → ℝ≥0} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (g : X → E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_smul₀ hf]

theorem setIntegral_withDensity_eq_setIntegral_smul₀' [SFinite μ] {f : X → ℝ≥0} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (g : X → E)  :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity' s, integral_withDensity_eq_integral_smul₀ hf]

end

section thickenedIndicator

variable [MeasurableSpace X] [PseudoEMetricSpace X]

theorem measure_le_lintegral_thickenedIndicatorAux (μ : Measure X) {E : Set X}
    (E_mble : MeasurableSet E) (δ : ℝ) : μ E ≤ ∫⁻ x, (thickenedIndicatorAux δ E x : ℝ≥0∞) ∂μ := by
  convert_to lintegral μ (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator E_mble]
    simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  · apply lintegral_mono
    apply indicator_le_thickenedIndicatorAux

theorem measure_le_lintegral_thickenedIndicator (μ : Measure X) {E : Set X}
    (E_mble : MeasurableSet E) {δ : ℝ} (δ_pos : 0 < δ) :
    μ E ≤ ∫⁻ x, (thickenedIndicator δ_pos E x : ℝ≥0∞) ∂μ := by
  convert measure_le_lintegral_thickenedIndicatorAux μ E_mble δ
  dsimp
  simp only [thickenedIndicatorAux_lt_top.ne, ENNReal.coe_toNNReal, Ne, not_false_iff]

end thickenedIndicator

-- We declare a new `{X : Type*}` to discard the instance `[MeasurableSpace X]`
-- which has been in scope for the entire file up to this point.
variable {X : Type*}

section BilinearMap

namespace MeasureTheory

variable {X : Type*} {f : X → ℝ} {m m0 : MeasurableSpace X} {μ : Measure X}

theorem Integrable.simpleFunc_mul (g : SimpleFunc X ℝ) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  refine
    SimpleFunc.induction (fun c s hs => ?_)
      (fun g₁ g₂ _ h_int₁ h_int₂ =>
        (h_int₁.add h_int₂).congr (by rw [SimpleFunc.coe_add, add_mul]))
      g
  simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
  have : Set.indicator s (Function.const X c) * f = s.indicator (c • f) := by
    ext1 x
    by_cases hx : x ∈ s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, Algebra.id.smul_eq_mul,
        ← Function.const_def]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_not_mem, not_false_iff, zero_mul]
  rw [this, integrable_indicator_iff hs]
  exact (hf.smul c).integrableOn

theorem Integrable.simpleFunc_mul' (hm : m ≤ m0) (g : @SimpleFunc X m ℝ) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  rw [← SimpleFunc.coe_toLargerSpace_eq hm g]; exact hf.simpleFunc_mul (g.toLargerSpace hm)

end MeasureTheory

end BilinearMap

section ParametricIntegral

variable {G 𝕜 : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Metric ContinuousLinearMap

/-- The parametric integral over a continuous function on a compact set is continuous,
  under mild assumptions on the topologies involved. -/
theorem continuous_parametric_integral_of_continuous
    [FirstCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopologyEither Y E] [IsLocallyFiniteMeasure μ]
    {f : X → Y → E} (hf : Continuous f.uncurry) {s : Set Y} (hs : IsCompact s) :
    Continuous (∫ y in s, f · y ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases (U_cpct.prod hs).bddAbove_image hf.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [U_nhds] with x x_in
    rw [ae_restrict_iff]
    · filter_upwards with t t_in using hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact integrableOn_const.mpr (Or.inr hs.measure_lt_top)
  · filter_upwards using (by fun_prop)

/-- Consider a parameterized integral `x ↦ ∫ y, L (g y) (f x y)` where `L` is bilinear,
`g` is locally integrable and `f` is continuous and uniformly compactly supported. Then the
integral depends continuously on `x`. -/
lemma continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    [NormedSpace 𝕜 E] (L : F →L[𝕜] G →L[𝕜] E)
    {f : X → Y → G} {s : Set X} {k : Set Y} {g : Y → F}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hfs : ∀ p, ∀ x, p ∈ s → x ∉ k → f p x = 0) (hg : IntegrableOn g k μ) :
    ContinuousOn (fun x ↦ ∫ y, L (g y) (f x y) ∂μ) s := by
  have A : ∀ p ∈ s, Continuous (f p) := fun p hp ↦ by
    refine hf.comp_continuous (continuous_const.prod_mk continuous_id') fun y => ?_
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hp
  intro q hq
  apply Metric.continuousWithinAt_iff'.2 (fun ε εpos ↦ ?_)
  obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ), 0 < δ ∧ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ < ε := by
    simpa [integral_mul_right] using exists_pos_mul_lt εpos _
  obtain ⟨v, v_mem, hv⟩ : ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ k, dist (f p x) (f q x) < δ :=
    hk.mem_uniformity_of_prod
      (hf.mono (Set.prod_mono_right (subset_univ k))) hq (dist_mem_uniformity δpos)
  simp_rw [dist_eq_norm] at hv ⊢
  have I : ∀ p ∈ s, IntegrableOn (fun y ↦ L (g y) (f p y)) k μ := by
    intro p hp
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖f p y‖ ≤ C := by
      have : ContinuousOn (f p) k := by
        have : ContinuousOn (fun y ↦ (p, y)) k := by fun_prop
        exact hf.comp this (by simp [MapsTo, hp])
      rcases IsCompact.exists_bound_of_continuousOn hk this with ⟨C, hC⟩
      refine ⟨max C 0, fun y ↦ ?_⟩
      by_cases hx : y ∈ k
      · exact (hC y hx).trans (le_max_left _ _)
      · simp [hfs p y hp hx]
    have : IntegrableOn (fun y ↦ ‖L‖ * ‖g y‖ * C) k μ :=
      (hg.norm.const_mul _).mul_const _
    apply Integrable.mono' this ?_ ?_
    · borelize G
      apply L.aestronglyMeasurable_comp₂ hg.aestronglyMeasurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply Continuous.stronglyMeasurable_of_support_subset_isCompact (A p hp) hk
      apply support_subset_iff'.2 (fun y hy ↦ hfs p y hp hy)
    · apply Eventually.of_forall (fun y ↦ (le_opNorm₂ L (g y) (f p y)).trans ?_)
      gcongr
      apply hC
  filter_upwards [v_mem, self_mem_nhdsWithin] with p hp h'p
  calc
  ‖∫ x, L (g x) (f p x) ∂μ - ∫ x, L (g x) (f q x) ∂μ‖
    = ‖∫ x in k, L (g x) (f p x) ∂μ - ∫ x in k, L (g x) (f q x) ∂μ‖ := by
      congr 2
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
        simp [hfs p y h'p hy]
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
        simp [hfs q y hq hy]
  _ = ‖∫ x in k, L (g x) (f p x) - L (g x) (f q x) ∂μ‖ := by rw [integral_sub (I p h'p) (I q hq)]
  _ ≤ ∫ x in k, ‖L (g x) (f p x) - L (g x) (f q x)‖ ∂μ := norm_integral_le_integral_norm _
  _ ≤ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y ↦ by positivity))
      · exact (hg.norm.const_mul _).mul_const _
      · filter_upwards with y
        by_cases hy : y ∈ k
        · dsimp only
          specialize hv p hp y hy
          calc
          ‖L (g y) (f p y) - L (g y) (f q y)‖
            = ‖L (g y) (f p y - f q y)‖ := by simp only [map_sub]
          _ ≤ ‖L‖ * ‖g y‖ * ‖f p y - f q y‖ := le_opNorm₂ _ _ _
          _ ≤ ‖L‖ * ‖g y‖ * δ := by gcongr
        · simp only [hfs p y h'p hy, hfs q y hq hy, sub_self, norm_zero, mul_zero]
          positivity
  _ < ε := hδ

/-- Consider a parameterized integral `x ↦ ∫ y, f x y` where `f` is continuous and uniformly
compactly supported. Then the integral depends continuously on `x`. -/
lemma continuousOn_integral_of_compact_support
    {f : X → Y → E} {s : Set X} {k : Set Y} [IsFiniteMeasureOnCompacts μ]
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hfs : ∀ p, ∀ x, p ∈ s → x ∉ k → f p x = 0) :
    ContinuousOn (fun x ↦ ∫ y, f x y ∂μ) s := by
  simpa using continuousOn_integral_bilinear_of_locally_integrable_of_compact_support (lsmul ℝ ℝ)
    hk hf hfs (integrableOn_const.2 (Or.inr hk.measure_lt_top)) (μ := μ) (g := fun _ ↦ 1)

end ParametricIntegral
