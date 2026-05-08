/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Order.Filter.Ring

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

This file is about Bochner integrals. See the file `AEEqOfLIntegral` for Lebesgue integrals.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.

The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`: for functions which are
  `AEFinStronglyMeasurable`.
* `Lp.ae_eq_of_forall_setIntegral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `Integrable.ae_eq_of_forall_setIntegral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `(fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the `StrongDual` space,
  `fun x => c (f x) =ᵐ[μ] 0` then `f =ᵐ[μ] 0`.

-/

public section


open MeasureTheory TopologicalSpace NormedSpace Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

section AeEqOfForall

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

open scoped InnerProductSpace in
theorem ae_eq_zero_of_forall_inner [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SecondCountableTopology E] {f : α → E} (hf : ∀ c : E, (fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0) :
    f =ᵐ[μ] 0 := by
  let s := denseSeq E
  have hs : DenseRange s := denseRange_denseSeq E
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪s n, f x⟫_𝕜 = 0 := ae_all_iff.mpr fun n => hf (s n)
  refine hf'.mono fun x hx => ?_
  rw [Pi.zero_apply, ← @inner_self_eq_zero 𝕜]
  have h_closed : IsClosed {c : E | ⟪c, f x⟫_𝕜 = 0} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact @isClosed_property ℕ E _ s (fun c => ⟪c, f x⟫_𝕜 = 0) hs h_closed hx _

local notation "⟪" x ", " y "⟫" => y x

variable (𝕜)

theorem ae_eq_zero_of_forall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {t : Set E} (ht : TopologicalSpace.IsSeparable t) {f : α → E}
    (hf : ∀ c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) (h't : ∀ᵐ x ∂μ, f x ∈ t) :
    f =ᵐ[μ] 0 := by
  rcases ht with ⟨d, d_count, hd⟩
  haveI : Encodable d := d_count.toEncodable
  have : ∀ x : d, ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖(x : E)‖ :=
    fun x => exists_dual_vector'' 𝕜 (x : E)
  choose s hs using this
  have A : ∀ a : E, a ∈ t → (∀ x, ⟪a, s x⟫ = (0 : 𝕜)) → a = 0 := by
    intro a hat ha
    contrapose! ha
    have a_pos : 0 < ‖a‖ := by simp only [ha, norm_pos_iff, Ne, not_false_iff]
    have a_mem : a ∈ closure d := hd hat
    obtain ⟨x, hx⟩ : ∃ x : d, dist a x < ‖a‖ / 2 := by
      rcases Metric.mem_closure_iff.1 a_mem (‖a‖ / 2) (half_pos a_pos) with ⟨x, h'x, hx⟩
      exact ⟨⟨x, h'x⟩, hx⟩
    use x
    have I : ‖a‖ / 2 < ‖(x : E)‖ := by
      have : ‖a‖ ≤ ‖(x : E)‖ + ‖a - x‖ := norm_le_insert' _ _
      have : ‖a - x‖ < ‖a‖ / 2 := by rwa [dist_eq_norm] at hx
      linarith
    intro h
    apply lt_irrefl ‖s x x‖
    calc
      ‖s x x‖ = ‖s x (x - a)‖ := by simp only [h, sub_zero, map_sub]
      _ ≤ 1 * ‖(x : E) - a‖ := ContinuousLinearMap.le_of_opNorm_le _ (hs x).1 _
      _ < ‖a‖ / 2 := by rw [one_mul]; rwa [dist_eq_norm'] at hx
      _ < ‖(x : E)‖ := I
      _ = ‖s x x‖ := by simp [(hs x).2]
  have hfs : ∀ y : d, ∀ᵐ x ∂μ, ⟪f x, s y⟫ = (0 : 𝕜) := fun y => hf (s y)
  have hf' : ∀ᵐ x ∂μ, ∀ y : d, ⟪f x, s y⟫ = (0 : 𝕜) := by rwa [ae_all_iff]
  filter_upwards [hf', h't] with x hx h'x
  exact A (f x) h'x hx

theorem ae_eq_zero_of_forall_dual [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SecondCountableTopology E] {f : α → E}
    (hf : ∀ c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) : f =ᵐ[μ] 0 :=
  ae_eq_zero_of_forall_dual_of_isSeparable 𝕜 (.of_separableSpace Set.univ) hf
    (Eventually.of_forall fun _ => Set.mem_univ _)

end AeEqOfForall

variable {α E : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞}

section AeEqOfForallSetIntegralEq

section Real

variable {f : α → ℝ}

theorem ae_nonneg_of_forall_setIntegral_nonneg (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  simp_rw [EventuallyLE, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := {x | f x ≤ b}
  have hs : NullMeasurableSet s μ := nullMeasurableSet_le hf.1.aemeasurable aemeasurable_const
  have mus : μ s < ∞ := Integrable.measure_le_lt_top hf hb_neg
  have h_int_gt : (∫ x in s, f x ∂μ) ≤ b * μ.real s := by
    have h_const_le : (∫ x in s, f x ∂μ) ≤ ∫ _ in s, b ∂μ := by
      refine setIntegral_mono_ae_restrict hf.integrableOn (integrableOn_const mus.ne) ?_
      rw [EventuallyLE, ae_restrict_iff₀ (hs.mono μ.restrict_le_self)]
      exact Eventually.of_forall fun x hxs => hxs
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at h_const_le
  contrapose! h_int_gt with H
  calc
    b * μ.real s < 0 := mul_neg_of_neg_of_pos hb_neg <| ENNReal.toReal_pos H mus.ne
    _ ≤ ∫ x in s, f x ∂μ := by
      rw [← μ.restrict_toMeasurable mus.ne]
      exact hf_zero _ (measurableSet_toMeasurable ..) (by rwa [measure_toMeasurable])

theorem ae_le_of_forall_setIntegral_le {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_le : ∀ s, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  rw [← eventually_sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg (hg.sub hf) fun s hs => ?_
  rw [integral_sub' hg.integrableOn hf.integrableOn, sub_nonneg]
  exact hf_le s hs

theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α → ℝ} {t : Set α}
    (hf : IntegrableOn f t μ)
    (hf_zero : ∀ s, MeasurableSet s → μ (s ∩ t) < ∞ → 0 ≤ ∫ x in s ∩ t, f x ∂μ) :
    0 ≤ᵐ[μ.restrict t] f := by
  refine ae_nonneg_of_forall_setIntegral_nonneg hf fun s hs h's => ?_
  simp_rw [Measure.restrict_restrict hs]
  apply hf_zero s hs
  rwa [Measure.restrict_apply hs] at h's

theorem ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hf_int_finite t t_meas t_lt_top)
  intro s s_meas _
  exact
    hf_zero _ (s_meas.inter t_meas)
      (lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) t_lt_top)

theorem AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg {f : α → ℝ}
    (hf : AEFinStronglyMeasurable f μ)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  let t := hf.sigmaFiniteSet
  suffices 0 ≤ᵐ[μ.restrict t] f from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  haveI : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμts => ?_) fun s hs hμts => ?_
  · rw [IntegrableOn, Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμts
    exact hf_int_finite (s ∩ t) (hs.inter hf.measurableSet) hμts
  · rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμts
    exact hf_zero (s ∩ t) (hs.inter hf.measurableSet) hμts

theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : 0 ≤ᵐ[μ.restrict t] f := by
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) fun s hs _ => ?_
  refine hf_zero (s ∩ t) (hs.inter ht) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμt)

theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f from
    h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymm hx2 hx1)
  refine
    ⟨?_,
      ae_nonneg_restrict_of_forall_setIntegral_nonneg hf_int_finite
        (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht hμt⟩
  suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f by
    refine h_neg.mono fun x hx => ?_
    rw [Pi.neg_apply] at hx
    simpa using hx
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg (fun s hs hμs => (hf_int_finite s hs hμs).neg)
      (fun s hs hμs => ?_) ht hμt
  simp_rw [Pi.neg_apply]
  rw [integral_neg, neg_nonneg]
  exact (hf_zero s hs hμs).le

end Real

theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  rcases (hf_int_finite t ht hμt.lt_top).aestronglyMeasurable.isSeparable_ae_range with
    ⟨u, u_sep, hu⟩
  refine ae_eq_zero_of_forall_dual_of_isSeparable ℝ u_sep (fun c => ?_) hu
  refine ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real ?_ ?_ ht hμt
  · intro s hs hμs
    exact ContinuousLinearMap.integrable_comp c (hf_int_finite s hs hμs)
  · intro s hs hμs
    rw [ContinuousLinearMap.integral_comp_comm c (hf_int_finite s hs hμs), hf_zero s hs hμs]
    exact map_zero _

theorem ae_eq_restrict_of_forall_setIntegral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hfg_int hfg' ht hμt

theorem ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  let S := spanningSets μ
  rw [← @Measure.restrict_univ _ _ μ, ← iUnion_spanningSets μ, EventuallyEq, ae_iff,
    Measure.restrict_apply' (MeasurableSet.iUnion (measurableSet_spanningSets μ))]
  rw [Set.inter_iUnion, measure_iUnion_null_iff]
  intro n
  have h_meas_n : MeasurableSet (S n) := measurableSet_spanningSets μ n
  have hμn : μ (S n) < ∞ := measure_spanningSets_lt_top μ n
  rw [← Measure.restrict_apply' h_meas_n]
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne

theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hfg_int hfg

theorem AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] 0 := by
  let t := hf.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  haveI : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    rw [IntegrableOn, Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμs
    exact hf_int_finite _ (hs.inter hf.measurableSet) hμs
  · intro s hs hμs
    rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμs
    exact hf_zero _ (hs.inter hf.measurableSet) hμs

theorem AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf : AEFinStronglyMeasurable f μ) (hg : AEFinStronglyMeasurable g μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact (hf.sub hg).ae_eq_zero_of_forall_setIntegral_eq_zero hfg_int hfg

theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero (f : Lp E p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero hf_int_finite hf_zero
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

theorem Lp.ae_eq_of_forall_setIntegral_eq (f g : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hf_int_finite hg_int_finite hfg
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

theorem ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim (hm : m ≤ m0) {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf : FinStronglyMeasurable f (μ.trim hm)) : f =ᵐ[μ] 0 := by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigmaFinite
  haveI : SigmaFinite ((μ.restrict t).trim hm) := by rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0 := by
    rw [EventuallyEq, ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
    exact Eventually.of_forall htf_zero
  have hf_meas_m : StronglyMeasurable[m] f := hf.stronglyMeasurable
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this htf_zero
  refine measure_eq_zero_of_trim_eq_zero hm ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    unfold IntegrableOn
    rw [restrict_trim hm (μ.restrict t) hs, Measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas, Measure.restrict_apply hs,
      trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
    refine Integrable.trim hm ?_ hf_meas_m
    exact hf_int_finite _ (hs.inter ht_meas) hμs
  · intro s hs hμs
    rw [restrict_trim hm (μ.restrict t) hs, Measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas, Measure.restrict_apply hs,
      trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
    rw [← integral_trim hm hf_meas_m]
    exact hf_zero _ (hs.inter ht_meas) hμs

theorem Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α → E} (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  hf.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun _ _ _ => hf.integrableOn) hf_zero

theorem Integrable.ae_eq_of_forall_setIntegral_eq (f g : α → E) (hf : Integrable f μ)
    (hg : Integrable g μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq (fun _ _ _ => hf.integrableOn)
    (fun _ _ _ => hg.integrableOn) hfg hf.aefinStronglyMeasurable hg.aefinStronglyMeasurable

variable {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/-- If an integrable function has zero integral on all closed sets, then it is zero
almost everywhere. -/
lemma ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero {μ : Measure β} {f : β → E}
    (hf : Integrable f μ) (h'f : ∀ (s : Set β), IsClosed s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  suffices ∀ s, MeasurableSet s → ∫ x in s, f x ∂μ = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ ↦ this s hs)
  have A : ∀ (t : Set β), MeasurableSet t → ∫ (x : β) in t, f x ∂μ = 0
      → ∫ (x : β) in tᶜ, f x ∂μ = 0 := by
    intro t t_meas ht
    have I : ∫ x, f x ∂μ = 0 := by rw [← setIntegral_univ]; exact h'f _ isClosed_univ
    simpa [ht, I] using integral_add_compl t_meas hf
  intro s hs
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact compl_compl U ▸ A _ hU.measurableSet.compl (h'f _ hU.isClosed_compl)
  | compl s hs ihs => exact A s hs ihs
  | iUnion g g_disj g_meas hg => simp [integral_iUnion g_meas g_disj hf.integrableOn, hg]

/-- If an integrable function has zero integral on all compact sets in a sigma-compact space, then
it is zero almost everywhere. -/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β → E} (hf : Integrable f μ)
    (h'f : ∀ (s : Set β), IsCompact s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf (fun s hs ↦ ?_)
  let t : ℕ → Set β := fun n ↦ closure (compactCovering β n) ∩ s
  suffices H : Tendsto (fun n ↦ ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) by
    have A : ∀ n, ∫ x in t n, f x ∂μ = 0 :=
      fun n ↦ h'f _ ((isCompact_compactCovering β n).closure.inter_right hs)
    simp_rw [A, tendsto_const_nhds_iff] at H
    exact H.symm
  have B : s = ⋃ n, t n := by
    rw [← Set.iUnion_inter, iUnion_closure_compactCovering, Set.univ_inter]
  rw [B]
  apply tendsto_setIntegral_of_monotone
  · intro n
    exact (isClosed_closure.inter hs).measurableSet
  · intro m n hmn
    simp only [t, Set.le_iff_subset]
    gcongr
  · exact hf.integrableOn

/-- If a locally integrable function has zero integral on all compact sets in a sigma-compact space,
then it is zero almost everywhere. -/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β → E} (hf : LocallyIntegrable f μ)
    (h'f : ∀ (s : Set β), IsCompact s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  rw [← μ.restrict_univ, ← iUnion_closure_compactCovering]
  apply (ae_restrict_iUnion_iff _ _).2 (fun n ↦ ?_)
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  · exact hf.integrableOn_isCompact (isCompact_compactCovering β n).closure
  · intro s hs
    rw [Measure.restrict_restrict' measurableSet_closure]
    exact h'f _ (hs.inter_right isClosed_closure)

end AeEqOfForallSetIntegralEq

end MeasureTheory
