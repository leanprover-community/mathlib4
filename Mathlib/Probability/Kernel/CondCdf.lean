/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Constructions.Prod.Basic

#align_import probability.kernel.cond_cdf from "leanprover-community/mathlib"@"3b88f4005dc2e28d42f974cc1ce838f0dafb39b8"

/-!
# Conditional cumulative distribution function

Given `ρ : measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `cond_cdf ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `cond_cdf ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ cond_cdf ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

## Main definitions

* `probability_theory.cond_cdf ρ : α → stieltjes_function`: the conditional cdf of
  `ρ : measure (α × ℝ)`. A `stieltjes_function` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `probability_theory.set_lintegral_cond_cdf`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

## References

The construction of the conditional cdf in this file follows the proof of Theorem 3.4 in
[O. Kallenberg, Foundations of modern probability][kallenberg2021].

## TODO

* The conditional cdf can be used to define the cdf of a real measure by using the
  conditional cdf of `(measure.dirac unit.star).prod μ : measure (unit × ℝ)`.

-/


open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

section AuxLemmasToBeMoved

variable {α β ι : Type*}

theorem Real.iUnion_Iic_rat : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
  ext1 x
  simp only [mem_iUnion, mem_Iic, mem_univ, iff_true_iff]
  obtain ⟨r, hr⟩ := exists_rat_gt x
  exact ⟨r, hr.le⟩
#align real.Union_Iic_rat Real.iUnion_Iic_rat

theorem Real.iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  ext1 x
  simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false_iff, not_forall, not_le]
  exact exists_rat_lt x
#align real.Inter_Iic_rat Real.iInter_Iic_rat

-- todo after the port: move to order/filter/at_top_bot
theorem atBot_le_nhds_bot {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderBot α]
    [OrderTopology α] : (atBot : Filter α) ≤ 𝓝 ⊥ := by
  cases subsingleton_or_nontrivial α
  · simp only [nhds_discrete, le_pure_iff, mem_atBot_sets, mem_singleton_iff,
      eq_iff_true_of_subsingleton, imp_true_iff, exists_const]
  have h : atBot.HasBasis (fun _ : α => True) Iic := @atBot_basis α _ _
  have h_nhds : (𝓝 ⊥).HasBasis (fun a : α => ⊥ < a) fun a => Iio a := @nhds_bot_basis α _ _ _ _ _
  intro s
  rw [h.mem_iff, h_nhds.mem_iff]
  rintro ⟨a, ha_bot_lt, h_Iio_a_subset_s⟩
  refine' ⟨⊥, trivial, _root_.trans _ h_Iio_a_subset_s⟩
  simpa only [Iic_bot, singleton_subset_iff, mem_Iio]
#align at_bot_le_nhds_bot atBot_le_nhds_bot

-- todo after the port: move to order/filter/at_top_bot
theorem atTop_le_nhds_top {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTop α]
    [OrderTopology α] : (atTop : Filter α) ≤ 𝓝 ⊤ :=
  @atBot_le_nhds_bot αᵒᵈ _ _ _ _
#align at_top_le_nhds_top atTop_le_nhds_top

-- todo: move to measure_theory/measurable_space
/-- Monotone convergence for an infimum over a directed family and indexed by a countable type -/
theorem lintegral_iInf_directed_of_measurable {mα : MeasurableSpace α} [Countable β]
    {f : β → α → ℝ≥0∞} {μ : Measure α} (hμ : μ ≠ 0) (hf : ∀ b, Measurable (f b))
    (hf_int : ∀ b, ∫⁻ a, f b a ∂μ ≠ ∞) (h_directed : Directed (· ≥ ·) f) :
    ∫⁻ a, ⨅ b, f b a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · -- Porting note: the next `simp only` doesn't do anything, so added a workaround below.
    -- simp only [WithTop.iInf_empty, lintegral_const]
    conv =>
      lhs
      congr
      · skip
      · ext x
        rw [WithTop.iInf_empty]
    rw [WithTop.iInf_empty, lintegral_const]
    rw [ENNReal.top_mul', if_neg]
    simp only [Measure.measure_univ_eq_zero, hμ, not_false_iff]
  inhabit β
  have : ∀ a, ⨅ b, f b a = ⨅ n, f (h_directed.sequence f n) a := by
    refine' fun a =>
      le_antisymm (le_iInf fun n => iInf_le _ _)
        (le_iInf fun b => iInf_le_of_le (Encodable.encode b + 1) _)
    exact h_directed.sequence_le b a
  -- Porting note: used `∘` below to deal with its reduced reducibility
  calc
    ∫⁻ a, ⨅ b, f b a ∂μ
    _ = ∫⁻ a, ⨅ n, (f ∘ h_directed.sequence f) n a ∂μ := by simp only [this, Function.comp_apply]
    _ = ⨅ n, ∫⁻ a, (f ∘ h_directed.sequence f) n a ∂μ := by
      rw [lintegral_iInf ?_ h_directed.sequence_anti]
      · exact hf_int _
      · exact (fun n => hf _)
    _ = ⨅ b, ∫⁻ a, f b a ∂μ := by
      refine' le_antisymm (le_iInf fun b => _) (le_iInf fun n => _)
      · exact iInf_le_of_le (Encodable.encode b + 1) (lintegral_mono <| h_directed.sequence_le b)
      · exact iInf_le (fun b => ∫⁻ a, f b a ∂μ) _
#align lintegral_infi_directed_of_measurable lintegral_iInf_directed_of_measurable

end AuxLemmasToBeMoved

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × ℝ))

/-- Measure on `α` such that for a measurable set `s`, `ρ.Iic_snd r s = ρ (s ×ˢ Iic r)`. -/
noncomputable def IicSnd (r : ℝ) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst
#align measure_theory.measure.Iic_snd MeasureTheory.Measure.IicSnd

theorem IicSnd_apply (r : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd, fst_apply hs,
    restrict_apply' (MeasurableSet.univ.prod (measurableSet_Iic : MeasurableSet (Iic r))), ←
    prod_univ, prod_inter_prod, inter_univ, univ_inter]
#align measure_theory.measure.Iic_snd_apply MeasureTheory.Measure.IicSnd_apply

theorem IicSnd_univ (r : ℝ) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ
#align measure_theory.measure.Iic_snd_univ MeasureTheory.Measure.IicSnd_univ

theorem IicSnd_mono {r r' : ℝ} (h_le : r ≤ r') : ρ.IicSnd r ≤ ρ.IicSnd r' := by
  intro s hs
  simp_rw [IicSnd_apply ρ _ hs]
  refine' measure_mono (prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr _⟩))
  exact mod_cast h_le
#align measure_theory.measure.Iic_snd_mono MeasureTheory.Measure.IicSnd_mono

theorem IicSnd_le_fst (r : ℝ) : ρ.IicSnd r ≤ ρ.fst := by
  intro s hs
  simp_rw [fst_apply hs, IicSnd_apply ρ r hs]
  exact measure_mono (prod_subset_preimage_fst _ _)
#align measure_theory.measure.Iic_snd_le_fst MeasureTheory.Measure.IicSnd_le_fst

theorem IicSnd_ac_fst (r : ℝ) : ρ.IicSnd r ≪ ρ.fst :=
  Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)
#align measure_theory.measure.Iic_snd_ac_fst MeasureTheory.Measure.IicSnd_ac_fst

theorem IsFiniteMeasure.IicSnd {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ] (r : ℝ) :
    IsFiniteMeasure (ρ.IicSnd r) :=
  isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)
#align measure_theory.measure.is_finite_measure.Iic_snd MeasureTheory.Measure.IsFiniteMeasure.IicSnd

theorem iInf_IicSnd_gt (t : ℚ) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ] :
    ⨅ r : { r' : ℚ // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s := by
  simp_rw [ρ.IicSnd_apply _ hs]
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with x : 1
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    refine' ⟨fun h => _, fun h a hta => h.trans _⟩
    · refine' le_of_forall_lt_rat_imp_le fun q htq => h q _
      exact mod_cast htq
    · exact mod_cast hta.le
  · exact fun _ => hs.prod measurableSet_Iic
  · refine' Monotone.directed_ge fun r r' hrr' => prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, _⟩)
    refine' Iic_subset_Iic.mpr _
    exact mod_cast hrr'
  · exact ⟨⟨t + 1, lt_add_one _⟩, measure_ne_top ρ _⟩
#align measure_theory.measure.infi_Iic_snd_gt MeasureTheory.Measure.iInf_IicSnd_gt

theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ => ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  refine' tendsto_measure_iUnion fun r q hr_le_q x => _
  simp only [mem_prod, mem_Iic, and_imp]
  refine' fun hxs hxr => ⟨hxs, hxr.trans _⟩
  exact mod_cast hr_le_q
#align measure_theory.measure.tendsto_Iic_snd_at_top MeasureTheory.Measure.tendsto_IicSnd_atTop

theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ => ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty, ← Real.iInter_Iic_rat, prod_iInter]
  suffices h_neg :
    Tendsto (fun r : ℚ => ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic ↑(-r))))
  · have h_inter_eq : ⋂ r : ℚ, s ×ˢ Iic ↑(-r) = ⋂ r : ℚ, s ×ˢ Iic (r : ℝ) := by
      ext1 x
      simp only [Rat.cast_eq_id, id.def, mem_iInter, mem_prod, mem_Iic]
      refine' ⟨fun h i => ⟨(h i).1, _⟩, fun h i => ⟨(h i).1, _⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    have h_fun_eq : (fun r : ℚ => ρ (s ×ˢ Iic (r : ℝ))) = fun r : ℚ => ρ (s ×ˢ Iic ↑(- -r)) := by
      simp_rw [neg_neg]
    rw [h_fun_eq]
    exact h_neg.comp tendsto_neg_atBot_atTop
  refine' tendsto_measure_iInter (fun q => hs.prod measurableSet_Iic) _ ⟨0, measure_ne_top ρ _⟩
  refine' fun q r hqr => prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, fun x hx => _⟩)
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  refine' hx.trans (neg_le_neg _)
  exact mod_cast hqr
#align measure_theory.measure.tendsto_Iic_snd_at_bot MeasureTheory.Measure.tendsto_IicSnd_atBot

end MeasureTheory.Measure

open MeasureTheory

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α}

attribute [local instance] MeasureTheory.Measure.IsFiniteMeasure.IicSnd

/-! ### Auxiliary definitions

We build towards the definition of `probability_theory.cond_cdf`. We first define
`probability_theory.pre_cdf`, a function defined on `α × ℚ` with the properties of a cdf almost
everywhere. We then introduce `probability_theory.cond_cdf_rat`, a function on `α × ℚ` which has
the properties of a cdf for all `a : α`. We finally extend to `ℝ`. -/


/-- `pre_cdf` is the Radon-Nikodym derivative of `ρ.IicSnd` with respect to `ρ.fst` at each
`r : ℚ`. This function `ℚ → α → ℝ≥0∞` is such that for almost all `a : α`, the function `ℚ → ℝ≥0∞`
satisfies the properties of a cdf (monotone with limit 0 at -∞ and 1 at +∞, right-continuous).

We define this function on `ℚ` and not `ℝ` because `ℚ` is countable, which allows us to prove
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (preCDF q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (preCDF q a)`. -/
noncomputable def preCDF (ρ : Measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst
#align probability_theory.pre_cdf ProbabilityTheory.preCDF

theorem measurable_preCDF {ρ : Measure (α × ℝ)} {r : ℚ} : Measurable (preCDF ρ r) :=
  Measure.measurable_rnDeriv _ _
#align probability_theory.measurable_pre_cdf ProbabilityTheory.measurable_preCDF

theorem withDensity_preCDF (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)
#align probability_theory.with_density_pre_cdf ProbabilityTheory.withDensity_preCDF

theorem set_lintegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] : ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  have : ∀ r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, eq_self_iff_true, forall_const]
  rw [this, ← set_lintegral_withDensity_eq_set_lintegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter]
  · rw [(_ : (1 : α → ℝ≥0∞) = fun _ => 1)]
    exacts [measurable_const, rfl]
#align probability_theory.set_lintegral_pre_cdf_fst ProbabilityTheory.set_lintegral_preCDF_fst

theorem monotone_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r => preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine' fun r r' hrr' =>
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCDF measurable_preCDF
      fun s hs _ => _
  rw [set_lintegral_preCDF_fst ρ r hs, set_lintegral_preCDF_fst ρ r' hs]
  refine' Measure.IicSnd_mono ρ _ s hs
  exact mod_cast hrr'
#align probability_theory.monotone_pre_cdf ProbabilityTheory.monotone_preCDF

theorem set_lintegral_iInf_gt_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (t : ℚ) {s : Set α}
    (hs : MeasurableSet s) : ∫⁻ x in s, ⨅ r : Ioi t, preCDF ρ r x ∂ρ.fst = ρ.IicSnd t s := by
  refine' le_antisymm _ _
  · have h : ∀ q : Ioi t, ∫⁻ x in s, ⨅ r : Ioi t, preCDF ρ r x ∂ρ.fst ≤ ρ.IicSnd q s := by
      intro q
      rw [← set_lintegral_preCDF_fst ρ _ hs]
      refine' set_lintegral_mono_ae _ measurable_preCDF _
      · exact measurable_iInf fun _ => measurable_preCDF
      · filter_upwards [monotone_preCDF _] with a _
        exact fun _ => iInf_le _ q
    calc
      ∫⁻ x in s, ⨅ r : Ioi t, preCDF ρ r x ∂ρ.fst ≤ ⨅ q : Ioi t, ρ.IicSnd q s := le_iInf h
      _ = ρ.IicSnd t s := Measure.iInf_IicSnd_gt ρ t hs
  · rw [(set_lintegral_preCDF_fst ρ t hs).symm]
    refine' set_lintegral_mono_ae measurable_preCDF _ _
    · exact measurable_iInf fun _ => measurable_preCDF
    · filter_upwards [monotone_preCDF _] with a ha_mono
      exact fun _ => le_iInf fun r => ha_mono (le_of_lt r.prop)
#align probability_theory.set_lintegral_infi_gt_pre_cdf ProbabilityTheory.set_lintegral_iInf_gt_preCDF

theorem preCDF_le_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCDF ρ r a ≤ 1 := by
  rw [ae_all_iff]
  refine' fun r =>
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCDF measurable_const
      fun s hs _ => _
  rw [set_lintegral_preCDF_fst ρ r hs]
  simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s hs
#align probability_theory.pre_cdf_le_one ProbabilityTheory.preCDF_le_one

theorem tendsto_lintegral_preCDF_atTop (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    Tendsto (fun r => ∫⁻ a, preCDF ρ r a ∂ρ.fst) atTop (𝓝 (ρ univ)) := by
  convert ρ.tendsto_IicSnd_atTop MeasurableSet.univ
  · rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ _ MeasurableSet.univ]
  · exact Measure.fst_univ.symm
#align probability_theory.tendsto_lintegral_pre_cdf_at_top ProbabilityTheory.tendsto_lintegral_preCDF_atTop

theorem tendsto_lintegral_preCDF_atBot (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    Tendsto (fun r => ∫⁻ a, preCDF ρ r a ∂ρ.fst) atBot (𝓝 0) := by
  convert ρ.tendsto_IicSnd_atBot MeasurableSet.univ
  rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ _ MeasurableSet.univ]
#align probability_theory.tendsto_lintegral_pre_cdf_at_bot ProbabilityTheory.tendsto_lintegral_preCDF_atBot

theorem tendsto_preCDF_atTop_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCDF ρ r a) atTop (𝓝 1) := by
  -- We show first that `preCDF` has a limit almost everywhere. That limit has to be at most 1.
  -- We then show that the integral of `preCDF` tends to the integral of 1, and that it also tends
  -- to the integral of the limit. Since the limit is at most 1 and has same integral as 1, it is
  -- equal to 1 a.e.
  have h_mono := monotone_preCDF ρ
  have h_le_one := preCDF_le_one ρ
  -- `preCDF` has a limit a.e.
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, Tendsto (fun r => preCDF ρ r a) atTop (𝓝 l) := by
    filter_upwards [h_mono, h_le_one] with a ha_mono ha_le_one
    have h_tendsto :
      Tendsto (fun r => preCDF ρ r a) atTop atTop ∨
        ∃ l, Tendsto (fun r => preCDF ρ r a) atTop (𝓝 l) :=
      tendsto_of_monotone ha_mono
    cases' h_tendsto with h_absurd h_tendsto
    · rw [Monotone.tendsto_atTop_atTop_iff ha_mono] at h_absurd
      obtain ⟨r, hr⟩ := h_absurd 2
      exact absurd (hr.trans (ha_le_one r)) ENNReal.one_lt_two.not_le
    · exact h_tendsto
  classical
  -- let `F` be the pointwise limit of `preCDF` where it exists, and 0 elsewhere.
  let F : α → ℝ≥0∞ := fun a =>
    if h : ∃ l, Tendsto (fun r => preCDF ρ r a) atTop (𝓝 l) then h.choose else 0
  have h_tendsto_ℚ : ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCDF ρ r a) atTop (𝓝 (F a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [dif_pos ha]
    exact ha.choose_spec
  have h_tendsto_ℕ : ∀ᵐ a ∂ρ.fst, Tendsto (fun n : ℕ => preCDF ρ n a) atTop (𝓝 (F a)) := by
    filter_upwards [h_tendsto_ℚ] with a ha using ha.comp tendsto_nat_cast_atTop_atTop
  have hF_ae_meas : AEMeasurable F ρ.fst := by
    refine' aemeasurable_of_tendsto_metrizable_ae _ (fun n => _) h_tendsto_ℚ
    exact measurable_preCDF.aemeasurable
  have hF_le_one : ∀ᵐ a ∂ρ.fst, F a ≤ 1 := by
    filter_upwards [h_tendsto_ℚ, h_le_one] with a ha ha_le using le_of_tendsto' ha ha_le
  -- it suffices to show that the limit `F` is 1 a.e.
  suffices ∀ᵐ a ∂ρ.fst, F a = 1 by
    filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq
    rwa [ha_eq] at ha_tendsto
  -- since `F` is at most 1, proving that its integral is the same as the integral of 1 will tell
  -- us that `F` is 1 a.e.
  have h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = ∫⁻ _, 1 ∂ρ.fst := by
    have h_lintegral :
      Tendsto (fun r : ℕ => ∫⁻ a, preCDF ρ r a ∂ρ.fst) atTop (𝓝 (∫⁻ a, F a ∂ρ.fst)) := by
      refine'
        lintegral_tendsto_of_tendsto_of_monotone
          (-- does this exist only for ℕ?
          fun _ => measurable_preCDF.aemeasurable)
          _ h_tendsto_ℕ
      filter_upwards [h_mono] with a ha
      refine' fun n m hnm => ha _
      exact mod_cast hnm
    have h_lintegral' :
      Tendsto (fun r : ℕ => ∫⁻ a, preCDF ρ r a ∂ρ.fst) atTop (𝓝 (∫⁻ _, 1 ∂ρ.fst)) := by
      rw [lintegral_one, Measure.fst_univ]
      exact (tendsto_lintegral_preCDF_atTop ρ).comp tendsto_nat_cast_atTop_atTop
    exact tendsto_nhds_unique h_lintegral h_lintegral'
  have : ∫⁻ a, 1 - F a ∂ρ.fst = 0 := by
    rw [lintegral_sub' hF_ae_meas _ hF_le_one, h_lintegral_eq, tsub_self]
    calc
      ∫⁻ a, F a ∂ρ.fst = ∫⁻ _, 1 ∂ρ.fst := h_lintegral_eq
      _ = ρ.fst univ := lintegral_one
      _ = ρ univ := Measure.fst_univ
      _ ≠ ∞ := measure_ne_top ρ _
  rw [lintegral_eq_zero_iff' (aemeasurable_const.sub hF_ae_meas)] at this
  filter_upwards [this, hF_le_one] with ha h_one_sub_eq_zero h_le_one
  rw [Pi.zero_apply, tsub_eq_zero_iff_le] at h_one_sub_eq_zero
  exact le_antisymm h_le_one h_one_sub_eq_zero
#align probability_theory.tendsto_pre_cdf_at_top_one ProbabilityTheory.tendsto_preCDF_atTop_one

theorem tendsto_preCDF_atBot_zero (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCDF ρ r a) atBot (𝓝 0) := by
  -- We show first that `preCDF` has a limit in ℝ≥0∞ almost everywhere.
  -- We then show that the integral of `pre_cdf` tends to 0, and that it also tends
  -- to the integral of the limit. Since the limit has integral 0, it is equal to 0 a.e.
  suffices ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCDF ρ (-r) a) atTop (𝓝 0) by
    filter_upwards [this] with a ha
    have h_eq_neg : (fun r : ℚ => preCDF ρ r a) = fun r : ℚ => preCDF ρ (- -r) a := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    exact ha.comp tendsto_neg_atBot_atTop
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, Tendsto (fun r => preCDF ρ (-r) a) atTop (𝓝 l) := by
    filter_upwards [monotone_preCDF ρ] with a ha
    have h_anti : Antitone fun r => preCDF ρ (-r) a := fun p q hpq => ha (neg_le_neg hpq)
    have h_tendsto :
      Tendsto (fun r => preCDF ρ (-r) a) atTop atBot ∨
        ∃ l, Tendsto (fun r => preCDF ρ (-r) a) atTop (𝓝 l) :=
      tendsto_of_antitone h_anti
    cases' h_tendsto with h_bot h_tendsto
    · exact ⟨0, Tendsto.mono_right h_bot atBot_le_nhds_bot⟩
    · exact h_tendsto
  classical
  let F : α → ℝ≥0∞ := fun a =>
    if h : ∃ l, Tendsto (fun r => preCDF ρ (-r) a) atTop (𝓝 l) then h.choose else 0
  have h_tendsto : ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCDF ρ (-r) a) atTop (𝓝 (F a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [dif_pos ha]
    exact ha.choose_spec
  suffices h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = 0
  · have hF_ae_meas : AEMeasurable F ρ.fst := by
      refine' aemeasurable_of_tendsto_metrizable_ae _ (fun n => _) h_tendsto
      exact measurable_preCDF.aemeasurable
    rw [lintegral_eq_zero_iff' hF_ae_meas] at h_lintegral_eq
    filter_upwards [h_tendsto, h_lintegral_eq] with a ha_tendsto ha_eq
    rwa [ha_eq] at ha_tendsto
  have h_lintegral :
    Tendsto (fun r => ∫⁻ a, preCDF ρ (-r) a ∂ρ.fst) atTop (𝓝 (∫⁻ a, F a ∂ρ.fst)) := by
    refine'
      tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
        (eventually_of_forall fun _ => measurable_preCDF) (eventually_of_forall fun _ => _) _
        h_tendsto
    · filter_upwards [preCDF_le_one ρ] with a ha using ha _
    · rw [lintegral_one]
      exact measure_ne_top _ _
  have h_lintegral' : Tendsto (fun r => ∫⁻ a, preCDF ρ (-r) a ∂ρ.fst) atTop (𝓝 0) := by
    have h_lintegral_eq :
      (fun r => ∫⁻ a, preCDF ρ (-r) a ∂ρ.fst) = fun r : ℚ => ρ (univ ×ˢ Iic (-r : ℝ)) := by
      ext1 n
      rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ _ MeasurableSet.univ,
        Measure.IicSnd_univ]
      norm_cast
    rw [h_lintegral_eq]
    have h_zero_eq_measure_iInter : (0 : ℝ≥0∞) = ρ (⋂ r : ℚ, univ ×ˢ Iic (-r : ℝ)) := by
      suffices ⋂ r : ℚ, Iic (-(r : ℝ)) = ∅ by rw [← prod_iInter, this, prod_empty, measure_empty]
      ext1 x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false_iff, not_forall, not_le]
      simp_rw [neg_lt]
      exact exists_rat_gt _
    rw [h_zero_eq_measure_iInter]
    refine'
      tendsto_measure_iInter (fun n => MeasurableSet.univ.prod measurableSet_Iic)
        (fun i j hij x => _) ⟨0, measure_ne_top ρ _⟩
    simp only [mem_prod, mem_univ, mem_Iic, true_and_iff]
    refine' fun hxj => hxj.trans (neg_le_neg _)
    exact mod_cast hij
  exact tendsto_nhds_unique h_lintegral h_lintegral'
#align probability_theory.tendsto_pre_cdf_at_bot_zero ProbabilityTheory.tendsto_preCDF_atBot_zero

theorem inf_gt_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ t : ℚ, ⨅ r : Ioi t, preCDF ρ r a = preCDF ρ t a := by
  rw [ae_all_iff]
  refine' fun t => ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite _ measurable_preCDF _
  · exact measurable_iInf fun i => measurable_preCDF
  intro s hs _
  rw [set_lintegral_iInf_gt_preCDF ρ t hs, set_lintegral_preCDF_fst ρ t hs]
#align probability_theory.inf_gt_pre_cdf ProbabilityTheory.inf_gt_preCDF

section HasCondCDF

/-- A product measure on `α × ℝ` is said to have a conditional cdf at `a : α` if `preCDF` is
monotone with limit 0 at -∞ and 1 at +∞, and is right continuous.
This property holds almost everywhere (see `has_cond_cdf_ae`). -/
structure HasCondCDF (ρ : Measure (α × ℝ)) (a : α) : Prop where
  mono : Monotone fun r => preCDF ρ r a
  le_one : ∀ r, preCDF ρ r a ≤ 1
  tendsto_atTop_one : Tendsto (fun r => preCDF ρ r a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (fun r => preCDF ρ r a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ t : ℚ, ⨅ r : Ioi t, preCDF ρ r a = preCDF ρ t a
#align probability_theory.has_cond_cdf ProbabilityTheory.HasCondCDF

theorem hasCondCDF_ae (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] : ∀ᵐ a ∂ρ.fst, HasCondCDF ρ a := by
  filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ, tendsto_preCDF_atTop_one ρ,
    tendsto_preCDF_atBot_zero ρ, inf_gt_preCDF ρ] with a h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩
#align probability_theory.has_cond_cdf_ae ProbabilityTheory.hasCondCDF_ae

/-- A measurable set of elements of `α` such that `ρ` has a conditional cdf at all
`a ∈ condCDFSet`. -/
def condCDFSet (ρ : Measure (α × ℝ)) : Set α :=
  (toMeasurable ρ.fst {b | ¬HasCondCDF ρ b})ᶜ
#align probability_theory.cond_cdf_set ProbabilityTheory.condCDFSet

theorem measurableSet_condCDFSet (ρ : Measure (α × ℝ)) : MeasurableSet (condCDFSet ρ) :=
  (measurableSet_toMeasurable _ _).compl
#align probability_theory.measurable_set_cond_cdf_set ProbabilityTheory.measurableSet_condCDFSet

theorem hasCondCDF_of_mem_condCDFSet {ρ : Measure (α × ℝ)} {a : α} (h : a ∈ condCDFSet ρ) :
    HasCondCDF ρ a := by
  rw [condCDFSet, mem_compl_iff] at h
  have h_ss := subset_toMeasurable ρ.fst {b | ¬HasCondCDF ρ b}
  by_contra ha
  exact h (h_ss ha)
#align probability_theory.has_cond_cdf_of_mem_cond_cdf_set ProbabilityTheory.hasCondCDF_of_mem_condCDFSet

theorem mem_condCDFSet_ae (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, a ∈ condCDFSet ρ := by
  simp_rw [ae_iff, condCDFSet, not_mem_compl_iff, setOf_mem_eq, measure_toMeasurable]
  exact hasCondCDF_ae ρ
#align probability_theory.mem_cond_cdf_set_ae ProbabilityTheory.mem_condCDFSet_ae

end HasCondCDF

open scoped Classical

/-- Conditional cdf of the measure given the value on `α`, restricted to the rationals.
It is defined to be `pre_cdf` if `a ∈ condCDFSet`, and a default cdf-like function
otherwise. This is an auxiliary definition used to define `cond_cdf`. -/
noncomputable def condCDFRat (ρ : Measure (α × ℝ)) : α → ℚ → ℝ := fun a =>
  if a ∈ condCDFSet ρ then fun r => (preCDF ρ r a).toReal else fun r => if r < 0 then 0 else 1
#align probability_theory.cond_cdf_rat ProbabilityTheory.condCDFRat

theorem condCDFRat_of_not_mem (ρ : Measure (α × ℝ)) (a : α) (h : a ∉ condCDFSet ρ) {r : ℚ} :
    condCDFRat ρ a r = if r < 0 then 0 else 1 := by simp only [condCDFRat, h, if_false]
#align probability_theory.cond_cdf_rat_of_not_mem ProbabilityTheory.condCDFRat_of_not_mem

theorem condCDFRat_of_mem (ρ : Measure (α × ℝ)) (a : α) (h : a ∈ condCDFSet ρ) (r : ℚ) :
    condCDFRat ρ a r = (preCDF ρ r a).toReal := by simp only [condCDFRat, h, if_true]
#align probability_theory.cond_cdf_rat_of_mem ProbabilityTheory.condCDFRat_of_mem

theorem monotone_condCDFRat (ρ : Measure (α × ℝ)) (a : α) : Monotone (condCDFRat ρ a) := by
  by_cases h : a ∈ condCDFSet ρ
  · simp only [condCDFRat, h, if_true, forall_const, and_self_iff]
    intro r r' hrr'
    have h' := hasCondCDF_of_mem_condCDFSet h
    have h_ne_top : ∀ r, preCDF ρ r a ≠ ∞ := fun r =>
      ((h'.le_one r).trans_lt ENNReal.one_lt_top).ne
    rw [ENNReal.toReal_le_toReal (h_ne_top _) (h_ne_top _)]
    exact h'.1 hrr'
  · simp only [condCDFRat, h, if_false]
    intro x y hxy
    dsimp only
    split_ifs with h_1 h_2 h_2
    exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]
#align probability_theory.monotone_cond_cdf_rat ProbabilityTheory.monotone_condCDFRat

theorem measurable_condCDFRat (ρ : Measure (α × ℝ)) (q : ℚ) :
    Measurable fun a => condCDFRat ρ a q := by
  simp_rw [condCDFRat, ite_apply]
  exact
    Measurable.ite (measurableSet_condCDFSet ρ) measurable_preCDF.ennreal_toReal
      measurable_const
#align probability_theory.measurable_cond_cdf_rat ProbabilityTheory.measurable_condCDFRat

theorem condCDFRat_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) : 0 ≤ condCDFRat ρ a r := by
  -- Porting note: was
  -- unfold condCDFRat; split_ifs; exacts [ENNReal.toReal_nonneg, le_rfl, zero_le_one]
  unfold condCDFRat; split_ifs
  · exact ENNReal.toReal_nonneg
  dsimp only
  split_ifs
  exacts [le_rfl, zero_le_one]
#align probability_theory.cond_cdf_rat_nonneg ProbabilityTheory.condCDFRat_nonneg

theorem condCDFRat_le_one (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) : condCDFRat ρ a r ≤ 1 := by
  unfold condCDFRat
  split_ifs with h
  · refine' ENNReal.toReal_le_of_le_ofReal zero_le_one _
    rw [ENNReal.ofReal_one]
    exact (hasCondCDF_of_mem_condCDFSet h).le_one r
  -- Porting note: added
  dsimp only; split_ifs
  exacts [zero_le_one, le_rfl]
#align probability_theory.cond_cdf_rat_le_one ProbabilityTheory.condCDFRat_le_one

theorem tendsto_condCDFRat_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDFRat ρ a) atBot (𝓝 0) := by
  unfold condCDFRat
  split_ifs with h
  · rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff]
    · exact (hasCondCDF_of_mem_condCDFSet h).tendsto_atBot_zero
    · have h' := hasCondCDF_of_mem_condCDFSet h
      exact fun r => ((h'.le_one r).trans_lt ENNReal.one_lt_top).ne
    · exact ENNReal.zero_ne_top
  · refine' (tendsto_congr' _).mp tendsto_const_nhds
    rw [EventuallyEq, eventually_atBot]
    refine' ⟨-1, fun q hq => (if_pos (hq.trans_lt _)).symm⟩
    linarith
#align probability_theory.tendsto_cond_cdf_rat_at_bot ProbabilityTheory.tendsto_condCDFRat_atBot

theorem tendsto_condCDFRat_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDFRat ρ a) atTop (𝓝 1) := by
  unfold condCDFRat
  split_ifs with h
  · have h' := hasCondCDF_of_mem_condCDFSet h
    rw [← ENNReal.one_toReal, ENNReal.tendsto_toReal_iff]
    · exact h'.tendsto_atTop_one
    · exact fun r => ((h'.le_one r).trans_lt ENNReal.one_lt_top).ne
    · exact ENNReal.one_ne_top
  · refine' (tendsto_congr' _).mp tendsto_const_nhds
    rw [EventuallyEq, eventually_atTop]
    exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩
#align probability_theory.tendsto_cond_cdf_rat_at_top ProbabilityTheory.tendsto_condCDFRat_atTop

theorem condCDFRat_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => condCDFRat ρ a r) =ᵐ[ρ.fst] fun a => (preCDF ρ r a).toReal := by
  filter_upwards [mem_condCDFSet_ae ρ] with a ha using condCDFRat_of_mem ρ a ha r
#align probability_theory.cond_cdf_rat_ae_eq ProbabilityTheory.condCDFRat_ae_eq

theorem ofReal_condCDFRat_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => ENNReal.ofReal (condCDFRat ρ a r)) =ᵐ[ρ.fst] preCDF ρ r := by
  filter_upwards [condCDFRat_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha, ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne
#align probability_theory.of_real_cond_cdf_rat_ae_eq ProbabilityTheory.ofReal_condCDFRat_ae_eq

theorem inf_gt_condCDFRat (ρ : Measure (α × ℝ)) (a : α) (t : ℚ) :
    ⨅ r : Ioi t, condCDFRat ρ a r = condCDFRat ρ a t := by
  by_cases ha : a ∈ condCDFSet ρ
  · simp_rw [condCDFRat_of_mem ρ a ha]
    have ha' := hasCondCDF_of_mem_condCDFSet ha
    rw [← ENNReal.toReal_iInf]
    · suffices ⨅ i : ↥(Ioi t), preCDF ρ (↑i) a = preCDF ρ t a by rw [this]
      rw [← ha'.iInf_rat_gt_eq]
    · exact fun r => ((ha'.le_one r).trans_lt ENNReal.one_lt_top).ne
  · simp_rw [condCDFRat_of_not_mem ρ a ha]
    have h_bdd : BddBelow (range fun r : ↥(Ioi t) => ite ((r : ℚ) < 0) (0 : ℝ) 1) := by
      refine' ⟨0, fun x hx => _⟩
      obtain ⟨y, rfl⟩ := mem_range.mpr hx
      dsimp only
      split_ifs
      exacts [le_rfl, zero_le_one]
    split_ifs with h
    · refine' le_antisymm _ (le_ciInf fun x => _)
      · obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0 := by
          refine' ⟨t / 2, _, _⟩
          · linarith
          · linarith
        refine' (ciInf_le h_bdd ⟨q, htq⟩).trans _
        rw [if_pos]
        rwa [Subtype.coe_mk]
      · split_ifs
        exacts [le_rfl, zero_le_one]
    · refine' le_antisymm _ _
      · refine' (ciInf_le h_bdd ⟨t + 1, lt_add_one t⟩).trans _
        split_ifs
        exacts [zero_le_one, le_rfl]
      · refine' le_ciInf fun x => _
        rw [if_neg]
        rw [not_lt] at h ⊢
        exact h.trans (mem_Ioi.mp x.prop).le
#align probability_theory.inf_gt_cond_cdf_rat ProbabilityTheory.inf_gt_condCDFRat

/-- Conditional cdf of the measure given the value on `α`, as a plain function. This is an auxiliary
definition used to define `cond_cdf`. -/
noncomputable irreducible_def condCDF' (ρ : Measure (α × ℝ)) : α → ℝ → ℝ := fun a t =>
  ⨅ r : { r' : ℚ // t < r' }, condCDFRat ρ a r
#align probability_theory.cond_cdf' ProbabilityTheory.condCDF'

theorem condCDF'_def' {ρ : Measure (α × ℝ)} {a : α} {x : ℝ} :
    condCDF' ρ a x = ⨅ r : { r : ℚ // x < r }, condCDFRat ρ a r := by rw [condCDF']
#align probability_theory.cond_cdf'_def ProbabilityTheory.condCDF'_def'

theorem condCDF'_eq_condCDFRat (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) :
    condCDF' ρ a r = condCDFRat ρ a r := by
  rw [← inf_gt_condCDFRat ρ a r, condCDF']
  refine' Equiv.iInf_congr _ _
  · exact
      { toFun := fun t => ⟨t.1, mod_cast t.2⟩
        invFun := fun t => ⟨t.1, mod_cast t.2⟩
        left_inv := fun t => by simp only [Subtype.coe_eta]
        right_inv := fun t => by simp only [Subtype.coe_eta] }
  · intro t
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]
#align probability_theory.cond_cdf'_eq_cond_cdf_rat ProbabilityTheory.condCDF'_eq_condCDFRat

theorem condCDF'_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCDF' ρ a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [condCDF'_def]
  exact le_ciInf fun r' => condCDFRat_nonneg ρ a _
#align probability_theory.cond_cdf'_nonneg ProbabilityTheory.condCDF'_nonneg

theorem bddBelow_range_condCDFRat_gt (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    BddBelow (range fun r : { r' : ℚ // x < ↑r' } => condCDFRat ρ a r) := by
  refine' ⟨0, fun z => _⟩; rintro ⟨u, rfl⟩; exact condCDFRat_nonneg ρ a _
#align probability_theory.bdd_below_range_cond_cdf_rat_gt ProbabilityTheory.bddBelow_range_condCDFRat_gt

theorem monotone_condCDF' (ρ : Measure (α × ℝ)) (a : α) : Monotone (condCDF' ρ a) := by
  intro x y hxy
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [condCDF'_def]
  refine' le_ciInf fun r => (ciInf_le _ _).trans_eq _
  · exact bddBelow_range_condCDFRat_gt ρ a x
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl
#align probability_theory.monotone_cond_cdf' ProbabilityTheory.monotone_condCDF'

theorem continuousWithinAt_condCDF'_Ici (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    ContinuousWithinAt (condCDF' ρ a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert Monotone.tendsto_nhdsWithin_Ioi (monotone_condCDF' ρ a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, condCDF' ρ a r = ⨅ r : { r' : ℚ // x < r' }, condCDF' ρ a r := by
    refine' Real.iInf_Ioi_eq_iInf_rat_gt x _ (monotone_condCDF' ρ a)
    refine' ⟨0, fun z => _⟩
    rintro ⟨u, -, rfl⟩
    exact condCDF'_nonneg ρ a u
  have h'' :
    ⨅ r : { r' : ℚ // x < r' }, condCDF' ρ a r =
      ⨅ r : { r' : ℚ // x < r' }, condCDFRat ρ a r := by
    congr with r
    exact condCDF'_eq_condCDFRat ρ a r
  rw [h', h'', ContinuousWithinAt]
  congr!
  exact condCDF'_def'
#align probability_theory.continuous_within_at_cond_cdf'_Ici ProbabilityTheory.continuousWithinAt_condCDF'_Ici

/-! ### Conditional cdf -/


/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable def condCDF (ρ : Measure (α × ℝ)) (a : α) : StieltjesFunction where
  toFun := condCDF' ρ a
  mono' := monotone_condCDF' ρ a
  right_continuous' x := continuousWithinAt_condCDF'_Ici ρ a x
#align probability_theory.cond_cdf ProbabilityTheory.condCDF

theorem condCDF_eq_condCDFRat (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) :
    condCDF ρ a r = condCDFRat ρ a r :=
  condCDF'_eq_condCDFRat ρ a r
#align probability_theory.cond_cdf_eq_cond_cdf_rat ProbabilityTheory.condCDF_eq_condCDFRat

/-- The conditional cdf is non-negative for all `a : α`. -/
theorem condCDF_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCDF ρ a r :=
  condCDF'_nonneg ρ a r
#align probability_theory.cond_cdf_nonneg ProbabilityTheory.condCDF_nonneg

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
theorem condCDF_le_one (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) : condCDF ρ a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [condCDF_eq_condCDFRat]
  refine' ciInf_le_of_le (bddBelow_range_condCDFRat_gt ρ a x) _ (condCDFRat_le_one _ _ _)
  exact ⟨r, hrx⟩
#align probability_theory.cond_cdf_le_one ProbabilityTheory.condCDF_le_one

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
theorem tendsto_condCDF_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := fun x => exists_rat_btwn (lt_add_one x)
  let qs : ℝ → ℚ := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine' fun q => ⟨q - 1, fun y hy => _⟩
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact mod_cast h_le
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_condCDFRat_atBot ρ a).comp hqs_tendsto) (condCDF_nonneg ρ a) fun x => _
  rw [Function.comp_apply, ← condCDF_eq_condCDFRat]
  exact (condCDF ρ a).mono (h_exists x).choose_spec.1.le
#align probability_theory.tendsto_cond_cdf_at_bot ProbabilityTheory.tendsto_condCDF_atBot

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
theorem tendsto_condCDF_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atTop (𝓝 1) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x - 1 < q ∧ ↑q < x := fun x => exists_rat_btwn (sub_one_lt x)
  let qs : ℝ → ℚ := fun x => (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine' fun q => ⟨q + 1, fun y hy => _⟩
    have h_le : y - 1 ≤ qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le ((tendsto_condCDFRat_atTop ρ a).comp hqs_tendsto)
      tendsto_const_nhds _ (condCDF_le_one ρ a)
  intro x
  rw [Function.comp_apply, ← condCDF_eq_condCDFRat]
  exact (condCDF ρ a).mono (le_of_lt (h_exists x).choose_spec.2)
#align probability_theory.tendsto_cond_cdf_at_top ProbabilityTheory.tendsto_condCDF_atTop

theorem condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => condCDF ρ a r) =ᵐ[ρ.fst] fun a => (preCDF ρ r a).toReal := by
  filter_upwards [mem_condCDFSet_ae ρ] with a ha using
    (condCDF_eq_condCDFRat ρ a r).trans (condCDFRat_of_mem ρ a ha r)
#align probability_theory.cond_cdf_ae_eq ProbabilityTheory.condCDF_ae_eq

theorem ofReal_condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => ENNReal.ofReal (condCDF ρ a r)) =ᵐ[ρ.fst] preCDF ρ r := by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha, ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne
#align probability_theory.of_real_cond_cdf_ae_eq ProbabilityTheory.ofReal_condCDF_ae_eq

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
theorem measurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) : Measurable fun a => condCDF ρ a x := by
  have : (fun a => condCDF ρ a x) = fun a => ⨅ r : { r' : ℚ // x < r' }, condCDFRat ρ a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [condCDF_eq_condCDFRat]
  rw [this]
  exact measurable_iInf (fun q => measurable_condCDFRat ρ q)
#align probability_theory.measurable_cond_cdf ProbabilityTheory.measurable_condCDF

/-- Auxiliary lemma for `set_lintegral_cond_cdf`. -/
theorem set_lintegral_condCDF_rat (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a r) ∂ρ.fst = ρ (s ×ˢ Iic (r : ℝ)) := by
  have : ∀ᵐ a ∂ρ.fst, a ∈ s → ENNReal.ofReal (condCDF ρ a r) = preCDF ρ r a := by
    filter_upwards [ofReal_condCDF_ae_eq ρ r] with a ha using fun _ => ha
  rw [set_lintegral_congr_fun hs this, set_lintegral_preCDF_fst ρ r hs]
  exact ρ.IicSnd_apply r hs
#align probability_theory.set_lintegral_cond_cdf_rat ProbabilityTheory.set_lintegral_condCDF_rat

theorem set_lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_condCDF_rat`. We use the equality
  -- `condCDF ρ a x = ⨅ r : {r' : ℚ // x < r'}, condCDF ρ a r` and a monotone convergence
  -- argument to extend it to the reals.
  by_cases hρ_zero : ρ.fst.restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    refine' le_antisymm (zero_le _) _
    calc
      ρ (s ×ˢ Iic x) ≤ ρ (Prod.fst ⁻¹' s) := measure_mono (prod_subset_preimage_fst s (Iic x))
      _ = ρ.fst s := by rw [Measure.fst_apply hs]
      _ = ρ.fst.restrict s univ := by rw [Measure.restrict_apply_univ]
      _ = 0 := by simp only [hρ_zero, Measure.coe_zero, Pi.zero_apply]
  have h :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst =
      ∫⁻ a in s, ENNReal.ofReal (⨅ r : { r' : ℚ // x < r' }, condCDF ρ a r) ∂ρ.fst := by
    congr with a : 1
    rw [← (condCDF ρ a).iInf_rat_gt_eq x]
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h]
  simp_rw [ENNReal.ofReal_cinfi]
  have h_coe : ∀ b : { r' : ℚ // x < ↑r' }, (b : ℝ) = ((b : ℚ) : ℝ) := fun _ => by congr
  rw [lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } =>
      (measurable_condCDF ρ q).ennreal_ofReal]
  rotate_left
  · intro b
    rw [set_lintegral_condCDF_rat ρ _ hs]
    exact measure_ne_top ρ _
  · refine' Monotone.directed_ge fun i j hij a => ENNReal.ofReal_le_ofReal ((condCDF ρ a).mono _)
    rw [h_coe, h_coe]
    exact mod_cast hij
  simp_rw [set_lintegral_condCDF_rat ρ _ hs]
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq => hyx.trans hq.le⟩
  · exact fun i => hs.prod measurableSet_Iic
  · refine' Monotone.directed_ge fun i j hij => _
    refine' prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr _⟩)
    exact mod_cast hij
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩
#align probability_theory.set_lintegral_cond_cdf ProbabilityTheory.set_lintegral_condCDF

theorem lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) := by
  rw [← set_lintegral_univ, set_lintegral_condCDF ρ _ MeasurableSet.univ]
#align probability_theory.lintegral_cond_cdf ProbabilityTheory.lintegral_condCDF

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) :
    StronglyMeasurable fun a => condCDF ρ a x :=
  (measurable_condCDF ρ x).stronglyMeasurable
#align probability_theory.strongly_measurable_cond_cdf ProbabilityTheory.stronglyMeasurable_condCDF

theorem integrable_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a => condCDF ρ a x) ρ.fst := by
  refine' integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) _ fun t _ _ => _
  · exact (stronglyMeasurable_condCDF ρ _).aestronglyMeasurable
  · have : ∀ y, (‖condCDF ρ y x‖₊ : ℝ≥0∞) ≤ 1 := by
      intro y
      rw [Real.nnnorm_of_nonneg (condCDF_nonneg _ _ _)]
      -- Porting note: was exact_mod_cast condCDF_le_one _ _ _
      simp only [ENNReal.coe_le_one_iff]
      exact condCDF_le_one _ _ _
    refine'
      (set_lintegral_mono (measurable_condCDF _ _).ennnorm measurable_one fun y _ => this y).trans
        _
    simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
    exact measure_mono (subset_univ _)
#align probability_theory.integrable_cond_cdf ProbabilityTheory.integrable_condCDF

theorem set_integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = (ρ (s ×ˢ Iic x)).toReal := by
  have h := set_lintegral_condCDF ρ x hs
  rw [← ofReal_integral_eq_lintegral_ofReal] at h
  · rw [← h, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ => condCDF_nonneg _ _ _
  · exact (integrable_condCDF _ _).integrableOn
  · exact eventually_of_forall fun _ => condCDF_nonneg _ _ _
#align probability_theory.set_integral_cond_cdf ProbabilityTheory.set_integral_condCDF

theorem integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = (ρ (univ ×ˢ Iic x)).toReal := by
  rw [← set_integral_condCDF ρ _ MeasurableSet.univ, Measure.restrict_univ]
#align probability_theory.integral_cond_cdf ProbabilityTheory.integral_condCDF

section Measure

theorem measure_condCDF_Iic (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    (condCDF ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x) := by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _
#align probability_theory.measure_cond_cdf_Iic ProbabilityTheory.measure_condCDF_Iic

theorem measure_condCDF_univ (ρ : Measure (α × ℝ)) (a : α) : (condCDF ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)
#align probability_theory.measure_cond_cdf_univ ProbabilityTheory.measure_condCDF_univ

instance instIsProbabilityMeasure (ρ : Measure (α × ℝ)) (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  ⟨measure_condCDF_univ ρ a⟩

/-- The function `a ↦ (condCDF ρ a).measure` is measurable. -/
theorem measurable_measure_condCDF (ρ : Measure (α × ℝ)) :
    Measurable fun a => (condCDF ρ a).measure := by
  rw [Measure.measurable_measure]
  refine' fun s hs => ?_
  -- Porting note: supplied `C`
  refine' MeasurableSpace.induction_on_inter
    (C := fun s => Measurable fun b ↦ StieltjesFunction.measure (condCDF ρ b) s)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ hs
  · simp only [measure_empty, measurable_const]
  · rintro S ⟨u, rfl⟩
    simp_rw [measure_condCDF_Iic ρ _ u]
    exact (measurable_condCDF ρ u).ennreal_ofReal
  · intro t ht ht_cd_meas
    have :
      (fun a => (condCDF ρ a).measure tᶜ) =
        (fun a => (condCDF ρ a).measure univ) - fun a => (condCDF ρ a).measure t := by
      ext1 a
      rw [measure_compl ht (measure_ne_top (condCDF ρ a).measure _), Pi.sub_apply]
    simp_rw [this, measure_condCDF_univ ρ]
    exact Measurable.sub measurable_const ht_cd_meas
  · intro f hf_disj hf_meas hf_cd_meas
    simp_rw [measure_iUnion hf_disj hf_meas]
    exact Measurable.ennreal_tsum hf_cd_meas
#align probability_theory.measurable_measure_cond_cdf ProbabilityTheory.measurable_measure_condCDF

end Measure

end ProbabilityTheory
