/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Kernel.Composition
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

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

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

section AuxLemmasToBeMoved

variable {α β ι : Type*}

namespace Directed

-- todo after the port: move this to logic.encodable.basic near sequence_mono
variable [Encodable α] [Inhabited α] [Preorder β] {f : α → β} (hf : Directed (· ≥ ·) f)

theorem sequence_anti : Antitone (f ∘ hf.sequence f) :=
  antitone_nat_of_succ_le <| hf.sequence_mono_nat
#align directed.sequence_anti Directed.sequence_anti

theorem sequence_le (a : α) : f (hf.sequence f (Encodable.encode a + 1)) ≤ f a :=
  hf.rel_sequence a
#align directed.sequence_le Directed.sequence_le

end Directed

-- todo: move to data/set/lattice next to prod_Union or prod_sInter
theorem prod_iInter {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (s ×ˢ ⋂ i, t i) = ⋂ i, s ×ˢ t i := by
  ext x
  -- ⊢ x ∈ s ×ˢ ⋂ (i : ι), t i ↔ x ∈ ⋂ (i : ι), s ×ˢ t i
  simp only [mem_prod, mem_iInter]
  -- ⊢ (x.fst ∈ s ∧ ∀ (i : ι), x.snd ∈ t i) ↔ ∀ (i : ι), x.fst ∈ s ∧ x.snd ∈ t i
  exact ⟨fun h i => ⟨h.1, h.2 i⟩, fun h => ⟨(h hι.some).1, fun i => (h i).2⟩⟩
  -- 🎉 no goals
#align prod_Inter prod_iInter

theorem Real.iUnion_Iic_rat : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
  ext1 x
  -- ⊢ x ∈ ⋃ (r : ℚ), Iic ↑r ↔ x ∈ univ
  simp only [mem_iUnion, mem_Iic, mem_univ, iff_true_iff]
  -- ⊢ ∃ i, x ≤ ↑i
  obtain ⟨r, hr⟩ := exists_rat_gt x
  -- ⊢ ∃ i, x ≤ ↑i
  exact ⟨r, hr.le⟩
  -- 🎉 no goals
#align real.Union_Iic_rat Real.iUnion_Iic_rat

theorem Real.iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  ext1 x
  -- ⊢ x ∈ ⋂ (r : ℚ), Iic ↑r ↔ x ∈ ∅
  simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false_iff, not_forall, not_le]
  -- ⊢ ∃ x_1, ↑x_1 < x
  exact exists_rat_lt x
  -- 🎉 no goals
#align real.Inter_Iic_rat Real.iInter_Iic_rat

-- todo after the port: move to order/filter/at_top_bot
theorem atBot_le_nhds_bot {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderBot α]
    [OrderTopology α] : (atBot : Filter α) ≤ 𝓝 ⊥ := by
  cases subsingleton_or_nontrivial α
  -- ⊢ atBot ≤ 𝓝 ⊥
  · simp only [nhds_discrete, le_pure_iff, mem_atBot_sets, mem_singleton_iff,
      eq_iff_true_of_subsingleton, imp_true_iff, exists_const]
  have h : atBot.HasBasis (fun _ : α => True) Iic := @atBot_basis α _ _
  -- ⊢ atBot ≤ 𝓝 ⊥
  have h_nhds : (𝓝 ⊥).HasBasis (fun a : α => ⊥ < a) fun a => Iio a := @nhds_bot_basis α _ _ _ _ _
  -- ⊢ atBot ≤ 𝓝 ⊥
  intro s
  -- ⊢ s ∈ 𝓝 ⊥ → s ∈ atBot
  rw [h.mem_iff, h_nhds.mem_iff]
  -- ⊢ (∃ i, ⊥ < i ∧ Iio i ⊆ s) → ∃ i, True ∧ Iic i ⊆ s
  rintro ⟨a, ha_bot_lt, h_Iio_a_subset_s⟩
  -- ⊢ ∃ i, True ∧ Iic i ⊆ s
  refine' ⟨⊥, trivial, _root_.trans _ h_Iio_a_subset_s⟩
  -- ⊢ Iic ⊥ ⊆ Iio a
  simpa only [Iic_bot, singleton_subset_iff, mem_Iio]
  -- 🎉 no goals
#align at_bot_le_nhds_bot atBot_le_nhds_bot

-- todo after the port: move to order/filter/at_top_bot
theorem atTop_le_nhds_top {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTop α]
    [OrderTopology α] : (atTop : Filter α) ≤ 𝓝 ⊤ :=
  @atBot_le_nhds_bot αᵒᵈ _ _ _ _
#align at_top_le_nhds_top atTop_le_nhds_top

-- todo: move to topology/algebra/order/monotone_convergence
theorem tendsto_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atTop atBot ∨ ∃ l, Tendsto f atTop (𝓝 l) :=
  @tendsto_of_monotone ι αᵒᵈ _ _ _ _ _ h_mono
#align tendsto_of_antitone tendsto_of_antitone

-- todo: move to data/real/ennreal
theorem ENNReal.ofReal_cinfi (f : α → ℝ) [Nonempty α] :
    ENNReal.ofReal (⨅ i, f i) = ⨅ i, ENNReal.ofReal (f i) := by
  by_cases hf : BddBelow (range f)
  -- ⊢ ENNReal.ofReal (⨅ (i : α), f i) = ⨅ (i : α), ENNReal.ofReal (f i)
  · exact
      Monotone.map_ciInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
        (fun i j hij => ENNReal.ofReal_le_ofReal hij) hf
  · symm
    -- ⊢ ⨅ (i : α), ENNReal.ofReal (f i) = ENNReal.ofReal (⨅ (i : α), f i)
    rw [Real.iInf_of_not_bddBelow hf, ENNReal.ofReal_zero, ← ENNReal.bot_eq_zero, iInf_eq_bot]
    -- ⊢ ∀ (b : ℝ≥0∞), b > ⊥ → ∃ i, ENNReal.ofReal (f i) < b
    obtain ⟨y, hy_mem, hy_neg⟩ := not_bddBelow_iff.mp hf 0
    -- ⊢ ∀ (b : ℝ≥0∞), b > ⊥ → ∃ i, ENNReal.ofReal (f i) < b
    obtain ⟨i, rfl⟩ := mem_range.mpr hy_mem
    -- ⊢ ∀ (b : ℝ≥0∞), b > ⊥ → ∃ i, ENNReal.ofReal (f i) < b
    refine' fun x hx => ⟨i, _⟩
    -- ⊢ ENNReal.ofReal (f i) < x
    rwa [ENNReal.ofReal_of_nonpos hy_neg.le]
    -- 🎉 no goals
#align ennreal.of_real_cinfi ENNReal.ofReal_cinfi

-- todo: move to measure_theory/measurable_space
/-- Monotone convergence for an infimum over a directed family and indexed by a countable type -/
theorem lintegral_iInf_directed_of_measurable {mα : MeasurableSpace α} [Countable β]
    {f : β → α → ℝ≥0∞} {μ : Measure α} (hμ : μ ≠ 0) (hf : ∀ b, Measurable (f b))
    (hf_int : ∀ b, ∫⁻ a, f b a ∂μ ≠ ∞) (h_directed : Directed (· ≥ ·) f) :
    ∫⁻ a, ⨅ b, f b a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ := by
  cases nonempty_encodable β
  -- ⊢ ∫⁻ (a : α), ⨅ (b : β), f b a ∂μ = ⨅ (b : β), ∫⁻ (a : α), f b a ∂μ
  cases isEmpty_or_nonempty β
  -- ⊢ ∫⁻ (a : α), ⨅ (b : β), f b a ∂μ = ⨅ (b : β), ∫⁻ (a : α), f b a ∂μ
  · -- Porting note: the next `simp only` doesn't do anything, so added a workaround below.
    -- simp only [WithTop.iInf_empty, lintegral_const]
    conv =>
      lhs
      congr
      · skip
      · ext x
        rw [WithTop.iInf_empty]
    rw [WithTop.iInf_empty, lintegral_const]
    -- ⊢ ⊤ * ↑↑μ univ = ⊤
    rw [ENNReal.top_mul', if_neg]
    -- ⊢ ¬↑↑μ univ = 0
    simp only [Measure.measure_univ_eq_zero, hμ, not_false_iff]
    -- 🎉 no goals
  inhabit β
  -- ⊢ ∫⁻ (a : α), ⨅ (b : β), f b a ∂μ = ⨅ (b : β), ∫⁻ (a : α), f b a ∂μ
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
  -- ⊢ ↑↑(IicSnd ρ r) s ≤ ↑↑(IicSnd ρ r') s
  simp_rw [IicSnd_apply ρ _ hs]
  -- ⊢ ↑↑ρ (s ×ˢ Iic r) ≤ ↑↑ρ (s ×ˢ Iic r')
  refine' measure_mono (prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr _⟩))
  -- ⊢ r ≤ r'
  exact_mod_cast h_le
  -- 🎉 no goals
#align measure_theory.measure.Iic_snd_mono MeasureTheory.Measure.IicSnd_mono

theorem IicSnd_le_fst (r : ℝ) : ρ.IicSnd r ≤ ρ.fst := by
  intro s hs
  -- ⊢ ↑↑(IicSnd ρ r) s ≤ ↑↑(fst ρ) s
  simp_rw [fst_apply hs, IicSnd_apply ρ r hs]
  -- ⊢ ↑↑ρ (s ×ˢ Iic r) ≤ ↑↑ρ (Prod.fst ⁻¹' s)
  exact measure_mono (prod_subset_preimage_fst _ _)
  -- 🎉 no goals
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
  -- ⊢ ⨅ (r : { r' // t < r' }), ↑↑ρ (s ×ˢ Iic ↑↑r) = ↑↑ρ (s ×ˢ Iic ↑t)
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    -- ⊢ ↑↑ρ (s ×ˢ ⋂ (i : { r' // t < r' }), Iic ↑↑i) = ↑↑ρ (s ×ˢ Iic ↑t)
    congr with x : 1
    -- ⊢ x ∈ ⋂ (i : { r' // t < r' }), Iic ↑↑i ↔ x ∈ Iic ↑t
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    -- ⊢ (∀ (a : ℚ), t < a → x ≤ ↑a) ↔ x ≤ ↑t
    refine' ⟨fun h => _, fun h a hta => h.trans _⟩
    -- ⊢ x ≤ ↑t
    · refine' le_of_forall_lt_rat_imp_le fun q htq => h q _
      -- ⊢ t < q
      exact_mod_cast htq
      -- 🎉 no goals
    · exact_mod_cast hta.le
      -- 🎉 no goals
  · exact fun _ => hs.prod measurableSet_Iic
    -- 🎉 no goals
  · refine' Monotone.directed_ge fun r r' hrr' => prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, _⟩)
    -- ⊢ Iic ↑↑r ⊆ Iic ↑↑r'
    refine' Iic_subset_Iic.mpr _
    -- ⊢ ↑↑r ≤ ↑↑r'
    exact_mod_cast hrr'
    -- 🎉 no goals
  · exact ⟨⟨t + 1, lt_add_one _⟩, measure_ne_top ρ _⟩
    -- 🎉 no goals
#align measure_theory.measure.infi_Iic_snd_gt MeasureTheory.Measure.iInf_IicSnd_gt

theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ => ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑r)) atTop (𝓝 (↑↑ρ (s ×ˢ univ)))
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑r)) atTop (𝓝 (↑↑ρ (⋃ (i : ℚ), s ×ˢ Iic ↑i)))
  refine' tendsto_measure_iUnion fun r q hr_le_q x => _
  -- ⊢ x ∈ s ×ˢ Iic ↑r → x ∈ s ×ˢ Iic ↑q
  simp only [mem_prod, mem_Iic, and_imp]
  -- ⊢ x.fst ∈ s → x.snd ≤ ↑r → x.fst ∈ s ∧ x.snd ≤ ↑q
  refine' fun hxs hxr => ⟨hxs, hxr.trans _⟩
  -- ⊢ ↑r ≤ ↑q
  exact_mod_cast hr_le_q
  -- 🎉 no goals
#align measure_theory.measure.tendsto_Iic_snd_at_top MeasureTheory.Measure.tendsto_IicSnd_atTop

theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ => ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑r)) atBot (𝓝 0)
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑r)) atBot (𝓝 0)
  rw [← h_empty, ← Real.iInter_Iic_rat, prod_iInter]
  -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑r)) atBot (𝓝 (↑↑ρ (⋂ (i : ℚ), s ×ˢ Iic ↑i)))
  suffices h_neg :
    Tendsto (fun r : ℚ => ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic ↑(-r))))
  · have h_inter_eq : ⋂ r : ℚ, s ×ˢ Iic ↑(-r) = ⋂ r : ℚ, s ×ˢ Iic (r : ℝ) := by
      ext1 x
      simp only [Rat.cast_eq_id, id.def, mem_iInter, mem_prod, mem_Iic]
      refine' ⟨fun h i => ⟨(h i).1, _⟩, fun h i => ⟨(h i).1, _⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑r)) atBot (𝓝 (↑↑ρ (⋂ (i : ℚ), s ×ˢ Iic ↑i)))
    have h_fun_eq : (fun r : ℚ => ρ (s ×ˢ Iic (r : ℝ))) = fun r : ℚ => ρ (s ×ˢ Iic ↑(- -r)) := by
      simp_rw [neg_neg]
    rw [h_fun_eq]
    -- ⊢ Tendsto (fun r => ↑↑ρ (s ×ˢ Iic ↑(- -r))) atBot (𝓝 (↑↑ρ (⋂ (i : ℚ), s ×ˢ Iic …
    exact h_neg.comp tendsto_neg_atBot_atTop
    -- 🎉 no goals
  refine' tendsto_measure_iInter (fun q => hs.prod measurableSet_Iic) _ ⟨0, measure_ne_top ρ _⟩
  -- ⊢ Antitone fun r => s ×ˢ Iic ↑(-r)
  refine' fun q r hqr => prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, fun x hx => _⟩)
  -- ⊢ x ∈ Iic ↑(-q)
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  -- ⊢ x ≤ -↑q
  refine' hx.trans (neg_le_neg _)
  -- ⊢ ↑q ≤ ↑r
  exact_mod_cast hqr
  -- 🎉 no goals
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
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (pre_cdf q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (pre_cdf q a)`. -/
noncomputable def preCdf (ρ : Measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst
#align probability_theory.pre_cdf ProbabilityTheory.preCdf

theorem measurable_preCdf {ρ : Measure (α × ℝ)} {r : ℚ} : Measurable (preCdf ρ r) :=
  Measure.measurable_rnDeriv _ _
#align probability_theory.measurable_pre_cdf ProbabilityTheory.measurable_preCdf

theorem withDensity_preCdf (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ρ.fst.withDensity (preCdf ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)
#align probability_theory.with_density_pre_cdf ProbabilityTheory.withDensity_preCdf

theorem set_lintegral_preCdf_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] : ∫⁻ x in s, preCdf ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  have : ∀ r, ∫⁻ x in s, preCdf ρ r x ∂ρ.fst = ∫⁻ x in s, (preCdf ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, eq_self_iff_true, forall_const]
  rw [this, ← set_lintegral_withDensity_eq_set_lintegral_mul _ measurable_preCdf _ hs]
  -- ⊢ ∫⁻ (x : α) in s, OfNat.ofNat 1 x ∂Measure.withDensity (Measure.fst ρ) (preCd …
  · simp only [withDensity_preCdf ρ r, Pi.one_apply, lintegral_one, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter]
  · rw [(_ : (1 : α → ℝ≥0∞) = fun _ => 1)]
    -- ⊢ Measurable fun x => 1
    exacts [measurable_const, rfl]
    -- 🎉 no goals
#align probability_theory.set_lintegral_pre_cdf_fst ProbabilityTheory.set_lintegral_preCdf_fst

theorem monotone_preCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r => preCdf ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  -- ⊢ ∀ (i i_1 : ℚ), i ≤ i_1 → ∀ᵐ (a : α) ∂Measure.fst ρ, preCdf ρ i a ≤ preCdf ρ  …
  refine' fun r r' hrr' =>
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCdf measurable_preCdf
      fun s hs _ => _
  rw [set_lintegral_preCdf_fst ρ r hs, set_lintegral_preCdf_fst ρ r' hs]
  -- ⊢ ↑↑(Measure.IicSnd ρ ↑r) s ≤ ↑↑(Measure.IicSnd ρ ↑r') s
  refine' Measure.IicSnd_mono ρ _ s hs
  -- ⊢ ↑r ≤ ↑r'
  exact_mod_cast hrr'
  -- 🎉 no goals
#align probability_theory.monotone_pre_cdf ProbabilityTheory.monotone_preCdf

theorem set_lintegral_iInf_gt_preCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (t : ℚ) {s : Set α}
    (hs : MeasurableSet s) : ∫⁻ x in s, ⨅ r : Ioi t, preCdf ρ r x ∂ρ.fst = ρ.IicSnd t s := by
  refine' le_antisymm _ _
  -- ⊢ ∫⁻ (x : α) in s, ⨅ (r : ↑(Ioi t)), preCdf ρ (↑r) x ∂Measure.fst ρ ≤ ↑↑(Measu …
  · have h : ∀ q : Ioi t, ∫⁻ x in s, ⨅ r : Ioi t, preCdf ρ r x ∂ρ.fst ≤ ρ.IicSnd q s := by
      intro q
      rw [← set_lintegral_preCdf_fst ρ _ hs]
      refine' set_lintegral_mono_ae _ measurable_preCdf _
      · exact measurable_iInf fun _ => measurable_preCdf
      · filter_upwards [monotone_preCdf _] with a _
        exact fun _ => iInf_le _ q
    calc
      ∫⁻ x in s, ⨅ r : Ioi t, preCdf ρ r x ∂ρ.fst ≤ ⨅ q : Ioi t, ρ.IicSnd q s := le_iInf h
      _ = ρ.IicSnd t s := Measure.iInf_IicSnd_gt ρ t hs
  · rw [(set_lintegral_preCdf_fst ρ t hs).symm]
    -- ⊢ ∫⁻ (x : α) in s, preCdf ρ t x ∂Measure.fst ρ ≤ ∫⁻ (x : α) in s, ⨅ (r : ↑(Ioi …
    refine' set_lintegral_mono_ae measurable_preCdf _ _
    -- ⊢ Measurable fun x => ⨅ (r : ↑(Ioi t)), preCdf ρ (↑r) x
    · exact measurable_iInf fun _ => measurable_preCdf
      -- 🎉 no goals
    · filter_upwards [monotone_preCdf _] with a ha_mono
      -- ⊢ a ∈ s → preCdf ρ t a ≤ ⨅ (r : ↑(Ioi t)), preCdf ρ (↑r) a
      exact fun _ => le_iInf fun r => ha_mono (le_of_lt r.prop)
      -- 🎉 no goals
#align probability_theory.set_lintegral_infi_gt_pre_cdf ProbabilityTheory.set_lintegral_iInf_gt_preCdf

theorem preCdf_le_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCdf ρ r a ≤ 1 := by
  rw [ae_all_iff]
  -- ⊢ ∀ (i : ℚ), ∀ᵐ (a : α) ∂Measure.fst ρ, preCdf ρ i a ≤ 1
  refine' fun r =>
    ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCdf measurable_const
      fun s hs _ => _
  rw [set_lintegral_preCdf_fst ρ r hs]
  -- ⊢ ↑↑(Measure.IicSnd ρ ↑r) s ≤ ∫⁻ (x : α) in s, 1 ∂Measure.fst ρ
  simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  -- ⊢ ↑↑(Measure.IicSnd ρ ↑r) s ≤ ↑↑(Measure.fst ρ) s
  exact Measure.IicSnd_le_fst ρ r s hs
  -- 🎉 no goals
#align probability_theory.pre_cdf_le_one ProbabilityTheory.preCdf_le_one

theorem tendsto_lintegral_preCdf_atTop (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    Tendsto (fun r => ∫⁻ a, preCdf ρ r a ∂ρ.fst) atTop (𝓝 (ρ univ)) := by
  convert ρ.tendsto_IicSnd_atTop MeasurableSet.univ
  -- ⊢ ∫⁻ (a : α), preCdf ρ x✝ a ∂Measure.fst ρ = ↑↑(Measure.IicSnd ρ ↑x✝) univ
  · rw [← set_lintegral_univ, set_lintegral_preCdf_fst ρ _ MeasurableSet.univ]
    -- 🎉 no goals
  · exact Measure.fst_univ.symm
    -- 🎉 no goals
#align probability_theory.tendsto_lintegral_pre_cdf_at_top ProbabilityTheory.tendsto_lintegral_preCdf_atTop

theorem tendsto_lintegral_preCdf_atBot (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    Tendsto (fun r => ∫⁻ a, preCdf ρ r a ∂ρ.fst) atBot (𝓝 0) := by
  convert ρ.tendsto_IicSnd_atBot MeasurableSet.univ
  -- ⊢ ∫⁻ (a : α), preCdf ρ x✝ a ∂Measure.fst ρ = ↑↑(Measure.IicSnd ρ ↑x✝) univ
  rw [← set_lintegral_univ, set_lintegral_preCdf_fst ρ _ MeasurableSet.univ]
  -- 🎉 no goals
#align probability_theory.tendsto_lintegral_pre_cdf_at_bot ProbabilityTheory.tendsto_lintegral_preCdf_atBot

theorem tendsto_preCdf_atTop_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 1) := by
  -- We show first that `preCdf` has a limit almost everywhere. That limit has to be at most 1.
  -- We then show that the integral of `preCdf` tends to the integral of 1, and that it also tends
  -- to the integral of the limit. Since the limit is at most 1 and has same integral as 1, it is
  -- equal to 1 a.e.
  have h_mono := monotone_preCdf ρ
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 1)
  have h_le_one := preCdf_le_one ρ
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 1)
  -- `preCdf` has a limit a.e.
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 l) := by
    filter_upwards [h_mono, h_le_one] with a ha_mono ha_le_one
    have h_tendsto :
      Tendsto (fun r => preCdf ρ r a) atTop atTop ∨
        ∃ l, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 l) :=
      tendsto_of_monotone ha_mono
    cases' h_tendsto with h_absurd h_tendsto
    · rw [Monotone.tendsto_atTop_atTop_iff ha_mono] at h_absurd
      obtain ⟨r, hr⟩ := h_absurd 2
      exact absurd (hr.trans (ha_le_one r)) ENNReal.one_lt_two.not_le
    · exact h_tendsto
  classical
  -- let `F` be the pointwise limit of `preCdf` where it exists, and 0 elsewhere.
  let F : α → ℝ≥0∞ := fun a =>
    if h : ∃ l, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 l) then h.choose else 0
  have h_tendsto_ℚ : ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCdf ρ r a) atTop (𝓝 (F a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [dif_pos ha]
    exact ha.choose_spec
  have h_tendsto_ℕ : ∀ᵐ a ∂ρ.fst, Tendsto (fun n : ℕ => preCdf ρ n a) atTop (𝓝 (F a)) := by
    filter_upwards [h_tendsto_ℚ] with a ha using ha.comp tendsto_nat_cast_atTop_atTop
  have hF_ae_meas : AEMeasurable F ρ.fst := by
    refine' aemeasurable_of_tendsto_metrizable_ae _ (fun n => _) h_tendsto_ℚ
    exact measurable_preCdf.aemeasurable
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
      Tendsto (fun r : ℕ => ∫⁻ a, preCdf ρ r a ∂ρ.fst) atTop (𝓝 (∫⁻ a, F a ∂ρ.fst)) := by
      refine'
        lintegral_tendsto_of_tendsto_of_monotone
          (-- does this exist only for ℕ?
          fun _ => measurable_preCdf.aemeasurable)
          _ h_tendsto_ℕ
      filter_upwards [h_mono] with a ha
      refine' fun n m hnm => ha _
      exact_mod_cast hnm
    have h_lintegral' :
      Tendsto (fun r : ℕ => ∫⁻ a, preCdf ρ r a ∂ρ.fst) atTop (𝓝 (∫⁻ _, 1 ∂ρ.fst)) := by
      rw [lintegral_one, Measure.fst_univ]
      exact (tendsto_lintegral_preCdf_atTop ρ).comp tendsto_nat_cast_atTop_atTop
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
#align probability_theory.tendsto_pre_cdf_at_top_one ProbabilityTheory.tendsto_preCdf_atTop_one

theorem tendsto_preCdf_atBot_zero (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCdf ρ r a) atBot (𝓝 0) := by
  -- We show first that `preCdf` has a limit in ℝ≥0∞ almost everywhere.
  -- We then show that the integral of `pre_cdf` tends to 0, and that it also tends
  -- to the integral of the limit. Since the limit has integral 0, it is equal to 0 a.e.
  suffices ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCdf ρ (-r) a) atTop (𝓝 0) by
    filter_upwards [this] with a ha
    have h_eq_neg : (fun r : ℚ => preCdf ρ r a) = fun r : ℚ => preCdf ρ (- -r) a := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    exact ha.comp tendsto_neg_atBot_atTop
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, Tendsto (fun r => preCdf ρ (-r) a) atTop (𝓝 l) := by
    filter_upwards [monotone_preCdf ρ] with a ha
    have h_anti : Antitone fun r => preCdf ρ (-r) a := fun p q hpq => ha (neg_le_neg hpq)
    have h_tendsto :
      Tendsto (fun r => preCdf ρ (-r) a) atTop atBot ∨
        ∃ l, Tendsto (fun r => preCdf ρ (-r) a) atTop (𝓝 l) :=
      tendsto_of_antitone h_anti
    cases' h_tendsto with h_bot h_tendsto
    · exact ⟨0, Tendsto.mono_right h_bot atBot_le_nhds_bot⟩
    · exact h_tendsto
  classical
  let F : α → ℝ≥0∞ := fun a =>
    if h : ∃ l, Tendsto (fun r => preCdf ρ (-r) a) atTop (𝓝 l) then h.choose else 0
  have h_tendsto : ∀ᵐ a ∂ρ.fst, Tendsto (fun r => preCdf ρ (-r) a) atTop (𝓝 (F a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [dif_pos ha]
    exact ha.choose_spec
  suffices h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = 0
  · have hF_ae_meas : AEMeasurable F ρ.fst := by
      refine' aemeasurable_of_tendsto_metrizable_ae _ (fun n => _) h_tendsto
      exact measurable_preCdf.aemeasurable
    rw [lintegral_eq_zero_iff' hF_ae_meas] at h_lintegral_eq
    filter_upwards [h_tendsto, h_lintegral_eq] with a ha_tendsto ha_eq
    rwa [ha_eq] at ha_tendsto
  have h_lintegral :
    Tendsto (fun r => ∫⁻ a, preCdf ρ (-r) a ∂ρ.fst) atTop (𝓝 (∫⁻ a, F a ∂ρ.fst)) := by
    refine'
      tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
        (eventually_of_forall fun _ => measurable_preCdf) (eventually_of_forall fun _ => _) _
        h_tendsto
    · filter_upwards [preCdf_le_one ρ] with a ha using ha _
    · rw [lintegral_one]
      exact measure_ne_top _ _
  have h_lintegral' : Tendsto (fun r => ∫⁻ a, preCdf ρ (-r) a ∂ρ.fst) atTop (𝓝 0) := by
    have h_lintegral_eq :
      (fun r => ∫⁻ a, preCdf ρ (-r) a ∂ρ.fst) = fun r : ℚ => ρ (univ ×ˢ Iic (-r : ℝ)) := by
      ext1 n
      rw [← set_lintegral_univ, set_lintegral_preCdf_fst ρ _ MeasurableSet.univ,
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
    exact_mod_cast hij
  exact tendsto_nhds_unique h_lintegral h_lintegral'
#align probability_theory.tendsto_pre_cdf_at_bot_zero ProbabilityTheory.tendsto_preCdf_atBot_zero

theorem inf_gt_preCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ t : ℚ, ⨅ r : Ioi t, preCdf ρ r a = preCdf ρ t a := by
  rw [ae_all_iff]
  -- ⊢ ∀ (i : ℚ), ∀ᵐ (a : α) ∂Measure.fst ρ, ⨅ (r : ↑(Ioi i)), preCdf ρ (↑r) a = pr …
  refine' fun t => ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite _ measurable_preCdf _
  -- ⊢ Measurable fun a => ⨅ (r : ↑(Ioi t)), preCdf ρ (↑r) a
  · exact measurable_iInf fun i => measurable_preCdf
    -- 🎉 no goals
  intro s hs _
  -- ⊢ ∫⁻ (x : α) in s, ⨅ (r : ↑(Ioi t)), preCdf ρ (↑r) x ∂Measure.fst ρ = ∫⁻ (x :  …
  rw [set_lintegral_iInf_gt_preCdf ρ t hs, set_lintegral_preCdf_fst ρ t hs]
  -- 🎉 no goals
#align probability_theory.inf_gt_pre_cdf ProbabilityTheory.inf_gt_preCdf

section HasCondCdf

/-- A product measure on `α × ℝ` is said to have a conditional cdf at `a : α` if `preCdf` is
monotone with limit 0 at -∞ and 1 at +∞, and is right continuous.
This property holds almost everywhere (see `has_cond_cdf_ae`). -/
structure HasCondCdf (ρ : Measure (α × ℝ)) (a : α) : Prop where
  mono : Monotone fun r => preCdf ρ r a
  le_one : ∀ r, preCdf ρ r a ≤ 1
  tendsto_atTop_one : Tendsto (fun r => preCdf ρ r a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (fun r => preCdf ρ r a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ t : ℚ, ⨅ r : Ioi t, preCdf ρ r a = preCdf ρ t a
#align probability_theory.has_cond_cdf ProbabilityTheory.HasCondCdf

theorem hasCondCdf_ae (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] : ∀ᵐ a ∂ρ.fst, HasCondCdf ρ a := by
  filter_upwards [monotone_preCdf ρ, preCdf_le_one ρ, tendsto_preCdf_atTop_one ρ,
    tendsto_preCdf_atBot_zero ρ, inf_gt_preCdf ρ] with a h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩
  -- 🎉 no goals
#align probability_theory.has_cond_cdf_ae ProbabilityTheory.hasCondCdf_ae

/-- A measurable set of elements of `α` such that `ρ` has a conditional cdf at all
`a ∈ condCdfSet`. -/
def condCdfSet (ρ : Measure (α × ℝ)) : Set α :=
  (toMeasurable ρ.fst {b | ¬HasCondCdf ρ b})ᶜ
#align probability_theory.cond_cdf_set ProbabilityTheory.condCdfSet

theorem measurableSet_condCdfSet (ρ : Measure (α × ℝ)) : MeasurableSet (condCdfSet ρ) :=
  (measurableSet_toMeasurable _ _).compl
#align probability_theory.measurable_set_cond_cdf_set ProbabilityTheory.measurableSet_condCdfSet

theorem hasCondCdf_of_mem_condCdfSet {ρ : Measure (α × ℝ)} {a : α} (h : a ∈ condCdfSet ρ) :
    HasCondCdf ρ a := by
  rw [condCdfSet, mem_compl_iff] at h
  -- ⊢ HasCondCdf ρ a
  have h_ss := subset_toMeasurable ρ.fst {b | ¬HasCondCdf ρ b}
  -- ⊢ HasCondCdf ρ a
  by_contra ha
  -- ⊢ False
  exact h (h_ss ha)
  -- 🎉 no goals
#align probability_theory.has_cond_cdf_of_mem_cond_cdf_set ProbabilityTheory.hasCondCdf_of_mem_condCdfSet

theorem mem_condCdfSet_ae (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, a ∈ condCdfSet ρ := by
  simp_rw [ae_iff, condCdfSet, not_mem_compl_iff, setOf_mem_eq, measure_toMeasurable]
  -- ⊢ ↑↑(Measure.fst ρ) {b | ¬HasCondCdf ρ b} = 0
  exact hasCondCdf_ae ρ
  -- 🎉 no goals
#align probability_theory.mem_cond_cdf_set_ae ProbabilityTheory.mem_condCdfSet_ae

end HasCondCdf

open scoped Classical

/-- Conditional cdf of the measure given the value on `α`, restricted to the rationals.
It is defined to be `pre_cdf` if `a ∈ condCdfSet`, and a default cdf-like function
otherwise. This is an auxiliary definition used to define `cond_cdf`. -/
noncomputable def condCdfRat (ρ : Measure (α × ℝ)) : α → ℚ → ℝ := fun a =>
  if a ∈ condCdfSet ρ then fun r => (preCdf ρ r a).toReal else fun r => if r < 0 then 0 else 1
#align probability_theory.cond_cdf_rat ProbabilityTheory.condCdfRat

theorem condCdfRat_of_not_mem (ρ : Measure (α × ℝ)) (a : α) (h : a ∉ condCdfSet ρ) {r : ℚ} :
    condCdfRat ρ a r = if r < 0 then 0 else 1 := by simp only [condCdfRat, h, if_false]
                                                    -- 🎉 no goals
#align probability_theory.cond_cdf_rat_of_not_mem ProbabilityTheory.condCdfRat_of_not_mem

theorem condCdfRat_of_mem (ρ : Measure (α × ℝ)) (a : α) (h : a ∈ condCdfSet ρ) (r : ℚ) :
    condCdfRat ρ a r = (preCdf ρ r a).toReal := by simp only [condCdfRat, h, if_true]
                                                   -- 🎉 no goals
#align probability_theory.cond_cdf_rat_of_mem ProbabilityTheory.condCdfRat_of_mem

theorem monotone_condCdfRat (ρ : Measure (α × ℝ)) (a : α) : Monotone (condCdfRat ρ a) := by
  by_cases h : a ∈ condCdfSet ρ
  -- ⊢ Monotone (condCdfRat ρ a)
  · simp only [condCdfRat, h, if_true, forall_const, and_self_iff]
    -- ⊢ Monotone fun r => ENNReal.toReal (preCdf ρ r a)
    intro r r' hrr'
    -- ⊢ (fun r => ENNReal.toReal (preCdf ρ r a)) r ≤ (fun r => ENNReal.toReal (preCd …
    have h' := hasCondCdf_of_mem_condCdfSet h
    -- ⊢ (fun r => ENNReal.toReal (preCdf ρ r a)) r ≤ (fun r => ENNReal.toReal (preCd …
    have h_ne_top : ∀ r, preCdf ρ r a ≠ ∞ := fun r =>
      ((h'.le_one r).trans_lt ENNReal.one_lt_top).ne
    rw [ENNReal.toReal_le_toReal (h_ne_top _) (h_ne_top _)]
    -- ⊢ preCdf ρ r a ≤ preCdf ρ r' a
    exact h'.1 hrr'
    -- 🎉 no goals
  · simp only [condCdfRat, h, if_false]
    -- ⊢ Monotone fun r => if r < 0 then 0 else 1
    intro x y hxy
    -- ⊢ (fun r => if r < 0 then 0 else 1) x ≤ (fun r => if r < 0 then 0 else 1) y
    dsimp only
    -- ⊢ (if x < 0 then 0 else 1) ≤ if y < 0 then 0 else 1
    split_ifs with h_1 h_2 h_2
    exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]
    -- 🎉 no goals
#align probability_theory.monotone_cond_cdf_rat ProbabilityTheory.monotone_condCdfRat

theorem measurable_condCdfRat (ρ : Measure (α × ℝ)) (q : ℚ) :
    Measurable fun a => condCdfRat ρ a q := by
  simp_rw [condCdfRat, ite_apply]
  -- ⊢ Measurable fun a => if a ∈ condCdfSet ρ then ENNReal.toReal (preCdf ρ q a) e …
  exact
    Measurable.ite (measurableSet_condCdfSet ρ) measurable_preCdf.ennreal_toReal
      measurable_const
#align probability_theory.measurable_cond_cdf_rat ProbabilityTheory.measurable_condCdfRat

theorem condCdfRat_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) : 0 ≤ condCdfRat ρ a r := by
  -- Porting note: was
  -- unfold condCdfRat; split_ifs; exacts [ENNReal.toReal_nonneg, le_rfl, zero_le_one]
  unfold condCdfRat; split_ifs
  -- ⊢ 0 ≤ ite (a ∈ condCdfSet ρ) (fun r => ENNReal.toReal (preCdf ρ r a)) (fun r = …
                     -- ⊢ 0 ≤ (fun r => ENNReal.toReal (preCdf ρ r a)) r
  · exact ENNReal.toReal_nonneg
    -- 🎉 no goals
  dsimp only
  -- ⊢ 0 ≤ if r < 0 then 0 else 1
  split_ifs
  -- ⊢ 0 ≤ 0
  exacts [le_rfl, zero_le_one]
  -- 🎉 no goals
#align probability_theory.cond_cdf_rat_nonneg ProbabilityTheory.condCdfRat_nonneg

theorem condCdfRat_le_one (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) : condCdfRat ρ a r ≤ 1 := by
  unfold condCdfRat
  -- ⊢ ite (a ∈ condCdfSet ρ) (fun r => ENNReal.toReal (preCdf ρ r a)) (fun r => if …
  split_ifs with h
  -- ⊢ (fun r => ENNReal.toReal (preCdf ρ r a)) r ≤ 1
  · refine' ENNReal.toReal_le_of_le_ofReal zero_le_one _
    -- ⊢ preCdf ρ r a ≤ ENNReal.ofReal 1
    rw [ENNReal.ofReal_one]
    -- ⊢ preCdf ρ r a ≤ 1
    exact (hasCondCdf_of_mem_condCdfSet h).le_one r
    -- 🎉 no goals
  -- Porting note: added
  dsimp only; split_ifs
  -- ⊢ (if r < 0 then 0 else 1) ≤ 1
              -- ⊢ 0 ≤ 1
  exacts [zero_le_one, le_rfl]
  -- 🎉 no goals
#align probability_theory.cond_cdf_rat_le_one ProbabilityTheory.condCdfRat_le_one

theorem tendsto_condCdfRat_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCdfRat ρ a) atBot (𝓝 0) := by
  unfold condCdfRat
  -- ⊢ Tendsto (if a ∈ condCdfSet ρ then fun r => ENNReal.toReal (preCdf ρ r a) els …
  split_ifs with h
  -- ⊢ Tendsto (fun r => ENNReal.toReal (preCdf ρ r a)) atBot (𝓝 0)
  · rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff]
    · exact (hasCondCdf_of_mem_condCdfSet h).tendsto_atBot_zero
      -- 🎉 no goals
    · have h' := hasCondCdf_of_mem_condCdfSet h
      -- ⊢ ∀ (i : ℚ), preCdf ρ i a ≠ ⊤
      exact fun r => ((h'.le_one r).trans_lt ENNReal.one_lt_top).ne
      -- 🎉 no goals
    · exact ENNReal.zero_ne_top
      -- 🎉 no goals
  · refine' (tendsto_congr' _).mp tendsto_const_nhds
    -- ⊢ (fun x => 0) =ᶠ[atBot] fun r => if r < 0 then 0 else 1
    rw [EventuallyEq, eventually_atBot]
    -- ⊢ ∃ a, ∀ (b : ℚ), b ≤ a → 0 = if b < 0 then 0 else 1
    refine' ⟨-1, fun q hq => (if_pos (hq.trans_lt _)).symm⟩
    -- ⊢ -1 < 0
    linarith
    -- 🎉 no goals
#align probability_theory.tendsto_cond_cdf_rat_at_bot ProbabilityTheory.tendsto_condCdfRat_atBot

theorem tendsto_condCdfRat_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCdfRat ρ a) atTop (𝓝 1) := by
  unfold condCdfRat
  -- ⊢ Tendsto (if a ∈ condCdfSet ρ then fun r => ENNReal.toReal (preCdf ρ r a) els …
  split_ifs with h
  -- ⊢ Tendsto (fun r => ENNReal.toReal (preCdf ρ r a)) atTop (𝓝 1)
  · have h' := hasCondCdf_of_mem_condCdfSet h
    -- ⊢ Tendsto (fun r => ENNReal.toReal (preCdf ρ r a)) atTop (𝓝 1)
    rw [← ENNReal.one_toReal, ENNReal.tendsto_toReal_iff]
    · exact h'.tendsto_atTop_one
      -- 🎉 no goals
    · exact fun r => ((h'.le_one r).trans_lt ENNReal.one_lt_top).ne
      -- 🎉 no goals
    · exact ENNReal.one_ne_top
      -- 🎉 no goals
  · refine' (tendsto_congr' _).mp tendsto_const_nhds
    -- ⊢ (fun x => 1) =ᶠ[atTop] fun r => if r < 0 then 0 else 1
    rw [EventuallyEq, eventually_atTop]
    -- ⊢ ∃ a, ∀ (b : ℚ), b ≥ a → 1 = if b < 0 then 0 else 1
    exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩
    -- 🎉 no goals
#align probability_theory.tendsto_cond_cdf_rat_at_top ProbabilityTheory.tendsto_condCdfRat_atTop

theorem condCdfRat_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => condCdfRat ρ a r) =ᵐ[ρ.fst] fun a => (preCdf ρ r a).toReal := by
  filter_upwards [mem_condCdfSet_ae ρ] with a ha using condCdfRat_of_mem ρ a ha r
  -- 🎉 no goals
#align probability_theory.cond_cdf_rat_ae_eq ProbabilityTheory.condCdfRat_ae_eq

theorem ofReal_condCdfRat_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => ENNReal.ofReal (condCdfRat ρ a r)) =ᵐ[ρ.fst] preCdf ρ r := by
  filter_upwards [condCdfRat_ae_eq ρ r, preCdf_le_one ρ] with a ha ha_le_one
  -- ⊢ ENNReal.ofReal (condCdfRat ρ a r) = preCdf ρ r a
  rw [ha, ENNReal.ofReal_toReal]
  -- ⊢ preCdf ρ r a ≠ ⊤
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne
  -- 🎉 no goals
#align probability_theory.of_real_cond_cdf_rat_ae_eq ProbabilityTheory.ofReal_condCdfRat_ae_eq

theorem inf_gt_condCdfRat (ρ : Measure (α × ℝ)) (a : α) (t : ℚ) :
    ⨅ r : Ioi t, condCdfRat ρ a r = condCdfRat ρ a t := by
  by_cases ha : a ∈ condCdfSet ρ
  -- ⊢ ⨅ (r : ↑(Ioi t)), condCdfRat ρ a ↑r = condCdfRat ρ a t
  · simp_rw [condCdfRat_of_mem ρ a ha]
    -- ⊢ ⨅ (r : ↑(Ioi t)), ENNReal.toReal (preCdf ρ (↑r) a) = ENNReal.toReal (preCdf  …
    have ha' := hasCondCdf_of_mem_condCdfSet ha
    -- ⊢ ⨅ (r : ↑(Ioi t)), ENNReal.toReal (preCdf ρ (↑r) a) = ENNReal.toReal (preCdf  …
    rw [← ENNReal.toReal_iInf]
    -- ⊢ ENNReal.toReal (⨅ (r : ↑(Ioi t)), preCdf ρ (↑r) a) = ENNReal.toReal (preCdf  …
    · suffices ⨅ i : ↥(Ioi t), preCdf ρ (↑i) a = preCdf ρ t a by rw [this]
      -- ⊢ ⨅ (i : ↑(Ioi t)), preCdf ρ (↑i) a = preCdf ρ t a
      rw [← ha'.iInf_rat_gt_eq]
      -- 🎉 no goals
    · exact fun r => ((ha'.le_one r).trans_lt ENNReal.one_lt_top).ne
      -- 🎉 no goals
  · simp_rw [condCdfRat_of_not_mem ρ a ha]
    -- ⊢ (⨅ (r : ↑(Ioi t)), if ↑r < 0 then 0 else 1) = if t < 0 then 0 else 1
    have h_bdd : BddBelow (range fun r : ↥(Ioi t) => ite ((r : ℚ) < 0) (0 : ℝ) 1) := by
      refine' ⟨0, fun x hx => _⟩
      obtain ⟨y, rfl⟩ := mem_range.mpr hx
      dsimp only
      split_ifs
      exacts [le_rfl, zero_le_one]
    split_ifs with h
    -- ⊢ (⨅ (r : ↑(Ioi t)), if ↑r < 0 then 0 else 1) = 0
    · refine' le_antisymm _ (le_ciInf fun x => _)
      -- ⊢ (⨅ (r : ↑(Ioi t)), if ↑r < 0 then 0 else 1) ≤ 0
      · obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0 := by
          refine' ⟨t / 2, _, _⟩
          · linarith
          · linarith
        refine' (ciInf_le h_bdd ⟨q, htq⟩).trans _
        -- ⊢ (if ↑{ val := q, property := htq } < 0 then 0 else 1) ≤ 0
        rw [if_pos]
        -- ⊢ ↑{ val := q, property := htq } < 0
        rwa [Subtype.coe_mk]
        -- 🎉 no goals
      · split_ifs
        -- ⊢ 0 ≤ 0
        exacts [le_rfl, zero_le_one]
        -- 🎉 no goals
    · refine' le_antisymm _ _
      -- ⊢ (⨅ (r : ↑(Ioi t)), if ↑r < 0 then 0 else 1) ≤ 1
      · refine' (ciInf_le h_bdd ⟨t + 1, lt_add_one t⟩).trans _
        -- ⊢ (if ↑{ val := t + 1, property := (_ : t < t + 1) } < 0 then 0 else 1) ≤ 1
        split_ifs
        -- ⊢ 0 ≤ 1
        exacts [zero_le_one, le_rfl]
        -- 🎉 no goals
      · refine' le_ciInf fun x => _
        -- ⊢ 1 ≤ if ↑x < 0 then 0 else 1
        rw [if_neg]
        -- ⊢ ¬↑x < 0
        rw [not_lt] at h ⊢
        -- ⊢ 0 ≤ ↑x
        exact h.trans (mem_Ioi.mp x.prop).le
        -- 🎉 no goals
#align probability_theory.inf_gt_cond_cdf_rat ProbabilityTheory.inf_gt_condCdfRat

/-- Conditional cdf of the measure given the value on `α`, as a plain function. This is an auxiliary
definition used to define `cond_cdf`. -/
noncomputable irreducible_def condCdf' (ρ : Measure (α × ℝ)) : α → ℝ → ℝ := fun a t =>
  ⨅ r : { r' : ℚ // t < r' }, condCdfRat ρ a r
#align probability_theory.cond_cdf' ProbabilityTheory.condCdf'

theorem condCdf'_def' {ρ : Measure (α × ℝ)} {a : α} {x : ℝ} :
    condCdf' ρ a x = ⨅ r : { r : ℚ // x < r }, condCdfRat ρ a r := by rw [condCdf']
                                                                      -- 🎉 no goals
#align probability_theory.cond_cdf'_def ProbabilityTheory.condCdf'_def'

theorem condCdf'_eq_condCdfRat (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) :
    condCdf' ρ a r = condCdfRat ρ a r := by
  rw [← inf_gt_condCdfRat ρ a r, condCdf']
  -- ⊢ ⨅ (r_1 : { r' // ↑r < ↑r' }), condCdfRat ρ a ↑r_1 = ⨅ (r_1 : ↑(Ioi r)), cond …
  refine' Equiv.iInf_congr _ _
  -- ⊢ { r' // ↑r < ↑r' } ≃ ↑(Ioi r)
  · exact
      { toFun := fun t => ⟨t.1, by exact_mod_cast t.2⟩
        invFun := fun t => ⟨t.1, by exact_mod_cast t.2⟩
        left_inv := fun t => by simp only [Subtype.coe_eta]
        right_inv := fun t => by simp only [Subtype.coe_eta] }
  · intro t
    -- ⊢ condCdfRat ρ a ↑(↑{ toFun := fun t => { val := ↑t, property := (_ : r < ↑t)  …
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]
    -- 🎉 no goals
#align probability_theory.cond_cdf'_eq_cond_cdf_rat ProbabilityTheory.condCdf'_eq_condCdfRat

theorem condCdf'_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCdf' ρ a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [condCdf'_def]
  -- ⊢ 0 ≤ ⨅ (r_1 : { r' // r < ↑r' }), condCdfRat ρ a ↑r_1
  exact le_ciInf fun r' => condCdfRat_nonneg ρ a _
  -- 🎉 no goals
#align probability_theory.cond_cdf'_nonneg ProbabilityTheory.condCdf'_nonneg

theorem bddBelow_range_condCdfRat_gt (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    BddBelow (range fun r : { r' : ℚ // x < ↑r' } => condCdfRat ρ a r) := by
  refine' ⟨0, fun z => _⟩; rintro ⟨u, rfl⟩; exact condCdfRat_nonneg ρ a _
  -- ⊢ (z ∈ range fun r => condCdfRat ρ a ↑r) → 0 ≤ z
                           -- ⊢ 0 ≤ (fun r => condCdfRat ρ a ↑r) u
                                            -- 🎉 no goals
#align probability_theory.bdd_below_range_cond_cdf_rat_gt ProbabilityTheory.bddBelow_range_condCdfRat_gt

theorem monotone_condCdf' (ρ : Measure (α × ℝ)) (a : α) : Monotone (condCdf' ρ a) := by
  intro x y hxy
  -- ⊢ condCdf' ρ a x ≤ condCdf' ρ a y
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [condCdf'_def]
  -- ⊢ ⨅ (r : { r' // x < ↑r' }), condCdfRat ρ a ↑r ≤ ⨅ (r : { r' // y < ↑r' }), co …
  refine' le_ciInf fun r => (ciInf_le _ _).trans_eq _
  · exact bddBelow_range_condCdfRat_gt ρ a x
    -- 🎉 no goals
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align probability_theory.monotone_cond_cdf' ProbabilityTheory.monotone_condCdf'

theorem continuousWithinAt_condCdf'_Ici (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    ContinuousWithinAt (condCdf' ρ a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  -- ⊢ ContinuousWithinAt (condCdf' ρ a) (Ioi x) x
  convert Monotone.tendsto_nhdsWithin_Ioi (monotone_condCdf' ρ a) x
  -- ⊢ ContinuousWithinAt (condCdf' ρ a) (Ioi x) x ↔ Tendsto (condCdf' ρ a) (𝓝[Ioi  …
  rw [sInf_image']
  -- ⊢ ContinuousWithinAt (condCdf' ρ a) (Ioi x) x ↔ Tendsto (condCdf' ρ a) (𝓝[Ioi  …
  have h' : ⨅ r : Ioi x, condCdf' ρ a r = ⨅ r : { r' : ℚ // x < r' }, condCdf' ρ a r := by
    refine' Real.iInf_Ioi_eq_iInf_rat_gt x _ (monotone_condCdf' ρ a)
    refine' ⟨0, fun z => _⟩
    rintro ⟨u, -, rfl⟩
    exact condCdf'_nonneg ρ a u
  have h'' :
    ⨅ r : { r' : ℚ // x < r' }, condCdf' ρ a r =
      ⨅ r : { r' : ℚ // x < r' }, condCdfRat ρ a r := by
    congr with r
    exact condCdf'_eq_condCdfRat ρ a r
  rw [h', h'', ContinuousWithinAt]
  -- ⊢ Tendsto (condCdf' ρ a) (𝓝[Ioi x] x) (𝓝 (condCdf' ρ a x)) ↔ Tendsto (condCdf' …
  congr!
  -- ⊢ condCdf' ρ a x = ⨅ (r : { r' // x < ↑r' }), condCdfRat ρ a ↑r
  exact condCdf'_def'
  -- 🎉 no goals
#align probability_theory.continuous_within_at_cond_cdf'_Ici ProbabilityTheory.continuousWithinAt_condCdf'_Ici

/-! ### Conditional cdf -/


/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable def condCdf (ρ : Measure (α × ℝ)) (a : α) : StieltjesFunction where
  toFun := condCdf' ρ a
  mono' := monotone_condCdf' ρ a
  right_continuous' x := continuousWithinAt_condCdf'_Ici ρ a x
#align probability_theory.cond_cdf ProbabilityTheory.condCdf

theorem condCdf_eq_condCdfRat (ρ : Measure (α × ℝ)) (a : α) (r : ℚ) :
    condCdf ρ a r = condCdfRat ρ a r :=
  condCdf'_eq_condCdfRat ρ a r
#align probability_theory.cond_cdf_eq_cond_cdf_rat ProbabilityTheory.condCdf_eq_condCdfRat

/-- The conditional cdf is non-negative for all `a : α`. -/
theorem condCdf_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCdf ρ a r :=
  condCdf'_nonneg ρ a r
#align probability_theory.cond_cdf_nonneg ProbabilityTheory.condCdf_nonneg

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
theorem condCdf_le_one (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) : condCdf ρ a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  -- ⊢ ↑(condCdf ρ a) x ≤ 1
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  -- ⊢ ⨅ (r : { r' // x < ↑r' }), ↑(condCdf ρ a) ↑↑r ≤ 1
  simp_rw [condCdf_eq_condCdfRat]
  -- ⊢ ⨅ (r : { r' // x < ↑r' }), condCdfRat ρ a ↑r ≤ 1
  refine' ciInf_le_of_le (bddBelow_range_condCdfRat_gt ρ a x) _ (condCdfRat_le_one _ _ _)
  -- ⊢ { r' // x < ↑r' }
  exact ⟨r, hrx⟩
  -- 🎉 no goals
#align probability_theory.cond_cdf_le_one ProbabilityTheory.condCdf_le_one

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
theorem tendsto_condCdf_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCdf ρ a) atBot (𝓝 0) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := fun x => exists_rat_btwn (lt_add_one x)
  -- ⊢ Tendsto (↑(condCdf ρ a)) atBot (𝓝 0)
  let qs : ℝ → ℚ := fun x => (h_exists x).choose
  -- ⊢ Tendsto (↑(condCdf ρ a)) atBot (𝓝 0)
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine' fun q => ⟨q - 1, fun y hy => _⟩
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact_mod_cast h_le
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_condCdfRat_atBot ρ a).comp hqs_tendsto) (condCdf_nonneg ρ a) fun x => _
  rw [Function.comp_apply, ← condCdf_eq_condCdfRat]
  -- ⊢ ↑(condCdf ρ a) x ≤ ↑(condCdf ρ a) ↑(qs x)
  exact (condCdf ρ a).mono (h_exists x).choose_spec.1.le
  -- 🎉 no goals
#align probability_theory.tendsto_cond_cdf_at_bot ProbabilityTheory.tendsto_condCdf_atBot

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
theorem tendsto_condCdf_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCdf ρ a) atTop (𝓝 1) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x - 1 < q ∧ ↑q < x := fun x => exists_rat_btwn (sub_one_lt x)
  -- ⊢ Tendsto (↑(condCdf ρ a)) atTop (𝓝 1)
  let qs : ℝ → ℚ := fun x => (h_exists x).choose
  -- ⊢ Tendsto (↑(condCdf ρ a)) atTop (𝓝 1)
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine' fun q => ⟨q + 1, fun y hy => _⟩
    have h_le : y - 1 ≤ qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le ((tendsto_condCdfRat_atTop ρ a).comp hqs_tendsto)
      tendsto_const_nhds _ (condCdf_le_one ρ a)
  intro x
  -- ⊢ (condCdfRat ρ a ∘ qs) x ≤ ↑(condCdf ρ a) x
  rw [Function.comp_apply, ← condCdf_eq_condCdfRat]
  -- ⊢ ↑(condCdf ρ a) ↑(qs x) ≤ ↑(condCdf ρ a) x
  exact (condCdf ρ a).mono (le_of_lt (h_exists x).choose_spec.2)
  -- 🎉 no goals
#align probability_theory.tendsto_cond_cdf_at_top ProbabilityTheory.tendsto_condCdf_atTop

theorem condCdf_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => condCdf ρ a r) =ᵐ[ρ.fst] fun a => (preCdf ρ r a).toReal := by
  filter_upwards [mem_condCdfSet_ae ρ] with a ha using
    (condCdf_eq_condCdfRat ρ a r).trans (condCdfRat_of_mem ρ a ha r)
#align probability_theory.cond_cdf_ae_eq ProbabilityTheory.condCdf_ae_eq

theorem ofReal_condCdf_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a => ENNReal.ofReal (condCdf ρ a r)) =ᵐ[ρ.fst] preCdf ρ r := by
  filter_upwards [condCdf_ae_eq ρ r, preCdf_le_one ρ] with a ha ha_le_one
  -- ⊢ ENNReal.ofReal (↑(condCdf ρ a) ↑r) = preCdf ρ r a
  rw [ha, ENNReal.ofReal_toReal]
  -- ⊢ preCdf ρ r a ≠ ⊤
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne
  -- 🎉 no goals
#align probability_theory.of_real_cond_cdf_ae_eq ProbabilityTheory.ofReal_condCdf_ae_eq

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
theorem measurable_condCdf (ρ : Measure (α × ℝ)) (x : ℝ) : Measurable fun a => condCdf ρ a x := by
  have : (fun a => condCdf ρ a x) = fun a => ⨅ r : { r' : ℚ // x < r' }, condCdfRat ρ a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [condCdf_eq_condCdfRat]
  rw [this]
  -- ⊢ Measurable fun a => ⨅ (r : { r' // x < ↑r' }), condCdfRat ρ a ↑r
  exact
    measurable_ciInf (fun q => measurable_condCdfRat ρ q) fun a =>
      bddBelow_range_condCdfRat_gt ρ a _
#align probability_theory.measurable_cond_cdf ProbabilityTheory.measurable_condCdf

/-- Auxiliary lemma for `set_lintegral_cond_cdf`. -/
theorem set_lintegral_condCdf_rat (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCdf ρ a r) ∂ρ.fst = ρ (s ×ˢ Iic (r : ℝ)) := by
  have : ∀ᵐ a ∂ρ.fst, a ∈ s → ENNReal.ofReal (condCdf ρ a r) = preCdf ρ r a := by
    filter_upwards [ofReal_condCdf_ae_eq ρ r] with a ha using fun _ => ha
  rw [set_lintegral_congr_fun hs this, set_lintegral_preCdf_fst ρ r hs]
  -- ⊢ ↑↑(Measure.IicSnd ρ ↑r) s = ↑↑ρ (s ×ˢ Iic ↑r)
  exact ρ.IicSnd_apply r hs
  -- 🎉 no goals
#align probability_theory.set_lintegral_cond_cdf_rat ProbabilityTheory.set_lintegral_condCdf_rat

theorem set_lintegral_condCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫⁻ a in s, ENNReal.ofReal (condCdf ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_cond_cdf_rat`. We use the equality
  -- `cond_cdf ρ a x = ⨅ r : {r' : ℚ // x < r'}, cond_cdf ρ a r` and a monotone convergence
  -- argument to extend it to the reals.
  by_cases hρ_zero : ρ.fst.restrict s = 0
  -- ⊢ ∫⁻ (a : α) in s, ENNReal.ofReal (↑(condCdf ρ a) x) ∂Measure.fst ρ = ↑↑ρ (s × …
  · rw [hρ_zero, lintegral_zero_measure]
    -- ⊢ 0 = ↑↑ρ (s ×ˢ Iic x)
    refine' le_antisymm (zero_le _) _
    -- ⊢ ↑↑ρ (s ×ˢ Iic x) ≤ 0
    calc
      ρ (s ×ˢ Iic x) ≤ ρ (Prod.fst ⁻¹' s) := measure_mono (prod_subset_preimage_fst s (Iic x))
      _ = ρ.fst s := by rw [Measure.fst_apply hs]
      _ = ρ.fst.restrict s univ := by rw [Measure.restrict_apply_univ]
      _ = 0 := by simp only [hρ_zero, Measure.coe_zero, Pi.zero_apply]
  have h :
    ∫⁻ a in s, ENNReal.ofReal (condCdf ρ a x) ∂ρ.fst =
      ∫⁻ a in s, ENNReal.ofReal (⨅ r : { r' : ℚ // x < r' }, condCdf ρ a r) ∂ρ.fst := by
    congr with a : 1
    rw [← (condCdf ρ a).iInf_rat_gt_eq x]
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h]
  -- ⊢ ∫⁻ (a : α) in s, ENNReal.ofReal (⨅ (r : { r' // x < ↑r' }), ↑(condCdf ρ a) ↑ …
  simp_rw [ENNReal.ofReal_cinfi]
  -- ⊢ ∫⁻ (a : α) in s, ⨅ (i : { r' // x < ↑r' }), ENNReal.ofReal (↑(condCdf ρ a) ↑ …
  have h_coe : ∀ b : { r' : ℚ // x < ↑r' }, (b : ℝ) = ((b : ℚ) : ℝ) := fun _ => by congr
  -- ⊢ ∫⁻ (a : α) in s, ⨅ (i : { r' // x < ↑r' }), ENNReal.ofReal (↑(condCdf ρ a) ↑ …
  rw [lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } =>
      (measurable_condCdf ρ q).ennreal_ofReal]
  rotate_left
  · intro b
    -- ⊢ ∫⁻ (a : α) in s, ENNReal.ofReal (↑(condCdf ρ a) ↑↑b) ∂Measure.fst ρ ≠ ⊤
    rw [set_lintegral_condCdf_rat ρ _ hs]
    -- ⊢ ↑↑ρ (s ×ˢ Iic ↑↑b) ≠ ⊤
    exact measure_ne_top ρ _
    -- 🎉 no goals
  · refine' Monotone.directed_ge fun i j hij a => ENNReal.ofReal_le_ofReal ((condCdf ρ a).mono _)
    -- ⊢ ↑↑i ≤ ↑↑j
    rw [h_coe, h_coe]
    -- ⊢ ↑↑i ≤ ↑↑j
    exact_mod_cast hij
    -- 🎉 no goals
  simp_rw [set_lintegral_condCdf_rat ρ _ hs]
  -- ⊢ ⨅ (b : { r' // x < ↑r' }), ↑↑ρ (s ×ˢ Iic ↑↑b) = ↑↑ρ (s ×ˢ Iic x)
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    -- ⊢ ↑↑ρ (s ×ˢ ⋂ (i : { r' // x < ↑r' }), Iic ↑↑i) = ↑↑ρ (s ×ˢ Iic x)
    congr with y
    -- ⊢ y ∈ ⋂ (i : { r' // x < ↑r' }), Iic ↑↑i ↔ y ∈ Iic x
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    -- ⊢ (∀ (a : ℚ), x < ↑a → y ≤ ↑a) ↔ y ≤ x
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq => hyx.trans hq.le⟩
    -- 🎉 no goals
  · exact fun i => hs.prod measurableSet_Iic
    -- 🎉 no goals
  · refine' Monotone.directed_ge fun i j hij => _
    -- ⊢ s ×ˢ Iic ↑↑i ≤ s ×ˢ Iic ↑↑j
    refine' prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr _⟩)
    -- ⊢ ↑↑i ≤ ↑↑j
    exact_mod_cast hij
    -- 🎉 no goals
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩
    -- 🎉 no goals
#align probability_theory.set_lintegral_cond_cdf ProbabilityTheory.set_lintegral_condCdf

theorem lintegral_condCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCdf ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) := by
  rw [← set_lintegral_univ, set_lintegral_condCdf ρ _ MeasurableSet.univ]
  -- 🎉 no goals
#align probability_theory.lintegral_cond_cdf ProbabilityTheory.lintegral_condCdf

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_condCdf (ρ : Measure (α × ℝ)) (x : ℝ) :
    StronglyMeasurable fun a => condCdf ρ a x :=
  (measurable_condCdf ρ x).stronglyMeasurable
#align probability_theory.strongly_measurable_cond_cdf ProbabilityTheory.stronglyMeasurable_condCdf

theorem integrable_condCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a => condCdf ρ a x) ρ.fst := by
  refine' integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) _ fun t _ _ => _
  -- ⊢ AEStronglyMeasurable (fun a => ↑(condCdf ρ a) x) (Measure.fst ρ)
  · exact (stronglyMeasurable_condCdf ρ _).aestronglyMeasurable
    -- 🎉 no goals
  · have : ∀ y, (‖condCdf ρ y x‖₊ : ℝ≥0∞) ≤ 1 := by
      intro y
      rw [Real.nnnorm_of_nonneg (condCdf_nonneg _ _ _)]
      -- Porting note: was exact_mod_cast condCdf_le_one _ _ _
      simp only [ENNReal.coe_le_one_iff]
      exact condCdf_le_one _ _ _
    refine'
      (set_lintegral_mono (measurable_condCdf _ _).ennnorm measurable_one fun y _ => this y).trans
        _
    simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
    -- ⊢ ↑↑(Measure.fst ρ) t ≤ ↑↑(Measure.fst ρ) univ
    exact measure_mono (subset_univ _)
    -- 🎉 no goals
#align probability_theory.integrable_cond_cdf ProbabilityTheory.integrable_condCdf

theorem set_integral_condCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCdf ρ a x ∂ρ.fst = (ρ (s ×ˢ Iic x)).toReal := by
  have h := set_lintegral_condCdf ρ x hs
  -- ⊢ ∫ (a : α) in s, ↑(condCdf ρ a) x ∂Measure.fst ρ = ENNReal.toReal (↑↑ρ (s ×ˢ  …
  rw [← ofReal_integral_eq_lintegral_ofReal] at h
  · rw [← h, ENNReal.toReal_ofReal]
    -- ⊢ 0 ≤ ∫ (x_1 : α) in s, ↑(condCdf ρ x_1) x ∂Measure.fst ρ
    exact integral_nonneg fun _ => condCdf_nonneg _ _ _
    -- 🎉 no goals
  · exact (integrable_condCdf _ _).integrableOn
    -- 🎉 no goals
  · exact eventually_of_forall fun _ => condCdf_nonneg _ _ _
    -- 🎉 no goals
#align probability_theory.set_integral_cond_cdf ProbabilityTheory.set_integral_condCdf

theorem integral_condCdf (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCdf ρ a x ∂ρ.fst = (ρ (univ ×ˢ Iic x)).toReal := by
  rw [← set_integral_condCdf ρ _ MeasurableSet.univ, Measure.restrict_univ]
  -- 🎉 no goals
#align probability_theory.integral_cond_cdf ProbabilityTheory.integral_condCdf

section Measure

theorem measure_condCdf_Iic (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    (condCdf ρ a).measure (Iic x) = ENNReal.ofReal (condCdf ρ a x) := by
  rw [← sub_zero (condCdf ρ a x)]
  -- ⊢ ↑↑(StieltjesFunction.measure (condCdf ρ a)) (Iic x) = ENNReal.ofReal (↑(cond …
  exact (condCdf ρ a).measure_Iic (tendsto_condCdf_atBot ρ a) _
  -- 🎉 no goals
#align probability_theory.measure_cond_cdf_Iic ProbabilityTheory.measure_condCdf_Iic

theorem measure_condCdf_univ (ρ : Measure (α × ℝ)) (a : α) : (condCdf ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  -- ⊢ ↑↑(StieltjesFunction.measure (condCdf ρ a)) univ = ENNReal.ofReal (1 - 0)
  exact StieltjesFunction.measure_univ _ (tendsto_condCdf_atBot ρ a) (tendsto_condCdf_atTop ρ a)
  -- 🎉 no goals
#align probability_theory.measure_cond_cdf_univ ProbabilityTheory.measure_condCdf_univ

instance instIsProbabilityMeasure (ρ : Measure (α × ℝ)) (a : α) :
    IsProbabilityMeasure (condCdf ρ a).measure :=
  ⟨measure_condCdf_univ ρ a⟩

/-- The function `a ↦ (condCdf ρ a).measure` is measurable. -/
theorem measurable_measure_condCdf (ρ : Measure (α × ℝ)) :
    Measurable fun a => (condCdf ρ a).measure := by
  rw [Measure.measurable_measure]
  -- ⊢ ∀ (s : Set ℝ), MeasurableSet s → Measurable fun b => ↑↑(StieltjesFunction.me …
  refine' fun s hs => ?_
  -- ⊢ Measurable fun b => ↑↑(StieltjesFunction.measure (condCdf ρ b)) s
  -- Porting note: supplied `C`
  refine' MeasurableSpace.induction_on_inter
    (C := fun s => Measurable fun b ↦ StieltjesFunction.measure (condCdf ρ b) s)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ hs
  · simp only [measure_empty, measurable_const]
    -- 🎉 no goals
  · rintro S ⟨u, rfl⟩
    -- ⊢ Measurable fun b => ↑↑(StieltjesFunction.measure (condCdf ρ b)) (Iic u)
    simp_rw [measure_condCdf_Iic ρ _ u]
    -- ⊢ Measurable fun b => ENNReal.ofReal (↑(condCdf ρ b) u)
    exact (measurable_condCdf ρ u).ennreal_ofReal
    -- 🎉 no goals
  · intro t ht ht_cd_meas
    -- ⊢ Measurable fun b => ↑↑(StieltjesFunction.measure (condCdf ρ b)) tᶜ
    have :
      (fun a => (condCdf ρ a).measure tᶜ) =
        (fun a => (condCdf ρ a).measure univ) - fun a => (condCdf ρ a).measure t := by
      ext1 a
      rw [measure_compl ht (measure_ne_top (condCdf ρ a).measure _), Pi.sub_apply]
    simp_rw [this, measure_condCdf_univ ρ]
    -- ⊢ Measurable ((fun a => 1) - fun a => ↑↑(StieltjesFunction.measure (condCdf ρ  …
    exact Measurable.sub measurable_const ht_cd_meas
    -- 🎉 no goals
  · intro f hf_disj hf_meas hf_cd_meas
    -- ⊢ Measurable fun b => ↑↑(StieltjesFunction.measure (condCdf ρ b)) (⋃ (i : ℕ),  …
    simp_rw [measure_iUnion hf_disj hf_meas]
    -- ⊢ Measurable fun b => ∑' (i : ℕ), ↑↑(StieltjesFunction.measure (condCdf ρ b))  …
    exact Measurable.ennreal_tsum hf_cd_meas
    -- 🎉 no goals
#align probability_theory.measurable_measure_cond_cdf ProbabilityTheory.measurable_measure_condCdf

end Measure

end ProbabilityTheory
