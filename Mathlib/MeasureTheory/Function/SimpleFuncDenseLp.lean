/-
Copyright (c) 2022 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.SimpleFuncDense

#align_import measure_theory.function.simple_func_dense_lp from "leanprover-community/mathlib"@"5a2df4cd59cb31e97a516d4603a14bed5c2f9425"

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.Lp.simpleFunc`, the type of `Lp` simple functions
* `coeToLp`, the embedding of `Lp.simpleFunc E p μ` into `Lp E p μ`

## Main results

* `tendsto_approxOn_Lp_snorm` (Lᵖ convergence): If `E` is a `NormedAddCommGroup` and `f` is
  measurable and `Memℒp` (for `p < ∞`), then the simple functions
  `SimpleFunc.approxOn f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simpleFunc.denseEmbedding`: the embedding `coeToLp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simpleFunc.induction`, `Lp.induction`, `Memℒp.induction`, `Integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/


noncomputable section

set_option linter.uppercaseLean3 false

open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open scoped Classical Topology ENNReal MeasureTheory BigOperators

variable {α β ι E F 𝕜 : Type*}

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Lp approximation by simple functions -/

section Lp

variable [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {q : ℝ} {p : ℝ≥0∞}

theorem nnnorm_approxOn_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - f x‖₊ ≤ ‖f x - y₀‖₊ := by
  have := edist_approxOn_le hf h₀ x n
  -- ⊢ ‖↑(approxOn f hf s y₀ h₀ n) x - f x‖₊ ≤ ‖f x - y₀‖₊
  rw [edist_comm y₀] at this
  -- ⊢ ‖↑(approxOn f hf s y₀ h₀ n) x - f x‖₊ ≤ ‖f x - y₀‖₊
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  -- ⊢ ‖↑(approxOn f hf s y₀ h₀ n) x - f x‖₊ ≤ ‖f x - y₀‖₊
  exact_mod_cast this
  -- 🎉 no goals
#align measure_theory.simple_func.nnnorm_approx_on_le MeasureTheory.SimpleFunc.nnnorm_approxOn_le

theorem norm_approxOn_y₀_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖ := by
  have := edist_approxOn_y0_le hf h₀ x n
  -- ⊢ ‖↑(approxOn f hf s y₀ h₀ n) x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖
  repeat' rw [edist_comm y₀, edist_eq_coe_nnnorm_sub] at this
  -- ⊢ ‖↑(approxOn f hf s y₀ h₀ n) x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖
  exact_mod_cast this
  -- 🎉 no goals
#align measure_theory.simple_func.norm_approx_on_y₀_le MeasureTheory.SimpleFunc.norm_approxOn_y₀_le

theorem norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    (h₀ : (0 : E) ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s 0 h₀ n x‖ ≤ ‖f x‖ + ‖f x‖ := by
  have := edist_approxOn_y0_le hf h₀ x n
  -- ⊢ ‖↑(approxOn f hf s 0 h₀ n) x‖ ≤ ‖f x‖ + ‖f x‖
  simp [edist_comm (0 : E), edist_eq_coe_nnnorm] at this
  -- ⊢ ‖↑(approxOn f hf s 0 h₀ n) x‖ ≤ ‖f x‖ + ‖f x‖
  exact_mod_cast this
  -- 🎉 no goals
#align measure_theory.simple_func.norm_approx_on_zero_le MeasureTheory.SimpleFunc.norm_approxOn_zero_le

theorem tendsto_approxOn_Lp_snorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (hp_ne_top : p ≠ ∞) {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : snorm (fun x => f x - y₀) p μ < ∞) :
    Tendsto (fun n => snorm (⇑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0) := by
  by_cases hp_zero : p = 0
  -- ⊢ Tendsto (fun n => snorm (↑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0)
  · simpa only [hp_zero, snorm_exponent_zero] using tendsto_const_nhds
    -- 🎉 no goals
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  -- ⊢ Tendsto (fun n => snorm (↑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0)
  suffices
      Tendsto (fun n => ∫⁻ x, (‖approxOn f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) atTop
        (𝓝 0) by
    simp only [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_ne_top]
    convert continuous_rpow_const.continuousAt.tendsto.comp this
    simp [zero_rpow_of_pos (_root_.inv_pos.mpr hp)]
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas :
    ∀ n, Measurable fun x => (‖approxOn f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.toReal := by
    simpa only [← edist_eq_coe_nnnorm_sub] using fun n =>
      (approxOn f hf s y₀ h₀ n).measurable_bind (fun y x => edist y (f x) ^ p.toReal) fun y =>
        (measurable_edist_right.comp hf).pow_const p.toReal
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `fun x => ‖f x - y₀‖ ^ p.toReal`
  have h_bound :
    ∀ n, (fun x => (‖approxOn f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.toReal) ≤ᵐ[μ] fun x =>
        (‖f x - y₀‖₊ : ℝ≥0∞) ^ p.toReal :=
    fun n =>
    eventually_of_forall fun x =>
      rpow_le_rpow (coe_mono (nnnorm_approxOn_le hf h₀ x n)) toReal_nonneg
  -- (3) The bounding function `fun x => ‖f x - y₀‖ ^ p.toReal` has finite integral
  have h_fin : (∫⁻ a : β, (‖f a - y₀‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ≠ ⊤ :=
    (lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_zero hp_ne_top hi).ne
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim :
    ∀ᵐ a : β ∂μ,
      Tendsto (fun n => (‖approxOn f hf s y₀ h₀ n a - f a‖₊ : ℝ≥0∞) ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [hμ] with a ha
    have : Tendsto (fun n => (approxOn f hf s y₀ h₀ n) a - f a) atTop (𝓝 (f a - f a)) :=
      (tendsto_approxOn hf h₀ ha).sub tendsto_const_nhds
    convert continuous_rpow_const.continuousAt.tendsto.comp (tendsto_coe.mpr this.nnnorm)
    simp [zero_rpow_of_pos hp]
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim
  -- 🎉 no goals
#align measure_theory.simple_func.tendsto_approx_on_Lp_snorm MeasureTheory.SimpleFunc.tendsto_approxOn_Lp_snorm

theorem memℒp_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Memℒp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Memℒp (fun _ => y₀) p μ) (n : ℕ) : Memℒp (approxOn f fmeas s y₀ h₀ n) p μ := by
  refine' ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, _⟩
  -- ⊢ snorm (↑(approxOn f fmeas s y₀ h₀ n)) p μ < ⊤
  suffices snorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : Memℒp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert snorm_add_lt_top this hi₀
    ext x
    simp
  have hf' : Memℒp (fun x => ‖f x - y₀‖) p μ := by
    have h_meas : Measurable fun x => ‖f x - y₀‖ := by
      simp only [← dist_eq_norm]
      exact (continuous_id.dist continuous_const).measurable.comp fmeas
    refine' ⟨h_meas.aemeasurable.aestronglyMeasurable, _⟩
    rw [snorm_norm]
    convert snorm_add_lt_top hf hi₀.neg with x
    simp [sub_eq_add_neg]
  have : ∀ᵐ x ∂μ, ‖approxOn f fmeas s y₀ h₀ n x - y₀‖ ≤ ‖‖f x - y₀‖ + ‖f x - y₀‖‖ := by
    refine' eventually_of_forall _
    intro x
    convert norm_approxOn_y₀_le fmeas h₀ x n using 1
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    snorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ ≤
        snorm (fun x => ‖f x - y₀‖ + ‖f x - y₀‖) p μ :=
      snorm_mono_ae this
    _ < ⊤ := snorm_add_lt_top hf' hf'
#align measure_theory.simple_func.mem_ℒp_approx_on MeasureTheory.SimpleFunc.memℒp_approxOn

theorem tendsto_approxOn_range_Lp_snorm [BorelSpace E] {f : β → E} (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : snorm f p μ < ∞) :
    Tendsto (fun n => snorm (⇑(approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) - f) p μ)
                                                                      -- 🎉 no goals
      atTop (𝓝 0) := by
  refine' tendsto_approxOn_Lp_snorm fmeas _ hp_ne_top _ _
  -- ⊢ ∀ᵐ (x : β) ∂μ, f x ∈ closure (Set.range f ∪ {0})
  · apply eventually_of_forall
    -- ⊢ ∀ (x : β), f x ∈ closure (Set.range f ∪ {0})
    intro x
    -- ⊢ f x ∈ closure (Set.range f ∪ {0})
    apply subset_closure
    -- ⊢ f x ∈ Set.range f ∪ {0}
    simp
    -- 🎉 no goals
  · simpa using hf
    -- 🎉 no goals
#align measure_theory.simple_func.tendsto_approx_on_range_Lp_snorm MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp_snorm

theorem memℒp_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Memℒp f p μ) (n : ℕ) :
    Memℒp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) p μ :=
                                                  -- 🎉 no goals
  memℒp_approxOn fmeas hf (y₀ := 0) (by simp) zero_memℒp n
                                        -- 🎉 no goals
#align measure_theory.simple_func.mem_ℒp_approx_on_range MeasureTheory.SimpleFunc.memℒp_approxOn_range

theorem tendsto_approxOn_range_Lp [BorelSpace E] {f : β → E} [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : Memℒp f p μ) :
    Tendsto
      (fun n =>
        (memℒp_approxOn_range fmeas hf n).toLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n))
                                                                                       -- 🎉 no goals
      atTop (𝓝 (hf.toLp f)) := by
  simpa only [Lp.tendsto_Lp_iff_tendsto_ℒp''] using
    tendsto_approxOn_range_Lp_snorm hp_ne_top fmeas hf.2
#align measure_theory.simple_func.tendsto_approx_on_range_Lp MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp

/-- Any function in `ℒp` can be approximated by a simple function if `p < ∞`. -/
theorem _root_.MeasureTheory.Memℒp.exists_simpleFunc_snorm_sub_lt {E : Type*}
    [NormedAddCommGroup E] {f : β → E} {μ : Measure β} (hf : Memℒp f p μ) (hp_ne_top : p ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : β →ₛ E, snorm (f - ⇑g) p μ < ε ∧ Memℒp g p μ := by
  borelize E
  -- ⊢ ∃ g, snorm (f - ↑g) p μ < ε ∧ Memℒp (↑g) p
  let f' := hf.1.mk f
  -- ⊢ ∃ g, snorm (f - ↑g) p μ < ε ∧ Memℒp (↑g) p
  rsuffices ⟨g, hg, g_mem⟩ : ∃ g : β →ₛ E, snorm (f' - ⇑g) p μ < ε ∧ Memℒp g p μ
  -- ⊢ ∃ g, snorm (f - ↑g) p μ < ε ∧ Memℒp (↑g) p
  · refine' ⟨g, _, g_mem⟩
    -- ⊢ snorm (f - ↑g) p μ < ε
    suffices snorm (f - ⇑g) p μ = snorm (f' - ⇑g) p μ by rwa [this]
    -- ⊢ snorm (f - ↑g) p μ = snorm (f' - ↑g) p μ
    apply snorm_congr_ae
    -- ⊢ f - ↑g =ᵐ[μ] f' - ↑g
    filter_upwards [hf.1.ae_eq_mk] with x hx
    -- ⊢ (f - ↑g) x = (AEStronglyMeasurable.mk f (_ : AEStronglyMeasurable f μ) - ↑g) x
    simpa only [Pi.sub_apply, sub_left_inj] using hx
    -- 🎉 no goals
  have hf' : Memℒp f' p μ := hf.ae_eq hf.1.ae_eq_mk
  -- ⊢ ∃ g, snorm (f' - ↑g) p μ < ε ∧ Memℒp (↑g) p
  have f'meas : Measurable f' := hf.1.measurable_mk
  -- ⊢ ∃ g, snorm (f' - ↑g) p μ < ε ∧ Memℒp (↑g) p
  have : SeparableSpace (range f' ∪ {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hf.1.stronglyMeasurable_mk
  rcases ((tendsto_approxOn_range_Lp_snorm hp_ne_top f'meas hf'.2).eventually <|
    gt_mem_nhds hε.bot_lt).exists with ⟨n, hn⟩
  rw [← snorm_neg, neg_sub] at hn
  -- ⊢ ∃ g, snorm (f' - ↑g) p μ < ε ∧ Memℒp (↑g) p
  exact ⟨_, hn, memℒp_approxOn_range f'meas hf' _⟩
  -- 🎉 no goals
#align measure_theory.mem_ℒp.exists_simple_func_snorm_sub_lt MeasureTheory.Memℒp.exists_simpleFunc_snorm_sub_lt

end Lp

/-! ### L1 approximation by simple functions -/


section Integrable

variable [MeasurableSpace β]

variable [MeasurableSpace E] [NormedAddCommGroup E]

theorem tendsto_approxOn_L1_nnnorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : HasFiniteIntegral (fun x => f x - y₀) μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖₊ ∂μ) atTop (𝓝 0) := by
  simpa [snorm_one_eq_lintegral_nnnorm] using
    tendsto_approxOn_Lp_snorm hf h₀ one_ne_top hμ
      (by simpa [snorm_one_eq_lintegral_nnnorm] using hi)
#align measure_theory.simple_func.tendsto_approx_on_L1_nnnorm MeasureTheory.SimpleFunc.tendsto_approxOn_L1_nnnorm

theorem integrable_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Integrable (fun _ => y₀) μ) (n : ℕ) : Integrable (approxOn f fmeas s y₀ h₀ n) μ := by
  rw [← memℒp_one_iff_integrable] at hf hi₀ ⊢
  -- ⊢ Memℒp (↑(approxOn f fmeas s y₀ h₀ n)) 1
  exact memℒp_approxOn fmeas hf h₀ hi₀ n
  -- 🎉 no goals
#align measure_theory.simple_func.integrable_approx_on MeasureTheory.SimpleFunc.integrable_approxOn

theorem tendsto_approxOn_range_L1_nnnorm [OpensMeasurableSpace E] {f : β → E} {μ : Measure β}
    [SeparableSpace (range f ∪ {0} : Set E)] (fmeas : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖₊ ∂μ) atTop
                                                                    -- 🎉 no goals
      (𝓝 0) := by
  apply tendsto_approxOn_L1_nnnorm fmeas
  -- ⊢ ∀ᵐ (x : β) ∂μ, f x ∈ closure (Set.range f ∪ {0})
  · apply eventually_of_forall
    -- ⊢ ∀ (x : β), f x ∈ closure (Set.range f ∪ {0})
    intro x
    -- ⊢ f x ∈ closure (Set.range f ∪ {0})
    apply subset_closure
    -- ⊢ f x ∈ Set.range f ∪ {0}
    simp
    -- 🎉 no goals
  · simpa using hf.2
    -- 🎉 no goals
#align measure_theory.simple_func.tendsto_approx_on_range_L1_nnnorm MeasureTheory.SimpleFunc.tendsto_approxOn_range_L1_nnnorm

theorem integrable_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Integrable f μ) (n : ℕ) :
    Integrable (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) μ :=
                                                       -- 🎉 no goals
  integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n
#align measure_theory.simple_func.integrable_approx_on_range MeasureTheory.SimpleFunc.integrable_approxOn_range

end Integrable

section SimpleFuncProperties

variable [MeasurableSpace α]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable {μ : Measure α} {p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `Memℒp f 0 μ` and `Memℒp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `Memℒp f p μ ↔ Integrable f μ ↔ f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞`.
-/


theorem exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  exists_forall_le (f.map fun x => ‖x‖)
#align measure_theory.simple_func.exists_forall_norm_le MeasureTheory.SimpleFunc.exists_forall_norm_le

theorem memℒp_zero (f : α →ₛ E) (μ : Measure α) : Memℒp f 0 μ :=
  memℒp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable
#align measure_theory.simple_func.mem_ℒp_zero MeasureTheory.SimpleFunc.memℒp_zero

theorem memℒp_top (f : α →ₛ E) (μ : Measure α) : Memℒp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  memℒp_top_of_bound f.aestronglyMeasurable C <| eventually_of_forall hfC
#align measure_theory.simple_func.mem_ℒp_top MeasureTheory.SimpleFunc.memℒp_top

protected theorem snorm'_eq {p : ℝ} (f : α →ₛ F) (μ : Measure α) :
    snorm' f p μ = (∑ y in f.range, (‖y‖₊ : ℝ≥0∞) ^ p * μ (f ⁻¹' {y})) ^ (1 / p) := by
  have h_map : (fun a => (‖f a‖₊ : ℝ≥0∞) ^ p) = f.map fun a : F => (‖a‖₊ : ℝ≥0∞) ^ p := by
    simp; rfl
  rw [snorm', h_map, lintegral_eq_lintegral, map_lintegral]
  -- 🎉 no goals
#align measure_theory.simple_func.snorm'_eq MeasureTheory.SimpleFunc.snorm'_eq

theorem measure_preimage_lt_top_of_memℒp (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) (f : α →ₛ E)
    (hf : Memℒp f p μ) (y : E) (hy_ne : y ≠ 0) : μ (f ⁻¹' {y}) < ∞ := by
  have hp_pos_real : 0 < p.toReal := ENNReal.toReal_pos hp_pos hp_ne_top
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  have hf_snorm := Memℒp.snorm_lt_top hf
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  rw [snorm_eq_snorm' hp_pos hp_ne_top, f.snorm'_eq, ←
    @ENNReal.lt_rpow_one_div_iff _ _ (1 / p.toReal) (by simp [hp_pos_real]),
    @ENNReal.top_rpow_of_pos (1 / (1 / p.toReal)) (by simp [hp_pos_real]),
    ENNReal.sum_lt_top_iff] at hf_snorm
  by_cases hyf : y ∈ f.range
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  swap
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  · suffices h_empty : f ⁻¹' {y} = ∅
    -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
    · rw [h_empty, measure_empty]; exact ENNReal.coe_lt_top
      -- ⊢ 0 < ⊤
                                   -- 🎉 no goals
    ext1 x
    -- ⊢ x ∈ ↑f ⁻¹' {y} ↔ x ∈ ∅
    rw [Set.mem_preimage, Set.mem_singleton_iff, mem_empty_iff_false, iff_false_iff]
    -- ⊢ ¬↑f x = y
    refine' fun hxy => hyf _
    -- ⊢ y ∈ SimpleFunc.range f
    rw [mem_range, Set.mem_range]
    -- ⊢ ∃ y_1, ↑f y_1 = y
    exact ⟨x, hxy⟩
    -- 🎉 no goals
  specialize hf_snorm y hyf
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  rw [ENNReal.mul_lt_top_iff] at hf_snorm
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  cases hf_snorm with
  | inl hf_snorm => exact hf_snorm.2
  | inr hf_snorm =>
    cases hf_snorm with
    | inl hf_snorm =>
      refine' absurd _ hy_ne
      simpa [hp_pos_real] using hf_snorm
    | inr hf_snorm => simp [hf_snorm]
#align measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memℒp

theorem memℒp_of_finite_measure_preimage (p : ℝ≥0∞) {f : α →ₛ E}
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) : Memℒp f p μ := by
  by_cases hp0 : p = 0
  -- ⊢ Memℒp (↑f) p
  · rw [hp0, memℒp_zero_iff_aestronglyMeasurable]; exact f.aestronglyMeasurable
    -- ⊢ AEStronglyMeasurable (↑f) μ
                                                   -- 🎉 no goals
  by_cases hp_top : p = ∞
  -- ⊢ Memℒp (↑f) p
  · rw [hp_top]; exact memℒp_top f μ
    -- ⊢ Memℒp ↑f ⊤
                 -- 🎉 no goals
  refine' ⟨f.aestronglyMeasurable, _⟩
  -- ⊢ snorm (↑f) p μ < ⊤
  rw [snorm_eq_snorm' hp0 hp_top, f.snorm'_eq]
  -- ⊢ (∑ y in SimpleFunc.range f, ↑‖y‖₊ ^ ENNReal.toReal p * ↑↑μ (↑f ⁻¹' {y})) ^ ( …
  refine' ENNReal.rpow_lt_top_of_nonneg (by simp) (ENNReal.sum_lt_top_iff.mpr fun y _ => _).ne
  -- ⊢ ↑‖y‖₊ ^ ENNReal.toReal p * ↑↑μ (↑f ⁻¹' {y}) < ⊤
  by_cases hy0 : y = 0
  -- ⊢ ↑‖y‖₊ ^ ENNReal.toReal p * ↑↑μ (↑f ⁻¹' {y}) < ⊤
  · simp [hy0, ENNReal.toReal_pos hp0 hp_top]
    -- 🎉 no goals
  · refine' ENNReal.mul_lt_top _ (hf y hy0).ne
    -- ⊢ ↑‖y‖₊ ^ ENNReal.toReal p ≠ ⊤
    exact (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top).ne
    -- 🎉 no goals
#align measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage MeasureTheory.SimpleFunc.memℒp_of_finite_measure_preimage

theorem memℒp_iff {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp f p μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ :=
  ⟨fun h => measure_preimage_lt_top_of_memℒp hp_pos hp_ne_top f h, fun h =>
    memℒp_of_finite_measure_preimage p h⟩
#align measure_theory.simple_func.mem_ℒp_iff MeasureTheory.SimpleFunc.memℒp_iff

theorem integrable_iff {f : α →ₛ E} : Integrable f μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ :=
  memℒp_one_iff_integrable.symm.trans <| memℒp_iff one_ne_zero ENNReal.coe_ne_top
#align measure_theory.simple_func.integrable_iff MeasureTheory.SimpleFunc.integrable_iff

theorem memℒp_iff_integrable {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp f p μ ↔ Integrable f μ :=
  (memℒp_iff hp_pos hp_ne_top).trans integrable_iff.symm
#align measure_theory.simple_func.mem_ℒp_iff_integrable MeasureTheory.SimpleFunc.memℒp_iff_integrable

theorem memℒp_iff_finMeasSupp {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp f p μ ↔ f.FinMeasSupp μ :=
  (memℒp_iff hp_pos hp_ne_top).trans finMeasSupp_iff.symm
#align measure_theory.simple_func.mem_ℒp_iff_fin_meas_supp MeasureTheory.SimpleFunc.memℒp_iff_finMeasSupp

theorem integrable_iff_finMeasSupp {f : α →ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ :=
  integrable_iff.trans finMeasSupp_iff.symm
#align measure_theory.simple_func.integrable_iff_fin_meas_supp MeasureTheory.SimpleFunc.integrable_iff_finMeasSupp

theorem FinMeasSupp.integrable {f : α →ₛ E} (h : f.FinMeasSupp μ) : Integrable f μ :=
  integrable_iff_finMeasSupp.2 h
#align measure_theory.simple_func.fin_meas_supp.integrable MeasureTheory.SimpleFunc.FinMeasSupp.integrable

theorem integrable_pair {f : α →ₛ E} {g : α →ₛ F} :
    Integrable f μ → Integrable g μ → Integrable (pair f g) μ := by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair
  -- 🎉 no goals
#align measure_theory.simple_func.integrable_pair MeasureTheory.SimpleFunc.integrable_pair

theorem memℒp_of_isFiniteMeasure (f : α →ₛ E) (p : ℝ≥0∞) (μ : Measure α) [IsFiniteMeasure μ] :
    Memℒp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  Memℒp.of_bound f.aestronglyMeasurable C <| eventually_of_forall hfC
#align measure_theory.simple_func.mem_ℒp_of_is_finite_measure MeasureTheory.SimpleFunc.memℒp_of_isFiniteMeasure

theorem integrable_of_isFiniteMeasure [IsFiniteMeasure μ] (f : α →ₛ E) : Integrable f μ :=
  memℒp_one_iff_integrable.mp (f.memℒp_of_isFiniteMeasure 1 μ)
#align measure_theory.simple_func.integrable_of_is_finite_measure MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure

theorem measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) {x : E}
    (hx : x ≠ 0) : μ (f ⁻¹' {x}) < ∞ :=
  integrable_iff.mp hf x hx
#align measure_theory.simple_func.measure_preimage_lt_top_of_integrable MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable

theorem measure_support_lt_top [Zero β] (f : α →ₛ β) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    μ (support f) < ∞ := by
  rw [support_eq]
  -- ⊢ ↑↑μ (⋃ (y : β) (_ : y ∈ filter (fun y => y ≠ 0) (SimpleFunc.range f)), ↑f ⁻¹ …
  refine' (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top_iff.mpr fun y hy => _)
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  rw [Finset.mem_filter] at hy
  -- ⊢ ↑↑μ (↑f ⁻¹' {y}) < ⊤
  exact hf y hy.2
  -- 🎉 no goals
#align measure_theory.simple_func.measure_support_lt_top MeasureTheory.SimpleFunc.measure_support_lt_top

theorem measure_support_lt_top_of_memℒp (f : α →ₛ E) (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : μ (support f) < ∞ :=
  f.measure_support_lt_top ((memℒp_iff hp_ne_zero hp_ne_top).mp hf)
#align measure_theory.simple_func.measure_support_lt_top_of_mem_ℒp MeasureTheory.SimpleFunc.measure_support_lt_top_of_memℒp

theorem measure_support_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) :
    μ (support f) < ∞ :=
  f.measure_support_lt_top (integrable_iff.mp hf)
#align measure_theory.simple_func.measure_support_lt_top_of_integrable MeasureTheory.SimpleFunc.measure_support_lt_top_of_integrable

theorem measure_lt_top_of_memℒp_indicator (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {c : E} (hc : c ≠ 0)
    {s : Set α} (hs : MeasurableSet s) (hcs : Memℒp ((const α c).piecewise s hs (const α 0)) p μ) :
    μ s < ⊤ := by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  -- ⊢ ↑↑μ s < ⊤
  simpa only [memℒp_iff_finMeasSupp hp_pos hp_ne_top, finMeasSupp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs
#align measure_theory.simple_func.measure_lt_top_of_mem_ℒp_indicator MeasureTheory.SimpleFunc.measure_lt_top_of_memℒp_indicator

end SimpleFuncProperties

end SimpleFunc

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/


namespace Lp

open AEEqFun

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (p : ℝ≥0∞)
  (μ : Measure α)

variable (E)

-- Porting note: the proofs were rewritten in tactic mode to avoid an
-- "unknown free variable '_uniq.546677'" error.
/-- `Lp.simpleFunc` is a subspace of Lp consisting of equivalence classes of an integrable simple
    function. -/
def simpleFunc : AddSubgroup (Lp E p μ) where
  carrier := { f : Lp E p μ | ∃ s : α →ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α →ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    -- ⊢ f + g ∈ {f | ∃ s, AEEqFun.mk ↑s (_ : AEStronglyMeasurable (↑s) μ) = ↑f}
    use s + t
    -- ⊢ AEEqFun.mk ↑(s + t) (_ : AEStronglyMeasurable (↑(s + t)) μ) = ↑(f + g)
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add, AEEqFun.mk_eq_mk,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro f ⟨s, hs⟩
    -- ⊢ -f ∈ { toAddSubsemigroup := { carrier := {f | ∃ s, AEEqFun.mk ↑s (_ : AEStro …
    use -s
    -- ⊢ AEEqFun.mk ↑(-s) (_ : AEStronglyMeasurable (↑(-s)) μ) = ↑(-f)
    simp only [← hs, AEEqFun.neg_mk, SimpleFunc.coe_neg, AEEqFun.mk_eq_mk, AddSubgroup.coe_neg]
    -- 🎉 no goals
#align measure_theory.Lp.simple_func MeasureTheory.Lp.simpleFunc

variable {E p μ}

namespace simpleFunc

section Instances

/-! Simple functions in Lp space form a `NormedSpace`. -/


#noalign measure_theory.Lp.simple_func.coe_coe

protected theorem eq' {f g : Lp.simpleFunc E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
  Subtype.eq ∘ Subtype.eq
#align measure_theory.Lp.simple_func.eq' MeasureTheory.Lp.simpleFunc.eq'

/-! Implementation note:  If `Lp.simpleFunc E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simpleFunc E p μ`, would be
unnecessary.  But instead, `Lp.simpleFunc E p μ` is defined as an `AddSubgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a `SMul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      -- ⊢ k • ↑{ val := f, property := (_ : ∃ s, AEEqFun.mk ↑s (_ : AEStronglyMeasurab …
      use k • s
      -- ⊢ AEEqFun.mk ↑(k • s) (_ : AEStronglyMeasurable (↑(k • s)) μ) = ↑(k • ↑{ val : …
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      -- ⊢ k • AEEqFun.mk ↑s (_ : AEStronglyMeasurable (↑s) μ) = ↑(k • ↑{ val := f, pro …
      rw [hs]
      -- ⊢ k • ↑f = ↑(k • ↑{ val := f, property := (_ : ∃ s, AEEqFun.mk ↑s (_ : AEStron …
      rfl⟩⟩
      -- 🎉 no goals
#align measure_theory.Lp.simple_func.has_smul MeasureTheory.Lp.simpleFunc.smul

attribute [local instance] simpleFunc.smul

@[simp, norm_cast]
theorem coe_smul (c : 𝕜) (f : Lp.simpleFunc E p μ) :
    ((c • f : Lp.simpleFunc E p μ) : Lp E p μ) = c • (f : Lp E p μ) :=
  rfl
#align measure_theory.Lp.simple_func.coe_smul MeasureTheory.Lp.simpleFunc.coe_smul

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def module : Module 𝕜 (Lp.simpleFunc E p μ) where
  one_smul f := by ext1; exact one_smul _ _
                   -- ⊢ ↑(1 • f) = ↑f
                         -- 🎉 no goals
  mul_smul x y f := by ext1; exact mul_smul _ _ _
                       -- ⊢ ↑((x * y) • f) = ↑(x • y • f)
                             -- 🎉 no goals
  smul_add x f g := by ext1; exact smul_add _ _ _
                       -- ⊢ ↑(x • (f + g)) = ↑(x • f + x • g)
                    -- ⊢ ↑(x • 0) = ↑0
                          -- 🎉 no goals
                             -- 🎉 no goals
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
                       -- ⊢ ↑((x + y) • f) = ↑(x • f + y • f)
                             -- 🎉 no goals
  zero_smul f := by ext1; exact zero_smul _ _
                    -- ⊢ ↑(0 • f) = ↑0
                          -- 🎉 no goals
#align measure_theory.Lp.simple_func.module MeasureTheory.Lp.simpleFunc.module

attribute [local instance] simpleFunc.module

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected theorem boundedSMul [Fact (1 ≤ p)] : BoundedSMul 𝕜 (Lp.simpleFunc E p μ) :=
  BoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : Lp E p μ) : _)
#align measure_theory.Lp.simple_func.has_bounded_smul MeasureTheory.Lp.simpleFunc.boundedSMul

attribute [local instance] simpleFunc.boundedSMul

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def normedSpace {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩
#align measure_theory.Lp.simple_func.normed_space MeasureTheory.Lp.simpleFunc.normedSpace

end Instances

attribute [local instance] simpleFunc.module simpleFunc.normedSpace simpleFunc.boundedSMul

section ToLp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `Memℒp`. -/
@[reducible]
def toLp (f : α →ₛ E) (hf : Memℒp f p μ) : Lp.simpleFunc E p μ :=
  ⟨hf.toLp f, ⟨f, rfl⟩⟩
#align measure_theory.Lp.simple_func.to_Lp MeasureTheory.Lp.simpleFunc.toLp

theorem toLp_eq_toLp (f : α →ₛ E) (hf : Memℒp f p μ) : (toLp f hf : Lp E p μ) = hf.toLp f :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_eq_to_Lp MeasureTheory.Lp.simpleFunc.toLp_eq_toLp

theorem toLp_eq_mk (f : α →ₛ E) (hf : Memℒp f p μ) :
    (toLp f hf : α →ₘ[μ] E) = AEEqFun.mk f f.aestronglyMeasurable :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_eq_mk MeasureTheory.Lp.simpleFunc.toLp_eq_mk

theorem toLp_zero : toLp (0 : α →ₛ E) zero_memℒp = (0 : Lp.simpleFunc E p μ) :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_zero MeasureTheory.Lp.simpleFunc.toLp_zero

theorem toLp_add (f g : α →ₛ E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    toLp (f + g) (hf.add hg) = toLp f hf + toLp g hg :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_add MeasureTheory.Lp.simpleFunc.toLp_add

theorem toLp_neg (f : α →ₛ E) (hf : Memℒp f p μ) : toLp (-f) hf.neg = -toLp f hf :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_neg MeasureTheory.Lp.simpleFunc.toLp_neg

theorem toLp_sub (f g : α →ₛ E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    toLp (f - g) (hf.sub hg) = toLp f hf - toLp g hg := by
  simp only [sub_eq_add_neg, ← toLp_neg, ← toLp_add]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.to_Lp_sub MeasureTheory.Lp.simpleFunc.toLp_sub

variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

theorem toLp_smul (f : α →ₛ E) (hf : Memℒp f p μ) (c : 𝕜) :
    toLp (c • f) (hf.const_smul c) = c • toLp f hf :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_smul MeasureTheory.Lp.simpleFunc.toLp_smul

nonrec theorem norm_toLp [Fact (1 ≤ p)] (f : α →ₛ E) (hf : Memℒp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (snorm f p μ) :=
  norm_toLp f hf
#align measure_theory.Lp.simple_func.norm_to_Lp MeasureTheory.Lp.simpleFunc.norm_toLp

end ToLp

section ToSimpleFunc

/-- Find a representative of a `Lp.simpleFunc`. -/
def toSimpleFunc (f : Lp.simpleFunc E p μ) : α →ₛ E :=
  Classical.choose f.2
#align measure_theory.Lp.simple_func.to_simple_func MeasureTheory.Lp.simpleFunc.toSimpleFunc

/-- `(toSimpleFunc f)` is measurable. -/
@[measurability]
protected theorem measurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    Measurable (toSimpleFunc f) :=
  (toSimpleFunc f).measurable
#align measure_theory.Lp.simple_func.measurable MeasureTheory.Lp.simpleFunc.measurable

protected theorem stronglyMeasurable (f : Lp.simpleFunc E p μ) :
    StronglyMeasurable (toSimpleFunc f) :=
  (toSimpleFunc f).stronglyMeasurable
#align measure_theory.Lp.simple_func.strongly_measurable MeasureTheory.Lp.simpleFunc.stronglyMeasurable

@[measurability]
protected theorem aemeasurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    AEMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.measurable f).aemeasurable
#align measure_theory.Lp.simple_func.ae_measurable MeasureTheory.Lp.simpleFunc.aemeasurable

protected theorem aestronglyMeasurable (f : Lp.simpleFunc E p μ) :
    AEStronglyMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.stronglyMeasurable f).aestronglyMeasurable
#align measure_theory.Lp.simple_func.ae_strongly_measurable MeasureTheory.Lp.simpleFunc.aestronglyMeasurable

theorem toSimpleFunc_eq_toFun (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f :=
  show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α →ₘ[μ] E) by
    convert (AEEqFun.coeFn_mk (toSimpleFunc f)
          (toSimpleFunc f).aestronglyMeasurable).symm using 2
    exact (Classical.choose_spec f.2).symm
    -- 🎉 no goals
#align measure_theory.Lp.simple_func.to_simple_func_eq_to_fun MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun

/-- `toSimpleFunc f` satisfies the predicate `Memℒp`. -/
protected theorem memℒp (f : Lp.simpleFunc E p μ) : Memℒp (toSimpleFunc f) p μ :=
  Memℒp.ae_eq (toSimpleFunc_eq_toFun f).symm <| mem_Lp_iff_memℒp.mp (f : Lp E p μ).2
#align measure_theory.Lp.simple_func.mem_ℒp MeasureTheory.Lp.simpleFunc.memℒp

theorem toLp_toSimpleFunc (f : Lp.simpleFunc E p μ) :
    toLp (toSimpleFunc f) (simpleFunc.memℒp f) = f :=
  simpleFunc.eq' (Classical.choose_spec f.2)
#align measure_theory.Lp.simple_func.to_Lp_to_simple_func MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc

theorem toSimpleFunc_toLp (f : α →ₛ E) (hfi : Memℒp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f := by
  rw [← AEEqFun.mk_eq_mk]; exact Classical.choose_spec (toLp f hfi).2
                           -- 🎉 no goals
#align measure_theory.Lp.simple_func.to_simple_func_to_Lp MeasureTheory.Lp.simpleFunc.toSimpleFunc_toLp

variable (E μ)

theorem zero_toSimpleFunc : toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0 := by
  filter_upwards [toSimpleFunc_eq_toFun (0 : Lp.simpleFunc E p μ),
    Lp.coeFn_zero E 1 μ] with _ h₁ _
  rwa [h₁]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.zero_to_simple_func MeasureTheory.Lp.simpleFunc.zero_toSimpleFunc

variable {E μ}

theorem add_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f + g) =ᵐ[μ] toSimpleFunc f + toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f + g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_add (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  -- ⊢ ↑(toSimpleFunc (f + g)) a✝ = ↑(↑↑f + ↑↑g) a✝ → ↑(toSimpleFunc f) a✝ = ↑↑↑f a …
  iterate 4 intro h; rw [h]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.add_to_simple_func MeasureTheory.Lp.simpleFunc.add_toSimpleFunc

theorem neg_toSimpleFunc (f : Lp.simpleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f := by
  filter_upwards [toSimpleFunc_eq_toFun (-f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_neg (f : Lp E p μ)] with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg]
  -- ⊢ ↑(toSimpleFunc (-f)) a✝ = ↑(-↑↑f) a✝ → ↑(toSimpleFunc f) a✝ = ↑↑↑f a✝ → ↑(-↑ …
  repeat intro h; rw [h]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.neg_to_simple_func MeasureTheory.Lp.simpleFunc.neg_toSimpleFunc

theorem sub_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f - g) =ᵐ[μ] toSimpleFunc f - toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f - g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_sub (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  -- ⊢ ↑(toSimpleFunc (f - g)) a✝ = ↑(↑↑f - ↑↑g) a✝ → ↑(toSimpleFunc f) a✝ = ↑↑↑f a …
  repeat' intro h; rw [h]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.sub_to_simple_func MeasureTheory.Lp.simpleFunc.sub_toSimpleFunc

variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

set_option synthInstance.maxHeartbeats 30000 in
theorem smul_toSimpleFunc (k : 𝕜) (f : Lp.simpleFunc E p μ) :
    toSimpleFunc (k • f) =ᵐ[μ] k • ⇑(toSimpleFunc f) := by
  filter_upwards [toSimpleFunc_eq_toFun (k • f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_smul k (f : Lp E p μ)] with _
  simp only [Pi.smul_apply, coe_smul]
  -- ⊢ ↑(toSimpleFunc (k • f)) a✝ = ↑↑(k • ↑f) a✝ → ↑(toSimpleFunc f) a✝ = ↑↑↑f a✝  …
  repeat intro h; rw [h]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.smul_to_simple_func MeasureTheory.Lp.simpleFunc.smul_toSimpleFunc

theorem norm_toSimpleFunc [Fact (1 ≤ p)] (f : Lp.simpleFunc E p μ) :
    ‖f‖ = ENNReal.toReal (snorm (toSimpleFunc f) p μ) := by
  simpa [toLp_toSimpleFunc] using norm_toLp (toSimpleFunc f) (simpleFunc.memℒp f)
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.norm_to_simple_func MeasureTheory.Lp.simpleFunc.norm_toSimpleFunc

end ToSimpleFunc

section Induction

variable (p)

/-- The characteristic function of a finite-measure measurable set `s`, as an `Lp` simple function.
-/
def indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Lp.simpleFunc E p μ :=
  toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.Lp.simple_func.indicator_const MeasureTheory.Lp.simpleFunc.indicatorConst

variable {p}

@[simp]
theorem coe_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    (↑(indicatorConst p hs hμs c) : Lp E p μ) = indicatorConstLp p hs hμs c :=
  rfl
#align measure_theory.Lp.simple_func.coe_indicator_const MeasureTheory.Lp.simpleFunc.coe_indicatorConst

theorem toSimpleFunc_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    toSimpleFunc (indicatorConst p hs hμs c) =ᵐ[μ]
      (SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0) :=
  Lp.simpleFunc.toSimpleFunc_toLp _ _
#align measure_theory.Lp.simple_func.to_simple_func_indicator_const MeasureTheory.Lp.simpleFunc.toSimpleFunc_indicatorConst

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_elim]
protected theorem induction (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {P : Lp.simpleFunc E p μ → Prop}
    (h_ind :
      ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
        P (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (h_add :
      ∀ ⦃f g : α →ₛ E⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            Disjoint (support f) (support g) →
              P (Lp.simpleFunc.toLp f hf) →
                P (Lp.simpleFunc.toLp g hg) → P (Lp.simpleFunc.toLp f hf + Lp.simpleFunc.toLp g hg))
    (f : Lp.simpleFunc E p μ) : P f := by
  suffices ∀ f : α →ₛ E, ∀ hf : Memℒp f p μ, P (toLp f hf) by
    rw [← toLp_toSimpleFunc f]
    apply this
  clear f
  -- ⊢ ∀ (f : α →ₛ E) (hf : Memℒp (↑f) p), P (toLp f hf)
  apply SimpleFunc.induction
  -- ⊢ ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hf : Memℒp (↑(SimpleFunc.piece …
  · intro c s hs hf
    -- ⊢ P (toLp (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const  …
    by_cases hc : c = 0
    -- ⊢ P (toLp (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const  …
    · convert h_ind 0 MeasurableSet.empty (by simp) using 1
      -- ⊢ toLp (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0 …
      ext1
      -- ⊢ ↑(toLp (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α …
      simp [hc]
      -- 🎉 no goals
    exact h_ind c hs (SimpleFunc.measure_lt_top_of_memℒp_indicator hp_pos hp_ne_top hc hs hf)
    -- 🎉 no goals
  · intro f g hfg hf hg hfg'
    -- ⊢ P (toLp (f + g) hfg')
    obtain ⟨hf', hg'⟩ : Memℒp f p μ ∧ Memℒp g p μ :=
      (memℒp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable).mp hfg'
    exact h_add hf' hg' hfg (hf hf') (hg hg')
    -- 🎉 no goals
#align measure_theory.Lp.simple_func.induction MeasureTheory.Lp.simpleFunc.induction

end Induction

section CoeToLp

variable [Fact (1 ≤ p)]

protected theorem uniformContinuous : UniformContinuous ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  uniformContinuous_comap
#align measure_theory.Lp.simple_func.uniform_continuous MeasureTheory.Lp.simpleFunc.uniformContinuous

protected theorem uniformEmbedding : UniformEmbedding ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  uniformEmbedding_comap Subtype.val_injective
#align measure_theory.Lp.simple_func.uniform_embedding MeasureTheory.Lp.simpleFunc.uniformEmbedding

protected theorem uniformInducing : UniformInducing ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  simpleFunc.uniformEmbedding.toUniformInducing
#align measure_theory.Lp.simple_func.uniform_inducing MeasureTheory.Lp.simpleFunc.uniformInducing

protected theorem denseEmbedding (hp_ne_top : p ≠ ∞) :
    DenseEmbedding ((↑) : Lp.simpleFunc E p μ → Lp E p μ) := by
  borelize E
  -- ⊢ DenseEmbedding Subtype.val
  apply simpleFunc.uniformEmbedding.denseEmbedding
  -- ⊢ DenseRange Subtype.val
  intro f
  -- ⊢ f ∈ closure (Set.range Subtype.val)
  rw [mem_closure_iff_seq_limit]
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range Subtype.val) ∧ Tendsto x atTop (𝓝 f)
  have hfi' : Memℒp f p μ := Lp.memℒp f
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range Subtype.val) ∧ Tendsto x atTop (𝓝 f)
  haveI : SeparableSpace (range f ∪ {0} : Set E) :=
    (Lp.stronglyMeasurable f).separableSpace_range_union_singleton
  refine'
    ⟨fun n =>
      toLp
        (SimpleFunc.approxOn f (Lp.stronglyMeasurable f).measurable (range f ∪ {0}) 0 _ n)
        (SimpleFunc.memℒp_approxOn_range (Lp.stronglyMeasurable f).measurable hfi' n),
      fun n => mem_range_self _, _⟩
  convert SimpleFunc.tendsto_approxOn_range_Lp hp_ne_top (Lp.stronglyMeasurable f).measurable hfi'
  -- ⊢ f = Memℒp.toLp (↑↑f) hfi'
  rw [toLp_coeFn f (Lp.memℒp f)]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.dense_embedding MeasureTheory.Lp.simpleFunc.denseEmbedding

protected theorem denseInducing (hp_ne_top : p ≠ ∞) :
    DenseInducing ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  (simpleFunc.denseEmbedding hp_ne_top).toDenseInducing
#align measure_theory.Lp.simple_func.dense_inducing MeasureTheory.Lp.simpleFunc.denseInducing

protected theorem denseRange (hp_ne_top : p ≠ ∞) :
    DenseRange ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  (simpleFunc.denseInducing hp_ne_top).dense
#align measure_theory.Lp.simple_func.dense_range MeasureTheory.Lp.simpleFunc.denseRange

variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

variable (α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
def coeToLp : Lp.simpleFunc E p μ →L[𝕜] Lp E p μ :=
  { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl
    cont := Lp.simpleFunc.uniformContinuous.continuous }
#align measure_theory.Lp.simple_func.coe_to_Lp MeasureTheory.Lp.simpleFunc.coeToLp

variable {α E 𝕜}

end CoeToLp

section Order

variable {G : Type*} [NormedLatticeAddCommGroup G]

theorem coeFn_le (f g : Lp.simpleFunc G p μ) : (f : α → G) ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← Lp.coeFn_le]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.coe_fn_le MeasureTheory.Lp.simpleFunc.coeFn_le

instance instCovariantClassLE :
    CovariantClass (Lp.simpleFunc G p μ) (Lp.simpleFunc G p μ) (· + ·) (· ≤ ·) := by
  refine' ⟨fun f g₁ g₂ hg₁₂ => _⟩
  -- ⊢ f + g₁ ≤ f + g₂
  rw [← Lp.simpleFunc.coeFn_le] at hg₁₂ ⊢
  -- ⊢ ↑↑↑(f + g₁) ≤ᵐ[μ] ↑↑↑(f + g₂)
  have h_add_1 : ((f + g₁ : Lp.simpleFunc G p μ) : α → G) =ᵐ[μ] (f : α → G) + g₁ := Lp.coeFn_add _ _
  -- ⊢ ↑↑↑(f + g₁) ≤ᵐ[μ] ↑↑↑(f + g₂)
  have h_add_2 : ((f + g₂ : Lp.simpleFunc G p μ) : α → G) =ᵐ[μ] (f : α → G) + g₂ := Lp.coeFn_add _ _
  -- ⊢ ↑↑↑(f + g₁) ≤ᵐ[μ] ↑↑↑(f + g₂)
  filter_upwards [h_add_1, h_add_2, hg₁₂] with _ h1 h2 h3
  -- ⊢ ↑↑↑(f + g₁) a✝ ≤ ↑↑↑(f + g₂) a✝
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  -- ⊢ ↑↑↑f a✝ + ↑↑↑g₁ a✝ ≤ ↑↑↑f a✝ + ↑↑↑g₂ a✝
  exact add_le_add le_rfl h3
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.has_le.le.covariant_class MeasureTheory.Lp.simpleFunc.instCovariantClassLE

variable (p μ G)

theorem coeFn_zero : (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α → G) :=
  Lp.coeFn_zero _ _ _
#align measure_theory.Lp.simple_func.coe_fn_zero MeasureTheory.Lp.simpleFunc.coeFn_zero

variable {p μ G}

theorem coeFn_nonneg (f : Lp.simpleFunc G p μ) : (0 : α → G) ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← Subtype.coe_le_coe, Lp.coeFn_nonneg, AddSubmonoid.coe_zero]
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.coe_fn_nonneg MeasureTheory.Lp.simpleFunc.coeFn_nonneg

theorem exists_simpleFunc_nonneg_ae_eq {f : Lp.simpleFunc G p μ} (hf : 0 ≤ f) :
    ∃ f' : α →ₛ G, 0 ≤ f' ∧ f =ᵐ[μ] f' := by
  rcases f with ⟨⟨f, hp⟩, g, (rfl : _ = f)⟩
  -- ⊢ ∃ f', 0 ≤ f' ∧ ↑↑↑{ val := { val := AEEqFun.mk ↑g (_ : AEStronglyMeasurable  …
  change 0 ≤ᵐ[μ] g at hf
  -- ⊢ ∃ f', 0 ≤ f' ∧ ↑↑↑{ val := { val := AEEqFun.mk ↑g (_ : AEStronglyMeasurable  …
  refine ⟨g ⊔ 0, le_sup_right, (AEEqFun.coeFn_mk _ _).trans ?_⟩
  -- ⊢ ↑g =ᵐ[μ] ↑(g ⊔ 0)
  exact hf.mono fun x hx ↦ (sup_of_le_left hx).symm
  -- 🎉 no goals
#align measure_theory.Lp.simple_func.exists_simple_func_nonneg_ae_eq MeasureTheory.Lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq

variable (p μ G)

/-- Coercion from nonnegative simple functions of Lp to nonnegative functions of Lp. -/
def coeSimpleFuncNonnegToLpNonneg :
    { g : Lp.simpleFunc G p μ // 0 ≤ g } → { g : Lp G p μ // 0 ≤ g } := fun g => ⟨g, g.2⟩
#align measure_theory.Lp.simple_func.coe_simple_func_nonneg_to_Lp_nonneg MeasureTheory.Lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg

theorem denseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G) := fun g ↦ by
  borelize G
  -- ⊢ g ∈ closure (Set.range (coeSimpleFuncNonnegToLpNonneg p μ G))
  rw [mem_closure_iff_seq_limit]
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range (coeSimpleFuncNonnegToLpNonneg p μ G)) ∧ Te …
  have hg_memℒp : Memℒp (g : α → G) p μ := Lp.memℒp (g : Lp G p μ)
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range (coeSimpleFuncNonnegToLpNonneg p μ G)) ∧ Te …
  have zero_mem : (0 : G) ∈ (range (g : α → G) ∪ {0} : Set G) ∩ { y | 0 ≤ y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, eq_self_iff_true, true_or_iff,
      mem_setOf_eq, le_refl, and_self_iff]
  have : SeparableSpace ((range (g : α → G) ∪ {0}) ∩ { y | 0 ≤ y } : Set G) := by
    apply IsSeparable.separableSpace
    apply IsSeparable.mono _ (Set.inter_subset_left _ _)
    exact
      (Lp.stronglyMeasurable (g : Lp G p μ)).isSeparable_range.union
        (finite_singleton _).isSeparable
  have g_meas : Measurable (g : α → G) := (Lp.stronglyMeasurable (g : Lp G p μ)).measurable
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range (coeSimpleFuncNonnegToLpNonneg p μ G)) ∧ Te …
  let x n := SimpleFunc.approxOn g g_meas ((range (g : α → G) ∪ {0}) ∩ { y | 0 ≤ y }) 0 zero_mem n
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range (coeSimpleFuncNonnegToLpNonneg p μ G)) ∧ Te …
  have hx_nonneg : ∀ n, 0 ≤ x n := by
    intro n a
    change x n a ∈ { y : G | 0 ≤ y }
    have A : (range (g : α → G) ∪ {0} : Set G) ∩ { y | 0 ≤ y } ⊆ { y | 0 ≤ y } :=
      inter_subset_right _ _
    apply A
    exact SimpleFunc.approxOn_mem g_meas _ n a
  have hx_memℒp : ∀ n, Memℒp (x n) p μ :=
    SimpleFunc.memℒp_approxOn _ hg_memℒp _ ⟨aestronglyMeasurable_const, by simp⟩
  have h_toLp := fun n => Memℒp.coeFn_toLp (hx_memℒp n)
  -- ⊢ ∃ x, (∀ (n : ℕ), x n ∈ Set.range (coeSimpleFuncNonnegToLpNonneg p μ G)) ∧ Te …
  have hx_nonneg_Lp : ∀ n, 0 ≤ toLp (x n) (hx_memℒp n) := by
    intro n
    rw [← Lp.simpleFunc.coeFn_le, Lp.simpleFunc.toLp_eq_toLp]
    filter_upwards [Lp.simpleFunc.coeFn_zero p μ G, h_toLp n] with a ha0 ha_toLp
    rw [ha0, ha_toLp]
    exact hx_nonneg n a
  have hx_tendsto :
      Tendsto (fun n : ℕ => snorm ((x n : α → G) - (g : α → G)) p μ) atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_snorm g_meas zero_mem hp_ne_top
    · have hg_nonneg : (0 : α → G) ≤ᵐ[μ] g := (Lp.coeFn_nonneg _).mpr g.2
      refine' hg_nonneg.mono fun a ha => subset_closure _
      simpa using ha
    · simp_rw [sub_zero]; exact hg_memℒp.snorm_lt_top
  refine'
    ⟨fun n =>
      (coeSimpleFuncNonnegToLpNonneg p μ G) ⟨toLp (x n) (hx_memℒp n), hx_nonneg_Lp n⟩,
      fun n => mem_range_self _, _⟩
  suffices Tendsto (fun n : ℕ => (toLp (x n) (hx_memℒp n) : Lp G p μ)) atTop (𝓝 (g : Lp G p μ)) by
    rw [tendsto_iff_dist_tendsto_zero] at this ⊢
    simp_rw [Subtype.dist_eq]
    exact this
  rw [Lp.tendsto_Lp_iff_tendsto_ℒp']
  -- ⊢ Tendsto (fun n => snorm (↑↑↑(toLp (x n) (_ : Memℒp (↑(x n)) p)) - ↑↑↑g) p μ) …
  refine Filter.Tendsto.congr (fun n => snorm_congr_ae (EventuallyEq.sub ?_ ?_)) hx_tendsto
  -- ⊢ (fun x_1 => ↑(x n) x_1) =ᵐ[μ] fun x_1 => ↑↑↑(toLp (x n) (_ : Memℒp (↑(x n))  …
  · symm
    -- ⊢ (fun x_1 => ↑↑↑(toLp (x n) (_ : Memℒp (↑(x n)) p)) x_1) =ᵐ[μ] fun x_1 => ↑(x …
    rw [Lp.simpleFunc.toLp_eq_toLp]
    -- ⊢ (fun x_1 => ↑↑(Memℒp.toLp ↑(x n) (_ : Memℒp (↑(x n)) p)) x_1) =ᵐ[μ] fun x_1  …
    exact h_toLp n
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align measure_theory.Lp.simple_func.dense_range_coe_simple_func_nonneg_to_Lp_nonneg MeasureTheory.Lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg

variable {p μ G}

end Order

end simpleFunc

end Lp

variable [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {p : ℝ≥0∞} {μ : Measure α}

/-- To prove something for an arbitrary `Lp` function in a second countable Borel normed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
@[elab_as_elim]
theorem Lp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (P : Lp E p μ → Prop)
    (h_ind : ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
      P (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (h_add : ∀ ⦃f g⦄, ∀ hf : Memℒp f p μ, ∀ hg : Memℒp g p μ, Disjoint (support f) (support g) →
      P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed { f : Lp E p μ | P f }) : ∀ f : Lp E p μ, P f := by
  refine' fun f => (Lp.simpleFunc.denseRange hp_ne_top).induction_on f h_closed _
  -- ⊢ ∀ (a : { x // x ∈ ↑(simpleFunc E p μ) }), P ↑a
  refine' Lp.simpleFunc.induction (α := α) (E := E) (lt_of_lt_of_le zero_lt_one _i.elim).ne'
    hp_ne_top _ _
  · exact fun c s => h_ind c
    -- 🎉 no goals
  · exact fun f g hf hg => h_add hf hg
    -- 🎉 no goals
#align measure_theory.Lp.induction MeasureTheory.Lp.induction

/-- To prove something for an arbitrary `Memℒp` function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `Lᵖ` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_elim]
theorem Memℒp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
    (h_ind : ∀ (c : E) ⦃s⦄, MeasurableSet s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add : ∀ ⦃f g : α → E⦄, Disjoint (support f) (support g) → Memℒp f p μ → Memℒp g p μ →
      P f → P g → P (f + g))
    (h_closed : IsClosed { f : Lp E p μ | P f })
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Memℒp f p μ → P f → P g) :
    ∀ ⦃f : α → E⦄, Memℒp f p μ → P f := by
  have : ∀ f : SimpleFunc α E, Memℒp f p μ → P f := by
    apply SimpleFunc.induction
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert h_ind 0 MeasurableSet.empty (by simp) using 1; ext; simp [const]
      have hp_pos : p ≠ 0 := (lt_of_lt_of_le zero_lt_one _i.elim).ne'
      exact h_ind c hs (SimpleFunc.measure_lt_top_of_memℒp_indicator hp_pos hp_ne_top hc hs h)
    · intro f g hfg hf hg int_fg
      rw [SimpleFunc.coe_add,
        memℒp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable] at int_fg
      refine' h_add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2)
  have : ∀ f : Lp.simpleFunc E p μ, P f := by
    intro f
    exact
      h_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f) (Lp.simpleFunc.memℒp f)
        (this (Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.memℒp f))
  have : ∀ f : Lp E p μ, P f := fun f =>
    (Lp.simpleFunc.denseRange hp_ne_top).induction_on f h_closed this
  exact fun f hf => h_ae hf.coeFn_toLp (Lp.memℒp _) (this (hf.toLp f))
  -- 🎉 no goals
#align measure_theory.mem_ℒp.induction MeasureTheory.Memℒp.induction

/-- If a set of ae strongly measurable functions is stable under addition and approximates
characteristic functions in `ℒp`, then it is dense in `ℒp`. -/
theorem Memℒp.induction_dense (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
    (h0P :
      ∀ (c : E) ⦃s : Set α⦄,
        MeasurableSet s →
          μ s < ∞ →
            ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : α → E, snorm (g - s.indicator fun _ => c) p μ ≤ ε ∧ P g)
    (h1P : ∀ f g, P f → P g → P (f + g)) (h2P : ∀ f, P f → AEStronglyMeasurable f μ) {f : α → E}
    (hf : Memℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : α → E, snorm (f - g) p μ ≤ ε ∧ P g := by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  -- ⊢ ∃ g, snorm (f - g) 0 μ ≤ ε ∧ P g
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, WithTop.zero_lt_top])
        hε with ⟨g, _, Pg⟩
    exact ⟨g, by simp only [snorm_exponent_zero, zero_le'], Pg⟩
    -- 🎉 no goals
  suffices H :
    ∀ (f' : α →ₛ E) (δ : ℝ≥0∞) (hδ : δ ≠ 0), Memℒp f' p μ → ∃ g, snorm (⇑f' - g) p μ ≤ δ ∧ P g
  · obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p hε
    -- ⊢ ∃ g, snorm (f - g) p μ ≤ ε ∧ P g
    rcases hf.exists_simpleFunc_snorm_sub_lt hp_ne_top ηpos.ne' with ⟨f', hf', f'_mem⟩
    -- ⊢ ∃ g, snorm (f - g) p μ ≤ ε ∧ P g
    rcases H f' η ηpos.ne' f'_mem with ⟨g, hg, Pg⟩
    -- ⊢ ∃ g, snorm (f - g) p μ ≤ ε ∧ P g
    refine' ⟨g, _, Pg⟩
    -- ⊢ snorm (f - g) p μ ≤ ε
    convert (hη _ _ (hf.aestronglyMeasurable.sub f'.aestronglyMeasurable)
          (f'.aestronglyMeasurable.sub (h2P g Pg)) hf'.le hg).le using 2
    simp only [sub_add_sub_cancel]
    -- 🎉 no goals
  apply SimpleFunc.induction
  -- ⊢ ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (δ : ℝ≥0∞), δ ≠ 0 → Memℒp (↑(Si …
  · intro c s hs ε εpos Hs
    -- ⊢ ∃ g, snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.c …
    rcases eq_or_ne c 0 with (rfl | hc)
    -- ⊢ ∃ g, snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α 0) (SimpleFunc.c …
    · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, WithTop.zero_lt_top])
          εpos with ⟨g, hg, Pg⟩
      rw [← snorm_neg, neg_sub] at hg
      -- ⊢ ∃ g, snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α 0) (SimpleFunc.c …
      refine' ⟨g, _, Pg⟩
      -- ⊢ snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α 0) (SimpleFunc.const  …
      convert hg
      -- ⊢ ↑(SimpleFunc.piecewise s hs (SimpleFunc.const α 0) (SimpleFunc.const α 0)) = …
      ext x
      -- ⊢ ↑(SimpleFunc.piecewise s hs (SimpleFunc.const α 0) (SimpleFunc.const α 0)) x …
      simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_zero,
        piecewise_eq_indicator, indicator_zero', Pi.zero_apply, indicator_zero]
    · have : μ s < ∞ := SimpleFunc.measure_lt_top_of_memℒp_indicator hp_pos hp_ne_top hc hs Hs
      -- ⊢ ∃ g, snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.c …
      rcases h0P c hs this εpos with ⟨g, hg, Pg⟩
      -- ⊢ ∃ g, snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.c …
      rw [← snorm_neg, neg_sub] at hg
      -- ⊢ ∃ g, snorm (↑(SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.c …
      exact ⟨g, hg, Pg⟩
      -- 🎉 no goals
  · intro f f' hff' hf hf' δ δpos int_ff'
    -- ⊢ ∃ g, snorm (↑(f + f') - g) p μ ≤ δ ∧ P g
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p δpos
    -- ⊢ ∃ g, snorm (↑(f + f') - g) p μ ≤ δ ∧ P g
    rw [SimpleFunc.coe_add,
      memℒp_add_of_disjoint hff' f.stronglyMeasurable f'.stronglyMeasurable] at int_ff'
    rcases hf η ηpos.ne' int_ff'.1 with ⟨g, hg, Pg⟩
    -- ⊢ ∃ g, snorm (↑(f + f') - g) p μ ≤ δ ∧ P g
    rcases hf' η ηpos.ne' int_ff'.2 with ⟨g', hg', Pg'⟩
    -- ⊢ ∃ g, snorm (↑(f + f') - g) p μ ≤ δ ∧ P g
    refine' ⟨g + g', _, h1P g g' Pg Pg'⟩
    -- ⊢ snorm (↑(f + f') - (g + g')) p μ ≤ δ
    convert (hη _ _ (f.aestronglyMeasurable.sub (h2P g Pg))
          (f'.aestronglyMeasurable.sub (h2P g' Pg')) hg hg').le using 2
    rw [SimpleFunc.coe_add]
    -- ⊢ ↑f + ↑f' - (g + g') = ↑f - g + (↑f' - g')
    abel
    -- 🎉 no goals
    -- 🎉 no goals
#align measure_theory.mem_ℒp.induction_dense MeasureTheory.Memℒp.induction_dense

section Integrable

-- mathport name: «expr →₁ₛ[ ] »
@[inherit_doc MeasureTheory.Lp.simpleFunc]
notation:25 α " →₁ₛ[" μ "] " E => @MeasureTheory.Lp.simpleFunc α E _ _ 1 μ

theorem L1.SimpleFunc.toLp_one_eq_toL1 (f : α →ₛ E) (hf : Integrable f μ) :
    (Lp.simpleFunc.toLp f (memℒp_one_iff_integrable.2 hf) : α →₁[μ] E) = hf.toL1 f :=
  rfl
#align measure_theory.L1.simple_func.to_Lp_one_eq_to_L1 MeasureTheory.L1.SimpleFunc.toLp_one_eq_toL1

protected theorem L1.SimpleFunc.integrable (f : α →₁ₛ[μ] E) :
    Integrable (Lp.simpleFunc.toSimpleFunc f) μ := by
  rw [← memℒp_one_iff_integrable]; exact Lp.simpleFunc.memℒp f
  -- ⊢ Memℒp (↑(Lp.simpleFunc.toSimpleFunc f)) 1
                                   -- 🎉 no goals
#align measure_theory.L1.simple_func.integrable MeasureTheory.L1.SimpleFunc.integrable

/-- To prove something for an arbitrary integrable function in a normed group,
it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_elim]
theorem Integrable.induction (P : (α → E) → Prop)
    (h_ind : ∀ (c : E) ⦃s⦄, MeasurableSet s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add :
      ∀ ⦃f g : α → E⦄,
        Disjoint (support f) (support g) → Integrable f μ → Integrable g μ → P f → P g → P (f + g))
    (h_closed : IsClosed { f : α →₁[μ] E | P f })
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Integrable f μ → P f → P g) :
    ∀ ⦃f : α → E⦄, Integrable f μ → P f := by
  simp only [← memℒp_one_iff_integrable] at *
  -- ⊢ ∀ ⦃f : α → E⦄, Memℒp f 1 → P f
  exact Memℒp.induction one_ne_top (P := P) h_ind h_add h_closed h_ae
  -- 🎉 no goals
#align measure_theory.integrable.induction MeasureTheory.Integrable.induction

end Integrable

end MeasureTheory
