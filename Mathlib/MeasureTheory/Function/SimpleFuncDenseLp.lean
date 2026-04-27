/-
Copyright (c) 2022 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.Lp.simpleFunc`, the type of `Lp` simple functions
* `coeToLp`, the embedding of `Lp.simpleFunc E p μ` into `Lp E p μ`

## Main results

* `tendsto_approxOn_Lp_eLpNorm` (Lᵖ convergence): If `E` is a `NormedAddCommGroup` and `f` is
  measurable and `MemLp` (for `p < ∞`), then the simple functions
  `SimpleFunc.approxOn f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simpleFunc.isDenseEmbedding`: the embedding `coeToLp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simpleFunc.induction`, `Lp.induction`, `MemLp.induction`, `Integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/

@[expose] public section


noncomputable section


open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open scoped Topology ENNReal MeasureTheory

variable {α β ι E F 𝕜 : Type*}

namespace MeasureTheory

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
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact mod_cast this

theorem norm_approxOn_y₀_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using edist_approxOn_y0_le hf h₀ x n

theorem norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    (h₀ : (0 : E) ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s 0 h₀ n x‖ ≤ ‖f x‖ + ‖f x‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using edist_approxOn_y0_le hf h₀ x n

theorem tendsto_approxOn_Lp_eLpNorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (hp_ne_top : p ≠ ∞) {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : eLpNorm (fun x => f x - y₀) p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0) := by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, eLpNorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  suffices Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) by
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_ne_top]
    convert continuous_rpow_const.continuousAt.tendsto.comp this
    simp [zero_rpow_of_pos (_root_.inv_pos.mpr hp)]
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas n : Measurable fun x => ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal := by
    simpa only [← edist_eq_enorm_sub] using
      (approxOn f hf s y₀ h₀ n).measurable_bind (fun y x => edist y (f x) ^ p.toReal) fun y =>
        (measurable_edist_right.comp hf).pow_const p.toReal
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `fun x => ‖f x - y₀‖ ^ p.toReal`
  have h_bound n :
    (fun x ↦ ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal) ≤ᵐ[μ] (‖f · - y₀‖ₑ ^ p.toReal) :=
    .of_forall fun x => rpow_le_rpow (coe_mono (nnnorm_approxOn_le hf h₀ x n)) toReal_nonneg
  -- (3) The bounding function `fun x => ‖f x - y₀‖ ^ p.toReal` has finite integral
  have h_fin : (∫⁻ a : β, ‖f a - y₀‖ₑ ^ p.toReal ∂μ) ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_ne_top hi).ne
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim :
    ∀ᵐ a : β ∂μ, Tendsto (‖approxOn f hf s y₀ h₀ · a - f a‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [hμ] with a ha
    have : Tendsto (fun n => (approxOn f hf s y₀ h₀ n) a - f a) atTop (𝓝 (f a - f a)) :=
      (tendsto_approxOn hf h₀ ha).sub tendsto_const_nhds
    convert continuous_rpow_const.continuousAt.tendsto.comp (tendsto_coe.mpr this.nnnorm)
    simp [zero_rpow_of_pos hp]
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim

theorem memLp_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : MemLp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : MemLp (fun _ => y₀) p μ) (n : ℕ) : MemLp (approxOn f fmeas s y₀ h₀ n) p μ := by
  refine ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, ?_⟩
  suffices eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : MemLp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert eLpNorm_add_lt_top this hi₀
    ext x
    simp
  have hf' : MemLp (fun x => ‖f x - y₀‖) p μ := by
    have h_meas : Measurable fun x => ‖f x - y₀‖ := by
      simp only [← dist_eq_norm]
      fun_prop
    refine ⟨h_meas.aemeasurable.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    convert eLpNorm_add_lt_top hf hi₀.neg with x
    simp [sub_eq_add_neg]
  have : ∀ᵐ x ∂μ, ‖approxOn f fmeas s y₀ h₀ n x - y₀‖ ≤ ‖‖f x - y₀‖ + ‖f x - y₀‖‖ := by
    filter_upwards with x
    convert norm_approxOn_y₀_le fmeas h₀ x n using 1
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  calc
    eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ ≤
        eLpNorm (fun x => ‖f x - y₀‖ + ‖f x - y₀‖) p μ :=
      eLpNorm_mono_ae this
    _ < ⊤ := eLpNorm_add_lt_top hf' hf'

theorem tendsto_approxOn_range_Lp_eLpNorm [BorelSpace E] {f : β → E} (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : eLpNorm f p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) - f) p μ)
      atTop (𝓝 0) := by
  refine tendsto_approxOn_Lp_eLpNorm fmeas _ hp_ne_top ?_ ?_
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf

theorem memLp_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : MemLp f p μ) (n : ℕ) :
    MemLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) p μ :=
  memLp_approxOn fmeas hf (y₀ := 0) (by simp) MemLp.zero n

theorem tendsto_approxOn_range_Lp [BorelSpace E] {f : β → E} [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : MemLp f p μ) :
    Tendsto
      (fun n =>
        (memLp_approxOn_range fmeas hf n).toLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n))
      atTop (𝓝 (hf.toLp f)) := by
  simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] using
    tendsto_approxOn_range_Lp_eLpNorm hp_ne_top fmeas hf.2

/-- Any function in `ℒp` can be approximated by a simple function if `p < ∞`. -/
theorem _root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt {E : Type*}
    [NormedAddCommGroup E] {f : β → E} {μ : Measure β} (hf : MemLp f p μ) (hp_ne_top : p ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : β →ₛ E, eLpNorm (f - ⇑g) p μ < ε ∧ MemLp g p μ := by
  borelize E
  let f' := hf.1.mk f
  rsuffices ⟨g, hg, g_mem⟩ : ∃ g : β →ₛ E, eLpNorm (f' - ⇑g) p μ < ε ∧ MemLp g p μ
  · refine ⟨g, ?_, g_mem⟩
    suffices eLpNorm (f - ⇑g) p μ = eLpNorm (f' - ⇑g) p μ by rwa [this]
    apply eLpNorm_congr_ae
    filter_upwards [hf.1.ae_eq_mk] with x hx
    simpa only [Pi.sub_apply, sub_left_inj] using hx
  have hf' : MemLp f' p μ := hf.ae_eq hf.1.ae_eq_mk
  have f'meas : Measurable f' := hf.1.measurable_mk
  have : SeparableSpace (range f' ∪ {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hf.1.stronglyMeasurable_mk
  rcases ((tendsto_approxOn_range_Lp_eLpNorm hp_ne_top f'meas hf'.2).eventually <|
    gt_mem_nhds hε.bot_lt).exists with ⟨n, hn⟩
  rw [← eLpNorm_neg, neg_sub] at hn
  exact ⟨_, hn, memLp_approxOn_range f'meas hf' _⟩

end Lp

/-! ### L1 approximation by simple functions -/


section Integrable

variable [MeasurableSpace β]
variable [MeasurableSpace E] [NormedAddCommGroup E]

theorem tendsto_approxOn_L1_enorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : HasFiniteIntegral (fun x => f x - y₀) μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
  simpa [eLpNorm_one_eq_lintegral_enorm] using
    tendsto_approxOn_Lp_eLpNorm hf h₀ one_ne_top hμ
      (by simpa [eLpNorm_one_eq_lintegral_enorm] using hi)

theorem integrable_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Integrable (fun _ => y₀) μ) (n : ℕ) : Integrable (approxOn f fmeas s y₀ h₀ n) μ := by
  rw [← memLp_one_iff_integrable] at hf hi₀ ⊢
  exact memLp_approxOn fmeas hf h₀ hi₀ n

theorem tendsto_approxOn_range_L1_enorm [OpensMeasurableSpace E] {f : β → E} {μ : Measure β}
    [SeparableSpace (range f ∪ {0} : Set E)] (fmeas : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ₑ ∂μ) atTop
      (𝓝 0) := by
  apply tendsto_approxOn_L1_enorm fmeas
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf.2

theorem integrable_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Integrable f μ) (n : ℕ) :
    Integrable (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) μ :=
  integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n

end Integrable

section SimpleFuncProperties

variable [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {μ : Measure α} {p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `MemLp f 0 μ` and `MemLp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `MemLp f p μ ↔ Integrable f μ ↔ f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞`.
-/


theorem exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  exists_forall_le (f.map fun x => ‖x‖)

theorem memLp_zero (f : α →ₛ E) (μ : Measure α) : MemLp f 0 μ :=
  memLp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable

theorem memLp_top (f : α →ₛ E) (μ : Measure α) : MemLp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  memLp_top_of_bound f.aestronglyMeasurable C <| Eventually.of_forall hfC

protected theorem eLpNorm'_eq {p : ℝ} (f : α →ₛ F) (μ : Measure α) :
    eLpNorm' f p μ = (∑ y ∈ f.range, ‖y‖ₑ ^ p * μ (f ⁻¹' {y})) ^ (1 / p) := by
  have h_map : (‖f ·‖ₑ ^ p) = f.map (‖·‖ₑ ^ p) := by simp; rfl
  rw [eLpNorm'_eq_lintegral_enorm, h_map, lintegral_eq_lintegral, map_lintegral]

theorem measure_preimage_lt_top_of_memLp (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) (f : α →ₛ E)
    (hf : MemLp f p μ) (y : E) (hy_ne : y ≠ 0) : μ (f ⁻¹' {y}) < ∞ := by
  have hp_pos_real : 0 < p.toReal := ENNReal.toReal_pos hp_pos hp_ne_top
  have hf_eLpNorm := MemLp.eLpNorm_lt_top hf
  rw [eLpNorm_eq_eLpNorm' hp_pos hp_ne_top, f.eLpNorm'_eq, one_div,
    ← @ENNReal.lt_rpow_inv_iff _ _ p.toReal⁻¹ (by simp [hp_pos_real]),
    @ENNReal.top_rpow_of_pos p.toReal⁻¹⁻¹ (by simp [hp_pos_real]),
    ENNReal.sum_lt_top] at hf_eLpNorm
  by_cases hyf : y ∈ f.range
  swap
  · suffices h_empty : f ⁻¹' {y} = ∅ by
      rw [h_empty, measure_empty]; exact ENNReal.coe_lt_top
    exact (preimage_eq_empty_iff _ _).mpr hyf
  specialize hf_eLpNorm y hyf
  rw [ENNReal.mul_lt_top_iff] at hf_eLpNorm
  cases hf_eLpNorm with
  | inl hf_eLpNorm => exact hf_eLpNorm.2
  | inr hf_eLpNorm =>
    cases hf_eLpNorm with
    | inl hf_eLpNorm =>
      refine absurd ?_ hy_ne
      simpa [hp_pos_real] using hf_eLpNorm
    | inr hf_eLpNorm => simp [hf_eLpNorm]

theorem memLp_of_finite_measure_preimage (p : ℝ≥0∞) {f : α →ₛ E}
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) : MemLp f p μ := by
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]; exact f.aestronglyMeasurable
  by_cases hp_top : p = ∞
  · rw [hp_top]; exact memLp_top f μ
  refine ⟨f.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top, f.eLpNorm'_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by simp) (ENNReal.sum_lt_top.mpr fun y _ => ?_).ne
  by_cases hy0 : y = 0
  · simp [hy0, ENNReal.toReal_pos hp0 hp_top]
  · refine ENNReal.mul_lt_top ?_ (hf y hy0)
    exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top

theorem memLp_iff {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp f p μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ :=
  ⟨fun h => measure_preimage_lt_top_of_memLp hp_pos hp_ne_top f h, fun h =>
    memLp_of_finite_measure_preimage p h⟩

theorem integrable_iff {f : α →ₛ E} : Integrable f μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ :=
  memLp_one_iff_integrable.symm.trans <| memLp_iff one_ne_zero ENNReal.coe_ne_top

theorem memLp_iff_integrable {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp f p μ ↔ Integrable f μ :=
  (memLp_iff hp_pos hp_ne_top).trans integrable_iff.symm

theorem memLp_iff_finMeasSupp {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp f p μ ↔ f.FinMeasSupp μ :=
  (memLp_iff hp_pos hp_ne_top).trans finMeasSupp_iff.symm

theorem integrable_iff_finMeasSupp {f : α →ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ :=
  integrable_iff.trans finMeasSupp_iff.symm

theorem FinMeasSupp.integrable {f : α →ₛ E} (h : f.FinMeasSupp μ) : Integrable f μ :=
  integrable_iff_finMeasSupp.2 h

theorem integrable_pair {f : α →ₛ E} {g : α →ₛ F} :
    Integrable f μ → Integrable g μ → Integrable (pair f g) μ := by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair

theorem memLp_of_isFiniteMeasure (f : α →ₛ E) (p : ℝ≥0∞) (μ : Measure α) [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  MemLp.of_bound f.aestronglyMeasurable C <| Eventually.of_forall hfC

@[fun_prop]
theorem integrable_of_isFiniteMeasure [IsFiniteMeasure μ] (f : α →ₛ E) : Integrable f μ :=
  memLp_one_iff_integrable.mp (f.memLp_of_isFiniteMeasure 1 μ)

theorem measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) {x : E}
    (hx : x ≠ 0) : μ (f ⁻¹' {x}) < ∞ :=
  integrable_iff.mp hf x hx

theorem measure_support_lt_top_of_memLp (f : α →ₛ E) (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : μ (support f) < ∞ :=
  f.measure_support_lt_top ((memLp_iff hp_ne_zero hp_ne_top).mp hf)

theorem measure_support_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) :
    μ (support f) < ∞ :=
  f.measure_support_lt_top (integrable_iff.mp hf)

theorem measure_lt_top_of_memLp_indicator (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {c : E} (hc : c ≠ 0)
    {s : Set α} (hs : MeasurableSet s) (hcs : MemLp ((const α c).piecewise s hs (const α 0)) p μ) :
    μ s < ⊤ := by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  simpa only [memLp_iff_finMeasSupp hp_pos hp_ne_top, finMeasSupp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs

end SimpleFuncProperties

end SimpleFunc

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/


namespace Lp

open AEEqFun

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (p : ℝ≥0∞)
  (μ : Measure α)

variable (E)

/-- `Lp.simpleFunc` is a subspace of Lp consisting of equivalence classes of an integrable simple
function. -/
def simpleFunc : AddSubgroup (Lp E p μ) where
  carrier := { f : Lp E p μ | ∃ s : α →ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α →ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro f ⟨s, hs⟩
    use -s
    simp only [← hs, AEEqFun.neg_mk, SimpleFunc.coe_neg, AddSubgroup.coe_neg]

variable {E p μ}

namespace simpleFunc

section Instances

/-! Simple functions in Lp space form a `NormedSpace`. -/



protected theorem eq' {f g : Lp.simpleFunc E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
  Subtype.ext ∘ Subtype.ext

/-! Implementation note:  If `Lp.simpleFunc E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simpleFunc E p μ`, would be
unnecessary.  But instead, `Lp.simpleFunc E p μ` is defined as an `AddSubgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a `SMul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
protected def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩

attribute [local instance] simpleFunc.smul

@[simp, norm_cast]
theorem coe_smul (c : 𝕜) (f : Lp.simpleFunc E p μ) :
    ((c • f : Lp.simpleFunc E p μ) : Lp E p μ) = c • (f : Lp E p μ) :=
  rfl

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
protected def module : Module 𝕜 (Lp.simpleFunc E p μ) where
  one_smul f := by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _

attribute [local instance] simpleFunc.module

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected theorem isBoundedSMul [Fact (1 ≤ p)] : IsBoundedSMul 𝕜 (Lp.simpleFunc E p μ) :=
  IsBoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : Lp E p μ) :)

attribute [local instance] simpleFunc.isBoundedSMul

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
protected def normedSpace {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩

end Instances

attribute [local instance] simpleFunc.module simpleFunc.normedSpace simpleFunc.isBoundedSMul

section ToLp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `MemLp`. -/
abbrev toLp (f : α →ₛ E) (hf : MemLp f p μ) : Lp.simpleFunc E p μ :=
  ⟨hf.toLp f, ⟨f, rfl⟩⟩

theorem toLp_eq_toLp (f : α →ₛ E) (hf : MemLp f p μ) : (toLp f hf : Lp E p μ) = hf.toLp f :=
  rfl

theorem toLp_eq_mk (f : α →ₛ E) (hf : MemLp f p μ) :
    (toLp f hf : α →ₘ[μ] E) = AEEqFun.mk f f.aestronglyMeasurable :=
  rfl

theorem toLp_zero : toLp (0 : α →ₛ E) MemLp.zero = (0 : Lp.simpleFunc E p μ) :=
  rfl

theorem toLp_add (f g : α →ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    toLp (f + g) (hf.add hg) = toLp f hf + toLp g hg :=
  rfl

theorem toLp_neg (f : α →ₛ E) (hf : MemLp f p μ) : toLp (-f) hf.neg = -toLp f hf :=
  rfl

theorem toLp_sub (f g : α →ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    toLp (f - g) (hf.sub hg) = toLp f hf - toLp g hg := by
  simp only [sub_eq_add_neg, ← toLp_neg, ← toLp_add]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

theorem toLp_smul (f : α →ₛ E) (hf : MemLp f p μ) (c : 𝕜) :
    toLp (c • f) (hf.const_smul c) = c • toLp f hf :=
  rfl

nonrec theorem norm_toLp [Fact (1 ≤ p)] (f : α →ₛ E) (hf : MemLp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ) :=
  norm_toLp f hf

end ToLp

section ToSimpleFunc

/-- Find a representative of a `Lp.simpleFunc`. -/
def toSimpleFunc (f : Lp.simpleFunc E p μ) : α →ₛ E :=
  Classical.choose f.2

/-- `(toSimpleFunc f)` is measurable. -/
@[fun_prop]
protected theorem measurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    Measurable (toSimpleFunc f) :=
  (toSimpleFunc f).measurable

protected theorem stronglyMeasurable (f : Lp.simpleFunc E p μ) :
    StronglyMeasurable (toSimpleFunc f) :=
  (toSimpleFunc f).stronglyMeasurable

@[fun_prop]
protected theorem aemeasurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    AEMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.measurable f).aemeasurable

protected theorem aestronglyMeasurable (f : Lp.simpleFunc E p μ) :
    AEStronglyMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.stronglyMeasurable f).aestronglyMeasurable

theorem toSimpleFunc_eq_toFun (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f :=
  show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α →ₘ[μ] E) by
    convert (AEEqFun.coeFn_mk (toSimpleFunc f)
          (toSimpleFunc f).aestronglyMeasurable).symm using 2
    exact (Classical.choose_spec f.2).symm

/-- `toSimpleFunc f` satisfies the predicate `MemLp`. -/
protected theorem memLp (f : Lp.simpleFunc E p μ) : MemLp (toSimpleFunc f) p μ :=
  MemLp.ae_eq (toSimpleFunc_eq_toFun f).symm <| mem_Lp_iff_memLp.mp (f : Lp E p μ).2

theorem toLp_toSimpleFunc (f : Lp.simpleFunc E p μ) :
    toLp (toSimpleFunc f) (simpleFunc.memLp f) = f :=
  simpleFunc.eq' (Classical.choose_spec f.2)

theorem toSimpleFunc_toLp (f : α →ₛ E) (hfi : MemLp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f := by
  rw [← AEEqFun.mk_eq_mk]; exact Classical.choose_spec (toLp f hfi).2

variable (E μ)

theorem zero_toSimpleFunc : toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0 := by
  filter_upwards [toSimpleFunc_eq_toFun (0 : Lp.simpleFunc E p μ),
    Lp.coeFn_zero E 1 μ] with _ h₁ _
  rwa [h₁]

variable {E μ}

theorem add_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f + g) =ᵐ[μ] toSimpleFunc f + toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f + g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_add (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  iterate 4 intro h; rw [h]

theorem neg_toSimpleFunc (f : Lp.simpleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f := by
  filter_upwards [toSimpleFunc_eq_toFun (-f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_neg (f : Lp E p μ)] with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg]
  repeat intro h; rw [h]

theorem sub_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f - g) =ᵐ[μ] toSimpleFunc f - toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f - g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_sub (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  repeat' intro h; rw [h]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

theorem smul_toSimpleFunc (k : 𝕜) (f : Lp.simpleFunc E p μ) :
    toSimpleFunc (k • f) =ᵐ[μ] k • ⇑(toSimpleFunc f) := by
  filter_upwards [toSimpleFunc_eq_toFun (k • f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_smul k (f : Lp E p μ)] with _
  simp only [Pi.smul_apply, coe_smul]
  repeat intro h; rw [h]

theorem norm_toSimpleFunc [Fact (1 ≤ p)] (f : Lp.simpleFunc E p μ) :
    ‖f‖ = ENNReal.toReal (eLpNorm (toSimpleFunc f) p μ) := by
  simpa [toLp_toSimpleFunc] using norm_toLp (toSimpleFunc f) (simpleFunc.memLp f)

end ToSimpleFunc

section Induction

variable (p) in
/-- The characteristic function of a finite-measure measurable set `s`, as an `Lp` simple function.
-/
def indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Lp.simpleFunc E p μ :=
  toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memLp_indicator_const p hs c (Or.inr hμs))

@[simp]
theorem coe_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    (↑(indicatorConst p hs hμs c) : Lp E p μ) = indicatorConstLp p hs hμs c :=
  rfl

theorem toSimpleFunc_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    toSimpleFunc (indicatorConst p hs hμs c) =ᵐ[μ]
      (SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0) :=
  Lp.simpleFunc.toSimpleFunc_toLp _ _

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_elim]
protected theorem induction (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {P : Lp.simpleFunc E p μ → Prop}
    (indicatorConst :
      ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
        P (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (add :
      ∀ ⦃f g : α →ₛ E⦄,
        ∀ hf : MemLp f p μ,
          ∀ hg : MemLp g p μ,
            Disjoint (support f) (support g) →
              P (Lp.simpleFunc.toLp f hf) →
                P (Lp.simpleFunc.toLp g hg) → P (Lp.simpleFunc.toLp f hf + Lp.simpleFunc.toLp g hg))
    (f : Lp.simpleFunc E p μ) : P f := by
  suffices ∀ f : α →ₛ E, ∀ hf : MemLp f p μ, P (toLp f hf) by
    rw [← toLp_toSimpleFunc f]
    apply this
  clear f
  apply SimpleFunc.induction
  · intro c s hs hf
    by_cases hc : c = 0
    · convert indicatorConst 0 MeasurableSet.empty (by simp) using 1
      ext1
      simp [hc]
    exact indicatorConst c hs
      (SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs hf)
  · intro f g hfg hf hg hfg'
    obtain ⟨hf', hg'⟩ : MemLp f p μ ∧ MemLp g p μ :=
      (memLp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable).mp hfg'
    exact add hf' hg' hfg (hf hf') (hg hg')

end Induction

section CoeToLp

variable [Fact (1 ≤ p)]

protected theorem uniformContinuous : UniformContinuous ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  uniformContinuous_comap

lemma isUniformEmbedding : IsUniformEmbedding ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  isUniformEmbedding_comap Subtype.val_injective

theorem isUniformInducing : IsUniformInducing ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  simpleFunc.isUniformEmbedding.isUniformInducing

lemma isDenseEmbedding (hp_ne_top : p ≠ ∞) :
    IsDenseEmbedding ((↑) : Lp.simpleFunc E p μ → Lp E p μ) := by
  borelize E
  apply simpleFunc.isUniformEmbedding.isDenseEmbedding
  intro f
  rw [mem_closure_iff_seq_limit]
  have hfi' : MemLp f p μ := Lp.memLp f
  haveI : SeparableSpace (range f ∪ {0} : Set E) :=
    (Lp.stronglyMeasurable f).separableSpace_range_union_singleton
  refine
    ⟨fun n =>
      toLp
        (SimpleFunc.approxOn f (Lp.stronglyMeasurable f).measurable (range f ∪ {0}) 0 _ n)
        (SimpleFunc.memLp_approxOn_range (Lp.stronglyMeasurable f).measurable hfi' n),
      fun n => mem_range_self _, ?_⟩
  convert SimpleFunc.tendsto_approxOn_range_Lp hp_ne_top (Lp.stronglyMeasurable f).measurable hfi'
  rw [toLp_coeFn f (Lp.memLp f)]

protected theorem isDenseInducing (hp_ne_top : p ≠ ∞) :
    IsDenseInducing ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  (simpleFunc.isDenseEmbedding hp_ne_top).isDenseInducing

protected theorem denseRange (hp_ne_top : p ≠ ∞) :
    DenseRange ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  (simpleFunc.isDenseInducing hp_ne_top).dense

protected theorem dense (hp_ne_top : p ≠ ∞) : Dense (Lp.simpleFunc E p μ : Set (Lp E p μ)) := by
  simpa only [denseRange_subtype_val] using simpleFunc.denseRange (E := E) (μ := μ) hp_ne_top

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable (α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
def coeToLp : Lp.simpleFunc E p μ →L[𝕜] Lp E p μ :=
  { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl
    cont := Lp.simpleFunc.uniformContinuous.continuous }

end CoeToLp

section Order

variable {G : Type*} [NormedAddCommGroup G]

theorem coeFn_le [PartialOrder G] (f g : Lp.simpleFunc G p μ) : (f : α → G) ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← Lp.coeFn_le]

variable (p μ G)

theorem coeFn_zero : (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α → G) :=
  Lp.coeFn_zero _ _ _

variable {p μ G}

variable [PartialOrder G]

theorem coeFn_nonneg (f : Lp.simpleFunc G p μ) : (0 : α → G) ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← Subtype.coe_le_coe, Lp.coeFn_nonneg, AddSubmonoid.coe_zero]

theorem exists_simpleFunc_nonneg_ae_eq {f : Lp.simpleFunc G p μ} (hf : 0 ≤ f) :
    ∃ f' : α →ₛ G, 0 ≤ f' ∧ f =ᵐ[μ] f' := by
  rcases f with ⟨⟨f, hp⟩, g, (rfl : _ = f)⟩
  change 0 ≤ᵐ[μ] g at hf
  classical
  refine ⟨g.map ({x : G | 0 ≤ x}.piecewise id 0), fun x ↦ ?_, (AEEqFun.coeFn_mk _ _).trans ?_⟩
  · simpa using Set.indicator_apply_nonneg id
  · filter_upwards [hf] with x (hx : 0 ≤ g x)
    simpa using Set.indicator_of_mem hx id |>.symm

variable (p μ G)

/-- Coercion from nonnegative simple functions of Lp to nonnegative functions of Lp. -/
def coeSimpleFuncNonnegToLpNonneg :
    { g : Lp.simpleFunc G p μ // 0 ≤ g } → { g : Lp G p μ // 0 ≤ g } := fun g => ⟨g, g.2⟩

theorem denseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G) := fun g ↦ by
  borelize G
  rw [mem_closure_iff_seq_limit]
  have hg_memLp : MemLp (g : α → G) p μ := Lp.memLp (g : Lp G p μ)
  have zero_mem : (0 : G) ∈ (range (g : α → G) ∪ {0} : Set G) ∩ { y | 0 ≤ y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, true_or,
      mem_setOf_eq, le_refl, and_self_iff]
  have : SeparableSpace ((range (g : α → G) ∪ {0}) ∩ { y | 0 ≤ y } : Set G) := by
    apply IsSeparable.separableSpace
    apply IsSeparable.mono _ Set.inter_subset_left
    exact
      (Lp.stronglyMeasurable (g : Lp G p μ)).isSeparable_range.union
        (finite_singleton _).isSeparable
  have g_meas : Measurable (g : α → G) := (Lp.stronglyMeasurable (g : Lp G p μ)).measurable
  let x n := SimpleFunc.approxOn (g : α → G) g_meas
    ((range (g : α → G) ∪ {0}) ∩ { y | 0 ≤ y }) 0 zero_mem n
  have hx_nonneg : ∀ n, 0 ≤ x n := by
    intro n a
    change x n a ∈ { y : G | 0 ≤ y }
    have A : (range (g : α → G) ∪ {0} : Set G) ∩ { y | 0 ≤ y } ⊆ { y | 0 ≤ y } :=
      inter_subset_right
    apply A
    exact SimpleFunc.approxOn_mem g_meas _ n a
  have hx_memLp : ∀ n, MemLp (x n) p μ :=
    SimpleFunc.memLp_approxOn _ hg_memLp _ ⟨aestronglyMeasurable_const, by simp⟩
  have h_toLp := fun n => MemLp.coeFn_toLp (hx_memLp n)
  have hx_nonneg_Lp : ∀ n, 0 ≤ toLp (x n) (hx_memLp n) := by
    intro n
    rw [← Lp.simpleFunc.coeFn_le, Lp.simpleFunc.toLp_eq_toLp]
    filter_upwards [Lp.simpleFunc.coeFn_zero p μ G, h_toLp n] with a ha0 ha_toLp
    rw [ha0, ha_toLp]
    exact hx_nonneg n a
  have hx_tendsto :
      Tendsto (fun n : ℕ => eLpNorm ((x n : α → G) - (g : α → G)) p μ) atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm g_meas zero_mem hp_ne_top
    · have hg_nonneg : (0 : α → G) ≤ᵐ[μ] g := (Lp.coeFn_nonneg _).mpr g.2
      refine hg_nonneg.mono fun a ha => subset_closure ?_
      simpa using ha
    · simp_rw [sub_zero]; finiteness
  refine
    ⟨fun n =>
      (coeSimpleFuncNonnegToLpNonneg p μ G) ⟨toLp (x n) (hx_memLp n), hx_nonneg_Lp n⟩,
      fun n => mem_range_self _, ?_⟩
  suffices Tendsto (fun n : ℕ => (toLp (x n) (hx_memLp n) : Lp G p μ)) atTop (𝓝 (g : Lp G p μ)) by
    rw [tendsto_iff_dist_tendsto_zero] at this ⊢
    simp_rw [Subtype.dist_eq]
    exact this
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine Filter.Tendsto.congr (fun n => eLpNorm_congr_ae (EventuallyEq.sub ?_ ?_)) hx_tendsto
  · symm
    rw [Lp.simpleFunc.toLp_eq_toLp]
    exact h_toLp n
  · rfl

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
theorem Lp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (motive : Lp E p μ → Prop)
    (indicatorConst : ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
      motive (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (add : ∀ ⦃f g⦄, ∀ hf : MemLp f p μ, ∀ hg : MemLp g p μ, Disjoint (support f) (support g) →
      motive (hf.toLp f) → motive (hg.toLp g) → motive (hf.toLp f + hg.toLp g))
    (isClosed : IsClosed { f : Lp E p μ | motive f }) : ∀ f : Lp E p μ, motive f := by
  refine fun f => (Lp.simpleFunc.denseRange hp_ne_top).induction_on f isClosed ?_
  refine Lp.simpleFunc.induction (α := α) (E := E) (lt_of_lt_of_le zero_lt_one _i.elim).ne'
    hp_ne_top ?_ ?_
  · exact fun c s => indicatorConst c
  · exact fun f g hf hg => add hf hg

/-- To prove something for an arbitrary `MemLp` function in a second countable
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
theorem MemLp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (motive : (α → E) → Prop)
    (indicator : ∀ (c : E) ⦃s⦄, MeasurableSet s → μ s < ∞ → motive (s.indicator fun _ => c))
    (add : ∀ ⦃f g : α → E⦄, Disjoint (support f) (support g) → MemLp f p μ → MemLp g p μ →
      motive f → motive g → motive (f + g))
    (closed : IsClosed { f : Lp E p μ | motive f })
    (ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → MemLp f p μ → motive f → motive g) :
    ∀ ⦃f : α → E⦄, MemLp f p μ → motive f := by
  have : ∀ f : SimpleFunc α E, MemLp f p μ → motive f := by
    apply SimpleFunc.induction
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert indicator 0 MeasurableSet.empty (by simp) using 1; ext; simp
      have hp_pos : p ≠ 0 := (lt_of_lt_of_le zero_lt_one _i.elim).ne'
      exact indicator c hs (SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs h)
    · intro f g hfg hf hg int_fg
      rw [SimpleFunc.coe_add,
        memLp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable] at int_fg
      exact add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2)
  have : ∀ f : Lp.simpleFunc E p μ, motive f := by
    intro f
    exact
      ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f) (Lp.simpleFunc.memLp f)
        (this (Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.memLp f))
  have : ∀ f : Lp E p μ, motive f := fun f =>
    (Lp.simpleFunc.denseRange hp_ne_top).induction_on f closed this
  exact fun f hf => ae hf.coeFn_toLp (Lp.memLp _) (this (hf.toLp f))

/-- If a set of ae strongly measurable functions is stable under addition and approximates
characteristic functions in `ℒp`, then it is dense in `ℒp`. -/
theorem MemLp.induction_dense (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
    (h0P :
      ∀ (c : E) ⦃s : Set α⦄,
        MeasurableSet s →
          μ s < ∞ →
            ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : α → E, eLpNorm (g - s.indicator fun _ => c) p μ ≤ ε ∧ P g)
    (h1P : ∀ f g, P f → P g → P (f + g)) (h2P : ∀ f, P f → AEStronglyMeasurable f μ) {f : α → E}
    (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ P g := by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
        hε with ⟨g, _, Pg⟩
    exact ⟨g, by simp, Pg⟩
  suffices H : ∀ (f' : α →ₛ E) (δ : ℝ≥0∞) (hδ : δ ≠ 0), MemLp f' p μ →
      ∃ g, eLpNorm (⇑f' - g) p μ ≤ δ ∧ P g by
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p hε
    rcases hf.exists_simpleFunc_eLpNorm_sub_lt hp_ne_top ηpos.ne' with ⟨f', hf', f'_mem⟩
    rcases H f' η ηpos.ne' f'_mem with ⟨g, hg, Pg⟩
    refine ⟨g, ?_, Pg⟩
    convert (hη _ _ (hf.aestronglyMeasurable.sub f'.aestronglyMeasurable)
          (f'.aestronglyMeasurable.sub (h2P g Pg)) hf'.le hg).le using 2
    simp only [sub_add_sub_cancel]
  apply SimpleFunc.induction
  · intro c s hs ε εpos Hs
    rcases eq_or_ne c 0 with (rfl | hc)
    · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
          εpos with ⟨g, hg, Pg⟩
      rw [← eLpNorm_neg, neg_sub] at hg
      refine ⟨g, ?_, Pg⟩
      convert hg
      ext x
      simp
    · have : μ s < ∞ := SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs Hs
      rcases h0P c hs this εpos with ⟨g, hg, Pg⟩
      rw [← eLpNorm_neg, neg_sub] at hg
      exact ⟨g, hg, Pg⟩
  · intro f f' hff' hf hf' δ δpos int_ff'
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p δpos
    rw [SimpleFunc.coe_add,
      memLp_add_of_disjoint hff' f.stronglyMeasurable f'.stronglyMeasurable] at int_ff'
    rcases hf η ηpos.ne' int_ff'.1 with ⟨g, hg, Pg⟩
    rcases hf' η ηpos.ne' int_ff'.2 with ⟨g', hg', Pg'⟩
    refine ⟨g + g', ?_, h1P g g' Pg Pg'⟩
    convert (hη _ _ (f.aestronglyMeasurable.sub (h2P g Pg))
          (f'.aestronglyMeasurable.sub (h2P g' Pg')) hg hg').le using 2
    rw [SimpleFunc.coe_add]
    abel

section Integrable

@[inherit_doc MeasureTheory.Lp.simpleFunc]
notation:25 α " →₁ₛ[" μ "] " E => @MeasureTheory.Lp.simpleFunc α E _ _ 1 μ

theorem L1.SimpleFunc.toLp_one_eq_toL1 (f : α →ₛ E) (hf : Integrable f μ) :
    (Lp.simpleFunc.toLp f (memLp_one_iff_integrable.2 hf) : α →₁[μ] E) = hf.toL1 f :=
  rfl

@[fun_prop]
protected theorem L1.SimpleFunc.integrable (f : α →₁ₛ[μ] E) :
    Integrable (Lp.simpleFunc.toSimpleFunc f) μ := by
  rw [← memLp_one_iff_integrable]; exact Lp.simpleFunc.memLp f

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
  simp only [← memLp_one_iff_integrable] at *
  exact MemLp.induction one_ne_top (motive := P) h_ind h_add h_closed h_ae

end Integrable

end MeasureTheory
