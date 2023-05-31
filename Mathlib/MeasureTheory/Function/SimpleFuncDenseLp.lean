/-
Copyright (c) 2022 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth

! This file was ported from Lean 3 source module measure_theory.function.simple_func_dense_lp
! leanprover-community/mathlib commit 5a2df4cd59cb31e97a516d4603a14bed5c2f9425
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.L1Space
import Mathbin.MeasureTheory.Function.SimpleFuncDense

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `measure_theory.Lp.simple_func`, the type of `Lp` simple functions
* `coe_to_Lp`, the embedding of `Lp.simple_func E p μ` into `Lp E p μ`

## Main results

* `tendsto_approx_on_univ_Lp` (Lᵖ convergence): If `E` is a `normed_add_comm_group` and `f` is
  measurable and `mem_ℒp` (for `p < ∞`), then the simple functions
  `simple_func.approx_on f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simple_func.dense_embedding`: the embedding `coe_to_Lp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simple_func.induction`, `Lp.induction`, `mem_ℒp.induction`, `integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/


noncomputable section

open Set Function Filter TopologicalSpace ENNReal Emetric Finset

open scoped Classical Topology ENNReal MeasureTheory BigOperators

variable {α β ι E F 𝕜 : Type _}

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
    ‖approxOn f hf s y₀ h₀ n x - f x‖₊ ≤ ‖f x - y₀‖₊ :=
  by
  have := edist_approx_on_le hf h₀ x n
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact_mod_cast this
#align measure_theory.simple_func.nnnorm_approx_on_le MeasureTheory.SimpleFunc.nnnorm_approxOn_le

theorem norm_approxOn_y₀_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖ :=
  by
  have := edist_approx_on_y0_le hf h₀ x n
  repeat' rw [edist_comm y₀, edist_eq_coe_nnnorm_sub] at this
  exact_mod_cast this
#align measure_theory.simple_func.norm_approx_on_y₀_le MeasureTheory.SimpleFunc.norm_approxOn_y₀_le

theorem norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    (h₀ : (0 : E) ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s 0 h₀ n x‖ ≤ ‖f x‖ + ‖f x‖ :=
  by
  have := edist_approx_on_y0_le hf h₀ x n
  simp [edist_comm (0 : E), edist_eq_coe_nnnorm] at this
  exact_mod_cast this
#align measure_theory.simple_func.norm_approx_on_zero_le MeasureTheory.SimpleFunc.norm_approxOn_zero_le

theorem tendsto_approxOn_Lp_snorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (hp_ne_top : p ≠ ∞) {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : snorm (fun x => f x - y₀) p μ < ∞) :
    Tendsto (fun n => snorm (approxOn f hf s y₀ h₀ n - f) p μ) atTop (𝓝 0) :=
  by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, snorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.to_real := to_real_pos hp_zero hp_ne_top
  suffices tendsto (fun n => ∫⁻ x, ‖approx_on f hf s y₀ h₀ n x - f x‖₊ ^ p.to_real ∂μ) at_top (𝓝 0)
    by
    simp only [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_ne_top]
    convert continuous_rpow_const.continuous_at.tendsto.comp this <;> simp [_root_.inv_pos.mpr hp]
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas :
    ∀ n, Measurable fun x => (‖approx_on f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.to_real := by
    simpa only [← edist_eq_coe_nnnorm_sub] using fun n =>
      (approx_on f hf s y₀ h₀ n).measurable_bind (fun y x => edist y (f x) ^ p.to_real) fun y =>
        (measurable_edist_right.comp hf).pow_const p.to_real
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `λ x, ‖f x - y₀‖ ^ p.to_real`
  have h_bound :
    ∀ n,
      (fun x => (‖approx_on f hf s y₀ h₀ n x - f x‖₊ : ℝ≥0∞) ^ p.to_real) ≤ᵐ[μ] fun x =>
        ‖f x - y₀‖₊ ^ p.to_real :=
    fun n =>
    eventually_of_forall fun x =>
      rpow_le_rpow (coe_mono (nnnorm_approx_on_le hf h₀ x n)) to_real_nonneg
  -- (3) The bounding function `λ x, ‖f x - y₀‖ ^ p.to_real` has finite integral
  have h_fin : (∫⁻ a : β, ‖f a - y₀‖₊ ^ p.to_real ∂μ) ≠ ⊤ :=
    (lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_zero hp_ne_top hi).Ne
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim :
    ∀ᵐ a : β ∂μ,
      tendsto (fun n => (‖approx_on f hf s y₀ h₀ n a - f a‖₊ : ℝ≥0∞) ^ p.to_real) at_top (𝓝 0) :=
    by
    filter_upwards [hμ]with a ha
    have : tendsto (fun n => (approx_on f hf s y₀ h₀ n) a - f a) at_top (𝓝 (f a - f a)) :=
      (tendsto_approx_on hf h₀ ha).sub tendsto_const_nhds
    convert continuous_rpow_const.continuous_at.tendsto.comp (tendsto_coe.mpr this.nnnorm)
    simp [zero_rpow_of_pos hp]
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim
#align measure_theory.simple_func.tendsto_approx_on_Lp_snorm MeasureTheory.SimpleFunc.tendsto_approxOn_Lp_snorm

theorem memℒp_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Memℒp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Memℒp (fun x => y₀) p μ) (n : ℕ) : Memℒp (approxOn f fmeas s y₀ h₀ n) p μ :=
  by
  refine' ⟨(approx_on f fmeas s y₀ h₀ n).AEStronglyMeasurable, _⟩
  suffices snorm (fun x => approx_on f fmeas s y₀ h₀ n x - y₀) p μ < ⊤
    by
    have : mem_ℒp (fun x => approx_on f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approx_on f fmeas s y₀ h₀ n - const β y₀).AEStronglyMeasurable, this⟩
    convert snorm_add_lt_top this hi₀
    ext x
    simp
  have hf' : mem_ℒp (fun x => ‖f x - y₀‖) p μ :=
    by
    have h_meas : Measurable fun x => ‖f x - y₀‖ :=
      by
      simp only [← dist_eq_norm]
      exact (continuous_id.dist continuous_const).Measurable.comp fmeas
    refine' ⟨h_meas.ae_measurable.ae_strongly_measurable, _⟩
    rw [snorm_norm]
    convert snorm_add_lt_top hf hi₀.neg
    ext x
    simp [sub_eq_add_neg]
  have : ∀ᵐ x ∂μ, ‖approx_on f fmeas s y₀ h₀ n x - y₀‖ ≤ ‖‖f x - y₀‖ + ‖f x - y₀‖‖ :=
    by
    refine' eventually_of_forall _
    intro x
    convert norm_approx_on_y₀_le fmeas h₀ x n
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    snorm (fun x => approx_on f fmeas s y₀ h₀ n x - y₀) p μ ≤
        snorm (fun x => ‖f x - y₀‖ + ‖f x - y₀‖) p μ :=
      snorm_mono_ae this
    _ < ⊤ := snorm_add_lt_top hf' hf'
    
#align measure_theory.simple_func.mem_ℒp_approx_on MeasureTheory.SimpleFunc.memℒp_approxOn

theorem tendsto_approxOn_range_Lp_snorm [BorelSpace E] {f : β → E} (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : snorm f p μ < ∞) :
    Tendsto (fun n => snorm (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n - f) p μ) atTop (𝓝 0) :=
  by
  refine' tendsto_approx_on_Lp_snorm fmeas _ hp_ne_top _ _
  · apply eventually_of_forall
    intro x
    apply subset_closure
    simp
  · simpa using hf
#align measure_theory.simple_func.tendsto_approx_on_range_Lp_snorm MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp_snorm

theorem memℒp_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Memℒp f p μ) (n : ℕ) :
    Memℒp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) p μ :=
  memℒp_approxOn fmeas hf (by simp) zero_memℒp n
#align measure_theory.simple_func.mem_ℒp_approx_on_range MeasureTheory.SimpleFunc.memℒp_approxOn_range

theorem tendsto_approxOn_range_lp [BorelSpace E] {f : β → E} [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : Memℒp f p μ) :
    Tendsto
      (fun n =>
        (memℒp_approxOn_range fmeas hf n).toLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n))
      atTop (𝓝 (hf.toLp f)) :=
  by
  simpa only [Lp.tendsto_Lp_iff_tendsto_ℒp''] using
    tendsto_approx_on_range_Lp_snorm hp_ne_top fmeas hf.2
#align measure_theory.simple_func.tendsto_approx_on_range_Lp MeasureTheory.SimpleFunc.tendsto_approxOn_range_lp

/-- Any function in `ℒp` can be approximated by a simple function if `p < ∞`. -/
theorem MeasureTheory.Memℒp.exists_simpleFunc_snorm_sub_lt {E : Type _} [NormedAddCommGroup E]
    {f : β → E} {μ : Measure β} (hf : Memℒp f p μ) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : β →ₛ E, snorm (f - g) p μ < ε ∧ Memℒp g p μ :=
  by
  borelize E
  let f' := hf.1.mk f
  suffices H : ∃ g : β →ₛ E, snorm (f' - g) p μ < ε ∧ mem_ℒp g p μ
  · rcases H with ⟨g, hg, g_mem⟩
    refine' ⟨g, _, g_mem⟩
    convert hg using 1
    apply snorm_congr_ae
    filter_upwards [hf.1.ae_eq_mk]with x hx
    simpa only [Pi.sub_apply, sub_left_inj] using hx
  have hf' : mem_ℒp f' p μ := hf.ae_eq hf.1.ae_eq_mk
  have f'meas : Measurable f' := hf.1.measurable_mk
  have : separable_space (range f' ∪ {0} : Set E) :=
    strongly_measurable.separable_space_range_union_singleton hf.1.stronglyMeasurable_mk
  rcases((tendsto_order.1 (tendsto_approx_on_range_Lp_snorm hp_ne_top f'meas hf'.2)).2 ε
        hε.bot_lt).exists with
    ⟨n, hn⟩
  rw [← snorm_neg, neg_sub] at hn
  exact ⟨_, hn, mem_ℒp_approx_on_range f'meas hf' _⟩
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
    tendsto_approx_on_Lp_snorm hf h₀ one_ne_top hμ
      (by simpa [snorm_one_eq_lintegral_nnnorm] using hi)
#align measure_theory.simple_func.tendsto_approx_on_L1_nnnorm MeasureTheory.SimpleFunc.tendsto_approxOn_L1_nnnorm

theorem integrable_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Integrable (fun x => y₀) μ) (n : ℕ) : Integrable (approxOn f fmeas s y₀ h₀ n) μ :=
  by
  rw [← mem_ℒp_one_iff_integrable] at hf hi₀⊢
  exact mem_ℒp_approx_on fmeas hf h₀ hi₀ n
#align measure_theory.simple_func.integrable_approx_on MeasureTheory.SimpleFunc.integrable_approxOn

theorem tendsto_approxOn_range_L1_nnnorm [OpensMeasurableSpace E] {f : β → E} {μ : Measure β}
    [SeparableSpace (range f ∪ {0} : Set E)] (fmeas : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖₊ ∂μ) atTop
      (𝓝 0) :=
  by
  apply tendsto_approx_on_L1_nnnorm fmeas
  · apply eventually_of_forall
    intro x
    apply subset_closure
    simp
  · simpa using hf.2
#align measure_theory.simple_func.tendsto_approx_on_range_L1_nnnorm MeasureTheory.SimpleFunc.tendsto_approxOn_range_L1_nnnorm

theorem integrable_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Integrable f μ) (n : ℕ) :
    Integrable (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) μ :=
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
- `mem_ℒp f 0 μ` and `mem_ℒp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `mem_ℒp f p μ ↔ integrable f μ ↔ f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞`.
-/


theorem exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  exists_forall_le (f.map fun x => ‖x‖)
#align measure_theory.simple_func.exists_forall_norm_le MeasureTheory.SimpleFunc.exists_forall_norm_le

theorem memℒp_zero (f : α →ₛ E) (μ : Measure α) : Memℒp f 0 μ :=
  memℒp_zero_iff_aestronglyMeasurable.mpr f.AEStronglyMeasurable
#align measure_theory.simple_func.mem_ℒp_zero MeasureTheory.SimpleFunc.memℒp_zero

theorem memℒp_top (f : α →ₛ E) (μ : Measure α) : Memℒp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  memℒp_top_of_bound f.AEStronglyMeasurable C <| eventually_of_forall hfC
#align measure_theory.simple_func.mem_ℒp_top MeasureTheory.SimpleFunc.memℒp_top

protected theorem snorm'_eq {p : ℝ} (f : α →ₛ F) (μ : Measure α) :
    snorm' f p μ = (∑ y in f.range, (‖y‖₊ : ℝ≥0∞) ^ p * μ (f ⁻¹' {y})) ^ (1 / p) :=
  by
  have h_map : (fun a => (‖f a‖₊ : ℝ≥0∞) ^ p) = f.map fun a : F => (‖a‖₊ : ℝ≥0∞) ^ p := by simp
  rw [snorm', h_map, lintegral_eq_lintegral, map_lintegral]
#align measure_theory.simple_func.snorm'_eq MeasureTheory.SimpleFunc.snorm'_eq

theorem measure_preimage_lt_top_of_memℒp (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) (f : α →ₛ E)
    (hf : Memℒp f p μ) (y : E) (hy_ne : y ≠ 0) : μ (f ⁻¹' {y}) < ∞ :=
  by
  have hp_pos_real : 0 < p.to_real := ENNReal.toReal_pos hp_pos hp_ne_top
  have hf_snorm := mem_ℒp.snorm_lt_top hf
  rw [snorm_eq_snorm' hp_pos hp_ne_top, f.snorm'_eq, ←
    @ENNReal.lt_rpow_one_div_iff _ _ (1 / p.to_real) (by simp [hp_pos_real]),
    @ENNReal.top_rpow_of_pos (1 / (1 / p.to_real)) (by simp [hp_pos_real]),
    ENNReal.sum_lt_top_iff] at hf_snorm
  by_cases hyf : y ∈ f.range
  swap
  · suffices h_empty : f ⁻¹' {y} = ∅
    · rw [h_empty, measure_empty]; exact ENNReal.coe_lt_top
    ext1 x
    rw [Set.mem_preimage, Set.mem_singleton_iff, mem_empty_iff_false, iff_false_iff]
    refine' fun hxy => hyf _
    rw [mem_range, Set.mem_range]
    exact ⟨x, hxy⟩
  specialize hf_snorm y hyf
  rw [ENNReal.mul_lt_top_iff] at hf_snorm
  cases hf_snorm
  · exact hf_snorm.2
  cases hf_snorm
  · refine' absurd _ hy_ne
    simpa [hp_pos_real] using hf_snorm
  · simp [hf_snorm]
#align measure_theory.simple_func.measure_preimage_lt_top_of_mem_ℒp MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memℒp

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem memℒp_of_finite_measure_preimage (p : ℝ≥0∞) {f : α →ₛ E}
    (hf : ∀ (y) (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞) : Memℒp f p μ :=
  by
  by_cases hp0 : p = 0
  · rw [hp0, mem_ℒp_zero_iff_ae_strongly_measurable]; exact f.ae_strongly_measurable
  by_cases hp_top : p = ∞
  · rw [hp_top]; exact mem_ℒp_top f μ
  refine' ⟨f.ae_strongly_measurable, _⟩
  rw [snorm_eq_snorm' hp0 hp_top, f.snorm'_eq]
  refine' ENNReal.rpow_lt_top_of_nonneg (by simp) (ennreal.sum_lt_top_iff.mpr fun y hy => _).Ne
  by_cases hy0 : y = 0
  · simp [hy0, ENNReal.toReal_pos hp0 hp_top]
  · refine' ENNReal.mul_lt_top _ (hf y hy0).Ne
    exact (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top).Ne
#align measure_theory.simple_func.mem_ℒp_of_finite_measure_preimage MeasureTheory.SimpleFunc.memℒp_of_finite_measure_preimage

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem memℒp_iff {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp f p μ ↔ ∀ (y) (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞ :=
  ⟨fun h => measure_preimage_lt_top_of_memℒp hp_pos hp_ne_top f h, fun h =>
    memℒp_of_finite_measure_preimage p h⟩
#align measure_theory.simple_func.mem_ℒp_iff MeasureTheory.SimpleFunc.memℒp_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem integrable_iff {f : α →ₛ E} : Integrable f μ ↔ ∀ (y) (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞ :=
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
  simpa only [integrable_iff_fin_meas_supp] using fin_meas_supp.pair
#align measure_theory.simple_func.integrable_pair MeasureTheory.SimpleFunc.integrable_pair

theorem memℒp_of_finiteMeasure (f : α →ₛ E) (p : ℝ≥0∞) (μ : Measure α) [FiniteMeasure μ] :
    Memℒp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  Memℒp.of_bound f.AEStronglyMeasurable C <| eventually_of_forall hfC
#align measure_theory.simple_func.mem_ℒp_of_is_finite_measure MeasureTheory.SimpleFunc.memℒp_of_finiteMeasure

theorem integrable_of_finiteMeasure [FiniteMeasure μ] (f : α →ₛ E) : Integrable f μ :=
  memℒp_one_iff_integrable.mp (f.memℒp_of_finiteMeasure 1 μ)
#align measure_theory.simple_func.integrable_of_is_finite_measure MeasureTheory.SimpleFunc.integrable_of_finiteMeasure

theorem measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) {x : E}
    (hx : x ≠ 0) : μ (f ⁻¹' {x}) < ∞ :=
  integrable_iff.mp hf x hx
#align measure_theory.simple_func.measure_preimage_lt_top_of_integrable MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem measure_support_lt_top [Zero β] (f : α →ₛ β) (hf : ∀ (y) (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞) :
    μ (support f) < ∞ := by
  rw [support_eq]
  refine' (measure_bUnion_finset_le _ _).trans_lt (ennreal.sum_lt_top_iff.mpr fun y hy => _)
  rw [Finset.mem_filter] at hy
  exact hf y hy.2
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
    μ s < ⊤ :=
  by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  simpa only [mem_ℒp_iff_fin_meas_supp hp_pos hp_ne_top, fin_meas_supp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs
#align measure_theory.simple_func.measure_lt_top_of_mem_ℒp_indicator MeasureTheory.SimpleFunc.measure_lt_top_of_memℒp_indicator

end SimpleFuncProperties

end SimpleFunc

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/


namespace Lp

open AeEqFun

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (p : ℝ≥0∞)
  (μ : Measure α)

variable (E)

/-- `Lp.simple_func` is a subspace of Lp consisting of equivalence classes of an integrable simple
    function. -/
def simpleFunc : AddSubgroup (lp E p μ)
    where
  carrier := { f : lp E p μ | ∃ s : α →ₛ E, (AEEqFun.mk s s.AEStronglyMeasurable : α →ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := fun f g ⟨s, hs⟩ ⟨t, ht⟩ =>
    ⟨s + t, by
      simp only [← hs, ← ht, ae_eq_fun.mk_add_mk, AddSubgroup.coe_add, ae_eq_fun.mk_eq_mk,
        simple_func.coe_add]⟩
  neg_mem' := fun f ⟨s, hs⟩ =>
    ⟨-s, by
      simp only [← hs, ae_eq_fun.neg_mk, simple_func.coe_neg, ae_eq_fun.mk_eq_mk,
        AddSubgroup.coe_neg]⟩
#align measure_theory.Lp.simple_func MeasureTheory.lp.simpleFunc

variable {E p μ}

namespace SimpleFunc

section Instances

/-! Simple functions in Lp space form a `normed_space`. -/


@[norm_cast]
theorem coe_coe (f : lp.simpleFunc E p μ) : ⇑(f : lp E p μ) = f :=
  rfl
#align measure_theory.Lp.simple_func.coe_coe MeasureTheory.lp.simpleFunc.coe_coe

protected theorem eq' {f g : lp.simpleFunc E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
  Subtype.eq ∘ Subtype.eq
#align measure_theory.Lp.simple_func.eq' MeasureTheory.lp.simpleFunc.eq'

/-! Implementation note:  If `Lp.simple_func E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simple_func E p μ`, would be
unnecessary.  But instead, `Lp.simple_func E p μ` is defined as an `add_subgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a `has_smul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def hasSmul : SMul 𝕜 (lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • f, by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (ae_eq_fun.smul_mk k s s.ae_strongly_measurable).symm _
      rw [hs]
      rfl⟩⟩
#align measure_theory.Lp.simple_func.has_smul MeasureTheory.lp.simpleFunc.hasSmul

attribute [local instance] simple_func.has_smul

@[simp, norm_cast]
theorem coe_smul (c : 𝕜) (f : lp.simpleFunc E p μ) :
    ((c • f : lp.simpleFunc E p μ) : lp E p μ) = c • (f : lp E p μ) :=
  rfl
#align measure_theory.Lp.simple_func.coe_smul MeasureTheory.lp.simpleFunc.coe_smul

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def module : Module 𝕜 (lp.simpleFunc E p μ)
    where
  one_smul f := by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _
#align measure_theory.Lp.simple_func.module MeasureTheory.lp.simpleFunc.module

attribute [local instance] simple_func.module

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected theorem boundedSMul [Fact (1 ≤ p)] : BoundedSMul 𝕜 (lp.simpleFunc E p μ) :=
  BoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : lp E p μ) : _)
#align measure_theory.Lp.simple_func.has_bounded_smul MeasureTheory.lp.simpleFunc.boundedSMul

attribute [local instance] simple_func.has_bounded_smul

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def normedSpace {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (lp.simpleFunc E p μ) :=
  ⟨norm_smul_le⟩
#align measure_theory.Lp.simple_func.normed_space MeasureTheory.lp.simpleFunc.normedSpace

end Instances

attribute [local instance] simple_func.module simple_func.normed_space simple_func.has_bounded_smul

section ToLp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `mem_ℒp`. -/
@[reducible]
def toLp (f : α →ₛ E) (hf : Memℒp f p μ) : lp.simpleFunc E p μ :=
  ⟨hf.toLp f, ⟨f, rfl⟩⟩
#align measure_theory.Lp.simple_func.to_Lp MeasureTheory.lp.simpleFunc.toLp

theorem toLp_eq_toLp (f : α →ₛ E) (hf : Memℒp f p μ) : (toLp f hf : lp E p μ) = hf.toLp f :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_eq_to_Lp MeasureTheory.lp.simpleFunc.toLp_eq_toLp

theorem toLp_eq_mk (f : α →ₛ E) (hf : Memℒp f p μ) :
    (toLp f hf : α →ₘ[μ] E) = AEEqFun.mk f f.AEStronglyMeasurable :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_eq_mk MeasureTheory.lp.simpleFunc.toLp_eq_mk

theorem toLp_zero : toLp (0 : α →ₛ E) zero_memℒp = (0 : lp.simpleFunc E p μ) :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_zero MeasureTheory.lp.simpleFunc.toLp_zero

theorem toLp_add (f g : α →ₛ E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    toLp (f + g) (hf.add hg) = toLp f hf + toLp g hg :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_add MeasureTheory.lp.simpleFunc.toLp_add

theorem toLp_neg (f : α →ₛ E) (hf : Memℒp f p μ) : toLp (-f) hf.neg = -toLp f hf :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_neg MeasureTheory.lp.simpleFunc.toLp_neg

theorem toLp_sub (f g : α →ₛ E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    toLp (f - g) (hf.sub hg) = toLp f hf - toLp g hg := by
  simp only [sub_eq_add_neg, ← to_Lp_neg, ← to_Lp_add]; rfl
#align measure_theory.Lp.simple_func.to_Lp_sub MeasureTheory.lp.simpleFunc.toLp_sub

variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

theorem toLp_smul (f : α →ₛ E) (hf : Memℒp f p μ) (c : 𝕜) :
    toLp (c • f) (hf.const_smul c) = c • toLp f hf :=
  rfl
#align measure_theory.Lp.simple_func.to_Lp_smul MeasureTheory.lp.simpleFunc.toLp_smul

theorem norm_toLp [Fact (1 ≤ p)] (f : α →ₛ E) (hf : Memℒp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (snorm f p μ) :=
  norm_toLp f hf
#align measure_theory.Lp.simple_func.norm_to_Lp MeasureTheory.lp.simpleFunc.norm_toLp

end ToLp

section ToSimpleFunc

/-- Find a representative of a `Lp.simple_func`. -/
def toSimpleFunc (f : lp.simpleFunc E p μ) : α →ₛ E :=
  Classical.choose f.2
#align measure_theory.Lp.simple_func.to_simple_func MeasureTheory.lp.simpleFunc.toSimpleFunc

/-- `(to_simple_func f)` is measurable. -/
@[measurability]
protected theorem measurable [MeasurableSpace E] (f : lp.simpleFunc E p μ) :
    Measurable (toSimpleFunc f) :=
  (toSimpleFunc f).Measurable
#align measure_theory.Lp.simple_func.measurable MeasureTheory.lp.simpleFunc.measurable

protected theorem stronglyMeasurable (f : lp.simpleFunc E p μ) :
    StronglyMeasurable (toSimpleFunc f) :=
  (toSimpleFunc f).StronglyMeasurable
#align measure_theory.Lp.simple_func.strongly_measurable MeasureTheory.lp.simpleFunc.stronglyMeasurable

@[measurability]
protected theorem aEMeasurable [MeasurableSpace E] (f : lp.simpleFunc E p μ) :
    AEMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.measurable f).AEMeasurable
#align measure_theory.Lp.simple_func.ae_measurable MeasureTheory.lp.simpleFunc.aEMeasurable

protected theorem aEStronglyMeasurable (f : lp.simpleFunc E p μ) :
    AEStronglyMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.stronglyMeasurable f).AEStronglyMeasurable
#align measure_theory.Lp.simple_func.ae_strongly_measurable MeasureTheory.lp.simpleFunc.aEStronglyMeasurable

theorem toSimpleFunc_eq_to_fun (f : lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f :=
  show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α →ₘ[μ] E)
    by
    convert(ae_eq_fun.coe_fn_mk (to_simple_func f)
          (to_simple_func f).AEStronglyMeasurable).symm using
      2
    exact (Classical.choose_spec f.2).symm
#align measure_theory.Lp.simple_func.to_simple_func_eq_to_fun MeasureTheory.lp.simpleFunc.toSimpleFunc_eq_to_fun

/-- `to_simple_func f` satisfies the predicate `mem_ℒp`. -/
protected theorem memℒp (f : lp.simpleFunc E p μ) : Memℒp (toSimpleFunc f) p μ :=
  Memℒp.ae_eq (toSimpleFunc_eq_to_fun f).symm <| mem_lp_iff_memℒp.mp (f : lp E p μ).2
#align measure_theory.Lp.simple_func.mem_ℒp MeasureTheory.lp.simpleFunc.memℒp

theorem toLp_toSimpleFunc (f : lp.simpleFunc E p μ) :
    toLp (toSimpleFunc f) (simpleFunc.memℒp f) = f :=
  simpleFunc.eq' (Classical.choose_spec f.2)
#align measure_theory.Lp.simple_func.to_Lp_to_simple_func MeasureTheory.lp.simpleFunc.toLp_toSimpleFunc

theorem toSimpleFunc_toLp (f : α →ₛ E) (hfi : Memℒp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f := by
  rw [← ae_eq_fun.mk_eq_mk]; exact Classical.choose_spec (to_Lp f hfi).2
#align measure_theory.Lp.simple_func.to_simple_func_to_Lp MeasureTheory.lp.simpleFunc.toSimpleFunc_toLp

variable (E μ)

theorem zero_toSimpleFunc : toSimpleFunc (0 : lp.simpleFunc E p μ) =ᵐ[μ] 0 :=
  by
  filter_upwards [to_simple_func_eq_to_fun (0 : Lp.simple_func E p μ),
    Lp.coe_fn_zero E 1 μ]with _ h₁ _
  rwa [h₁]
#align measure_theory.Lp.simple_func.zero_to_simple_func MeasureTheory.lp.simpleFunc.zero_toSimpleFunc

variable {E μ}

theorem add_toSimpleFunc (f g : lp.simpleFunc E p μ) :
    toSimpleFunc (f + g) =ᵐ[μ] toSimpleFunc f + toSimpleFunc g :=
  by
  filter_upwards [to_simple_func_eq_to_fun (f + g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, Lp.coe_fn_add (f : Lp E p μ) g]with _
  simp only [← coe_coe, AddSubgroup.coe_add, Pi.add_apply]
  iterate 4 intro h; rw [h]
#align measure_theory.Lp.simple_func.add_to_simple_func MeasureTheory.lp.simpleFunc.add_toSimpleFunc

theorem neg_toSimpleFunc (f : lp.simpleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f :=
  by
  filter_upwards [to_simple_func_eq_to_fun (-f), to_simple_func_eq_to_fun f,
    Lp.coe_fn_neg (f : Lp E p μ)]with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg, ← coe_coe]
  repeat' intro h; rw [h]
#align measure_theory.Lp.simple_func.neg_to_simple_func MeasureTheory.lp.simpleFunc.neg_toSimpleFunc

theorem sub_toSimpleFunc (f g : lp.simpleFunc E p μ) :
    toSimpleFunc (f - g) =ᵐ[μ] toSimpleFunc f - toSimpleFunc g :=
  by
  filter_upwards [to_simple_func_eq_to_fun (f - g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, Lp.coe_fn_sub (f : Lp E p μ) g]with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply, ← coe_coe]
  repeat' intro h; rw [h]
#align measure_theory.Lp.simple_func.sub_to_simple_func MeasureTheory.lp.simpleFunc.sub_toSimpleFunc

variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

theorem smul_toSimpleFunc (k : 𝕜) (f : lp.simpleFunc E p μ) :
    toSimpleFunc (k • f) =ᵐ[μ] k • toSimpleFunc f :=
  by
  filter_upwards [to_simple_func_eq_to_fun (k • f), to_simple_func_eq_to_fun f,
    Lp.coe_fn_smul k (f : Lp E p μ)]with _
  simp only [Pi.smul_apply, coe_smul, ← coe_coe]
  repeat' intro h; rw [h]
#align measure_theory.Lp.simple_func.smul_to_simple_func MeasureTheory.lp.simpleFunc.smul_toSimpleFunc

theorem norm_toSimpleFunc [Fact (1 ≤ p)] (f : lp.simpleFunc E p μ) :
    ‖f‖ = ENNReal.toReal (snorm (toSimpleFunc f) p μ) := by
  simpa [to_Lp_to_simple_func] using norm_to_Lp (to_simple_func f) (simple_func.mem_ℒp f)
#align measure_theory.Lp.simple_func.norm_to_simple_func MeasureTheory.lp.simpleFunc.norm_toSimpleFunc

end ToSimpleFunc

section Induction

variable (p)

/-- The characteristic function of a finite-measure measurable set `s`, as an `Lp` simple function.
-/
def indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    lp.simpleFunc E p μ :=
  toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.Lp.simple_func.indicator_const MeasureTheory.lp.simpleFunc.indicatorConst

variable {p}

@[simp]
theorem coe_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    (↑(indicatorConst p hs hμs c) : lp E p μ) = indicatorConstLp p hs hμs c :=
  rfl
#align measure_theory.Lp.simple_func.coe_indicator_const MeasureTheory.lp.simpleFunc.coe_indicatorConst

theorem toSimpleFunc_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    toSimpleFunc (indicatorConst p hs hμs c) =ᵐ[μ]
      (SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0) :=
  lp.simpleFunc.toSimpleFunc_toLp _ _
#align measure_theory.Lp.simple_func.to_simple_func_indicator_const MeasureTheory.lp.simpleFunc.toSimpleFunc_indicatorConst

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_elim]
protected theorem induction (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {P : lp.simpleFunc E p μ → Prop}
    (h_ind :
      ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
        P (lp.simpleFunc.indicatorConst p hs hμs.Ne c))
    (h_add :
      ∀ ⦃f g : α →ₛ E⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            Disjoint (support f) (support g) →
              P (lp.simpleFunc.toLp f hf) →
                P (lp.simpleFunc.toLp g hg) → P (lp.simpleFunc.toLp f hf + lp.simpleFunc.toLp g hg))
    (f : lp.simpleFunc E p μ) : P f :=
  by
  suffices ∀ f : α →ₛ E, ∀ hf : mem_ℒp f p μ, P (to_Lp f hf)
    by
    rw [← to_Lp_to_simple_func f]
    apply this
  clear f
  refine' simple_func.induction _ _
  · intro c s hs hf
    by_cases hc : c = 0
    · convert h_ind 0 MeasurableSet.empty (by simp) using 1
      ext1
      simp [hc]
    exact h_ind c hs (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs hf)
  · intro f g hfg hf hg hfg'
    obtain ⟨hf', hg'⟩ : mem_ℒp f p μ ∧ mem_ℒp g p μ :=
      (mem_ℒp_add_of_disjoint hfg f.strongly_measurable g.strongly_measurable).mp hfg'
    exact h_add hf' hg' hfg (hf hf') (hg hg')
#align measure_theory.Lp.simple_func.induction MeasureTheory.lp.simpleFunc.induction

end Induction

section CoeToLp

variable [Fact (1 ≤ p)]

protected theorem uniformContinuous : UniformContinuous (coe : lp.simpleFunc E p μ → lp E p μ) :=
  uniformContinuous_comap
#align measure_theory.Lp.simple_func.uniform_continuous MeasureTheory.lp.simpleFunc.uniformContinuous

protected theorem uniformEmbedding : UniformEmbedding (coe : lp.simpleFunc E p μ → lp E p μ) :=
  uniformEmbedding_comap Subtype.val_injective
#align measure_theory.Lp.simple_func.uniform_embedding MeasureTheory.lp.simpleFunc.uniformEmbedding

protected theorem uniformInducing : UniformInducing (coe : lp.simpleFunc E p μ → lp E p μ) :=
  simpleFunc.uniformEmbedding.to_uniformInducing
#align measure_theory.Lp.simple_func.uniform_inducing MeasureTheory.lp.simpleFunc.uniformInducing

protected theorem denseEmbedding (hp_ne_top : p ≠ ∞) :
    DenseEmbedding (coe : lp.simpleFunc E p μ → lp E p μ) :=
  by
  borelize E
  apply simple_func.uniform_embedding.dense_embedding
  intro f
  rw [mem_closure_iff_seq_limit]
  have hfi' : mem_ℒp f p μ := Lp.mem_ℒp f
  haveI : separable_space (range f ∪ {0} : Set E) :=
    (Lp.strongly_measurable f).separableSpace_range_union_singleton
  refine'
    ⟨fun n =>
      ↑(to_Lp
          (simple_func.approx_on f (Lp.strongly_measurable f).Measurable (range f ∪ {0}) 0 (by simp)
            n)
          (simple_func.mem_ℒp_approx_on_range (Lp.strongly_measurable f).Measurable hfi' n)),
      fun n => mem_range_self _, _⟩
  convert simple_func.tendsto_approx_on_range_Lp hp_ne_top (Lp.strongly_measurable f).Measurable
      hfi'
  rw [to_Lp_coe_fn f (Lp.mem_ℒp f)]
#align measure_theory.Lp.simple_func.dense_embedding MeasureTheory.lp.simpleFunc.denseEmbedding

protected theorem denseInducing (hp_ne_top : p ≠ ∞) :
    DenseInducing (coe : lp.simpleFunc E p μ → lp E p μ) :=
  (simpleFunc.denseEmbedding hp_ne_top).to_denseInducing
#align measure_theory.Lp.simple_func.dense_inducing MeasureTheory.lp.simpleFunc.denseInducing

protected theorem denseRange (hp_ne_top : p ≠ ∞) :
    DenseRange (coe : lp.simpleFunc E p μ → lp E p μ) :=
  (simpleFunc.denseInducing hp_ne_top).dense
#align measure_theory.Lp.simple_func.dense_range MeasureTheory.lp.simpleFunc.denseRange

variable [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

variable (α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
def coeToLp : lp.simpleFunc E p μ →L[𝕜] lp E p μ :=
  {
    AddSubgroup.subtype
      (lp.simpleFunc E p μ) with
    map_smul' := fun k f => rfl
    cont := lp.simpleFunc.uniformContinuous.Continuous }
#align measure_theory.Lp.simple_func.coe_to_Lp MeasureTheory.lp.simpleFunc.coeToLp

variable {α E 𝕜}

end CoeToLp

section Order

variable {G : Type _} [NormedLatticeAddCommGroup G]

theorem coeFn_le (f g : lp.simpleFunc G p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← Lp.coe_fn_le, coeFn_coe_base', coeFn_coe_base' g]
#align measure_theory.Lp.simple_func.coe_fn_le MeasureTheory.lp.simpleFunc.coeFn_le

instance : CovariantClass (lp.simpleFunc G p μ) (lp.simpleFunc G p μ) (· + ·) (· ≤ ·) :=
  by
  refine' ⟨fun f g₁ g₂ hg₁₂ => _⟩
  rw [← Lp.simple_func.coe_fn_le] at hg₁₂⊢
  have h_add_1 : ⇑(f + g₁) =ᵐ[μ] f + g₁ := Lp.coe_fn_add _ _
  have h_add_2 : ⇑(f + g₂) =ᵐ[μ] f + g₂ := Lp.coe_fn_add _ _
  filter_upwards [h_add_1, h_add_2, hg₁₂]with _ h1 h2 h3
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  exact add_le_add le_rfl h3

variable (p μ G)

theorem coeFn_zero : (0 : lp.simpleFunc G p μ) =ᵐ[μ] (0 : α → G) :=
  lp.coeFn_zero _ _ _
#align measure_theory.Lp.simple_func.coe_fn_zero MeasureTheory.lp.simpleFunc.coeFn_zero

variable {p μ G}

theorem coeFn_nonneg (f : lp.simpleFunc G p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f :=
  by
  rw [← Lp.simple_func.coe_fn_le]
  have h0 : (0 : Lp.simple_func G p μ) =ᵐ[μ] (0 : α → G) := Lp.simple_func.coe_fn_zero p μ G
  constructor <;> intro h <;> filter_upwards [h, h0]with _ _ h2
  · rwa [h2]
  · rwa [← h2]
#align measure_theory.Lp.simple_func.coe_fn_nonneg MeasureTheory.lp.simpleFunc.coeFn_nonneg

theorem exists_simpleFunc_nonneg_ae_eq {f : lp.simpleFunc G p μ} (hf : 0 ≤ f) :
    ∃ f' : α →ₛ G, 0 ≤ f' ∧ f =ᵐ[μ] f' :=
  by
  rw [← Lp.simple_func.coe_fn_nonneg] at hf
  have hf_ae : 0 ≤ᵐ[μ] simple_func.to_simple_func f := by
    filter_upwards [to_simple_func_eq_to_fun f, hf]with _ h1 _; rwa [h1]
  let s := to_measurable μ { x | ¬0 ≤ simple_func.to_simple_func f x }ᶜ
  have hs_zero : μ (sᶜ) = 0 := by rw [compl_compl, measure_to_measurable];
    rwa [eventually_le, ae_iff] at hf_ae
  have hfs_nonneg : ∀ x ∈ s, 0 ≤ simple_func.to_simple_func f x :=
    by
    intro x hxs
    rw [mem_compl_iff] at hxs
    have hx' : x ∉ { a : α | ¬0 ≤ simple_func.to_simple_func f a } := fun h =>
      hxs (subset_to_measurable μ _ h)
    rwa [Set.nmem_setOf_iff, Classical.not_not] at hx'
  let f' :=
    simple_func.piecewise s (measurable_set_to_measurable μ _).compl (simple_func.to_simple_func f)
      (simple_func.const α (0 : G))
  refine' ⟨f', fun x => _, _⟩
  · rw [simple_func.piecewise_apply]
    by_cases hxs : x ∈ s
    · simp only [hxs, hfs_nonneg x hxs, if_true, Pi.zero_apply, simple_func.coe_zero]
    · simp only [hxs, simple_func.const_zero, if_false]
  · rw [simple_func.coe_piecewise]
    have : s =ᵐ[μ] univ := by
      rw [ae_eq_set]
      simp only [true_and_iff, measure_empty, eq_self_iff_true, diff_univ, ← compl_eq_univ_diff]
      exact hs_zero
    refine' eventually_eq.trans (to_simple_func_eq_to_fun f).symm _
    refine' eventually_eq.trans _ (piecewise_ae_eq_of_ae_eq_set this.symm)
    simp only [simple_func.const_zero, indicator_univ, piecewise_eq_indicator, simple_func.coe_zero]
#align measure_theory.Lp.simple_func.exists_simple_func_nonneg_ae_eq MeasureTheory.lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq

variable (p μ G)

/-- Coercion from nonnegative simple functions of Lp to nonnegative functions of Lp. -/
def coeSimpleFuncNonnegToLpNonneg :
    { g : lp.simpleFunc G p μ // 0 ≤ g } → { g : lp G p μ // 0 ≤ g } := fun g => ⟨g, g.2⟩
#align measure_theory.Lp.simple_func.coe_simple_func_nonneg_to_Lp_nonneg MeasureTheory.lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg

theorem denseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G) :=
  by
  borelize G
  intro g
  rw [mem_closure_iff_seq_limit]
  have hg_mem_ℒp : mem_ℒp g p μ := Lp.mem_ℒp g
  have zero_mem : (0 : G) ∈ (range g ∪ {0} : Set G) ∩ { y | 0 ≤ y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, eq_self_iff_true, true_or_iff,
      mem_set_of_eq, le_refl, and_self_iff]
  have : separable_space ((range g ∪ {0}) ∩ { y | 0 ≤ y } : Set G) :=
    by
    apply is_separable.separable_space
    apply is_separable.mono _ (Set.inter_subset_left _ _)
    exact
      (Lp.strongly_measurable (g : Lp G p μ)).isSeparable_range.union
        (finite_singleton _).IsSeparable
  have g_meas : Measurable g := (Lp.strongly_measurable (g : Lp G p μ)).Measurable
  let x n := simple_func.approx_on g g_meas ((range g ∪ {0}) ∩ { y | 0 ≤ y }) 0 zero_mem n
  have hx_nonneg : ∀ n, 0 ≤ x n := by
    intro n a
    change x n a ∈ { y : G | 0 ≤ y }
    have A : (range g ∪ {0} : Set G) ∩ { y | 0 ≤ y } ⊆ { y | 0 ≤ y } := inter_subset_right _ _
    apply A
    exact simple_func.approx_on_mem g_meas _ n a
  have hx_mem_ℒp : ∀ n, mem_ℒp (x n) p μ :=
    simple_func.mem_ℒp_approx_on _ hg_mem_ℒp _ ⟨ae_strongly_measurable_const, by simp⟩
  have h_to_Lp := fun n => mem_ℒp.coe_fn_to_Lp (hx_mem_ℒp n)
  have hx_nonneg_Lp : ∀ n, 0 ≤ to_Lp (x n) (hx_mem_ℒp n) :=
    by
    intro n
    rw [← Lp.simple_func.coe_fn_le, coeFn_coe_base' (simple_func.to_Lp (x n) _),
      Lp.simple_func.to_Lp_eq_to_Lp]
    have h0 := Lp.simple_func.coe_fn_zero p μ G
    filter_upwards [Lp.simple_func.coe_fn_zero p μ G, h_to_Lp n]with a ha0 ha_to_Lp
    rw [ha0, ha_to_Lp]
    exact hx_nonneg n a
  have hx_tendsto : tendsto (fun n : ℕ => snorm (x n - g) p μ) at_top (𝓝 0) :=
    by
    apply simple_func.tendsto_approx_on_Lp_snorm g_meas zero_mem hp_ne_top
    · have hg_nonneg : 0 ≤ᵐ[μ] g := (Lp.coe_fn_nonneg _).mpr g.2
      refine' hg_nonneg.mono fun a ha => subset_closure _
      simpa using ha
    · simp_rw [sub_zero]; exact hg_mem_ℒp.snorm_lt_top
  refine'
    ⟨fun n =>
      (coe_simple_func_nonneg_to_Lp_nonneg p μ G) ⟨to_Lp (x n) (hx_mem_ℒp n), hx_nonneg_Lp n⟩,
      fun n => mem_range_self _, _⟩
  suffices tendsto (fun n : ℕ => ↑(to_Lp (x n) (hx_mem_ℒp n))) at_top (𝓝 (g : Lp G p μ))
    by
    rw [tendsto_iff_dist_tendsto_zero] at this⊢
    simp_rw [Subtype.dist_eq]
    convert this
  rw [Lp.tendsto_Lp_iff_tendsto_ℒp']
  convert hx_tendsto
  refine' funext fun n => snorm_congr_ae (eventually_eq.sub _ _)
  · rw [Lp.simple_func.to_Lp_eq_to_Lp]
    exact h_to_Lp n
  · rw [← coeFn_coeBase]
#align measure_theory.Lp.simple_func.dense_range_coe_simple_func_nonneg_to_Lp_nonneg MeasureTheory.lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg

variable {p μ G}

end Order

end SimpleFunc

end Lp

variable [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {p : ℝ≥0∞} {μ : Measure α}

/-- To prove something for an arbitrary `Lp` function in a second countable Borel normed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
@[elab_as_elim]
theorem lp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (P : lp E p μ → Prop)
    (h_ind :
      ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
        P (lp.simpleFunc.indicatorConst p hs hμs.Ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            Disjoint (support f) (support g) →
              P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed { f : lp E p μ | P f }) : ∀ f : lp E p μ, P f :=
  by
  refine' fun f => (Lp.simple_func.dense_range hp_ne_top).inductionOn f h_closed _
  refine' Lp.simple_func.induction (lt_of_lt_of_le zero_lt_one _i.elim).ne' hp_ne_top _ _
  · exact fun c s => h_ind c
  · exact fun f g hf hg => h_add hf hg
#align measure_theory.Lp.induction MeasureTheory.lp.induction

/-- To prove something for an arbitrary `mem_ℒp` function in a second countable
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
    (h_add :
      ∀ ⦃f g : α → E⦄,
        Disjoint (support f) (support g) → Memℒp f p μ → Memℒp g p μ → P f → P g → P (f + g))
    (h_closed : IsClosed { f : lp E p μ | P f })
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Memℒp f p μ → P f → P g) : ∀ ⦃f : α → E⦄ (hf : Memℒp f p μ), P f :=
  by
  have : ∀ f : simple_func α E, mem_ℒp f p μ → P f :=
    by
    refine' simple_func.induction _ _
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert h_ind 0 MeasurableSet.empty (by simp) using 1; ext; simp [const]
      have hp_pos : p ≠ 0 := (lt_of_lt_of_le zero_lt_one _i.elim).ne'
      exact h_ind c hs (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs h)
    · intro f g hfg hf hg int_fg
      rw [simple_func.coe_add,
        mem_ℒp_add_of_disjoint hfg f.strongly_measurable g.strongly_measurable] at int_fg
      refine' h_add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2)
  have : ∀ f : Lp.simple_func E p μ, P f := by
    intro f
    exact
      h_ae (Lp.simple_func.to_simple_func_eq_to_fun f) (Lp.simple_func.mem_ℒp f)
        (this (Lp.simple_func.to_simple_func f) (Lp.simple_func.mem_ℒp f))
  have : ∀ f : Lp E p μ, P f := fun f =>
    (Lp.simple_func.dense_range hp_ne_top).inductionOn f h_closed this
  exact fun f hf => h_ae hf.coeFn_toLp (Lp.mem_ℒp _) (this (hf.toLp f))
#align measure_theory.mem_ℒp.induction MeasureTheory.Memℒp.induction

/-- If a set of ae strongly measurable functions is stable under addition and approximates
characteristic functions in `ℒp`, then it is dense in `ℒp`. -/
theorem Memℒp.induction_dense (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
    (h0P :
      ∀ (c : E) ⦃s : Set α⦄,
        MeasurableSet s →
          μ s < ∞ →
            ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : α → E, snorm (g - s.indicator fun x => c) p μ ≤ ε ∧ P g)
    (h1P : ∀ f g, P f → P g → P (f + g)) (h2P : ∀ f, P f → AEStronglyMeasurable f μ) {f : α → E}
    (hf : Memℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : α → E, snorm (f - g) p μ ≤ ε ∧ P g :=
  by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, WithTop.zero_lt_top])
        hε with ⟨g, hg, Pg⟩
    exact ⟨g, by simp only [snorm_exponent_zero, zero_le'], Pg⟩
  suffices H :
    ∀ (f' : α →ₛ E) (δ : ℝ≥0∞) (hδ : δ ≠ 0), mem_ℒp f' p μ → ∃ g, snorm (f' - g) p μ ≤ δ ∧ P g
  · obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p hε
    rcases hf.exists_simple_func_snorm_sub_lt hp_ne_top ηpos.ne' with ⟨f', hf', f'_mem⟩
    rcases H f' η ηpos.ne' f'_mem with ⟨g, hg, Pg⟩
    refine' ⟨g, _, Pg⟩
    convert(hη _ _ (hf.ae_strongly_measurable.sub f'.ae_strongly_measurable)
          (f'.ae_strongly_measurable.sub (h2P g Pg)) hf'.le hg).le
    simp only [sub_add_sub_cancel]
  refine' simple_func.induction _ _
  · intro c s hs ε εpos Hs
    rcases eq_or_ne c 0 with (rfl | hc)
    · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, WithTop.zero_lt_top])
          εpos with ⟨g, hg, Pg⟩
      rw [← snorm_neg, neg_sub] at hg
      refine' ⟨g, _, Pg⟩
      convert hg
      ext x
      simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_zero,
        piecewise_eq_indicator, indicator_zero', Pi.zero_apply, indicator_zero]
    · have : μ s < ∞ := simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs Hs
      rcases h0P c hs this εpos with ⟨g, hg, Pg⟩
      rw [← snorm_neg, neg_sub] at hg
      exact ⟨g, hg, Pg⟩
  · intro f f' hff' hf hf' δ δpos int_ff'
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p δpos
    rw [simple_func.coe_add,
      mem_ℒp_add_of_disjoint hff' f.strongly_measurable f'.strongly_measurable] at int_ff'
    rcases hf η ηpos.ne' int_ff'.1 with ⟨g, hg, Pg⟩
    rcases hf' η ηpos.ne' int_ff'.2 with ⟨g', hg', Pg'⟩
    refine' ⟨g + g', _, h1P g g' Pg Pg'⟩
    convert(hη _ _ (f.ae_strongly_measurable.sub (h2P g Pg))
          (f'.ae_strongly_measurable.sub (h2P g' Pg')) hg hg').le
    abel
#align measure_theory.mem_ℒp.induction_dense MeasureTheory.Memℒp.induction_dense

section Integrable

-- mathport name: «expr →₁ₛ[ ] »
notation:25 α " →₁ₛ[" μ "] " E => @MeasureTheory.lp.simpleFunc α E _ _ 1 μ

theorem L1.SimpleFunc.toLp_one_eq_toL1 (f : α →ₛ E) (hf : Integrable f μ) :
    (lp.simpleFunc.toLp f (memℒp_one_iff_integrable.2 hf) : α →₁[μ] E) = hf.toL1 f :=
  rfl
#align measure_theory.L1.simple_func.to_Lp_one_eq_to_L1 MeasureTheory.L1.SimpleFunc.toLp_one_eq_toL1

protected theorem L1.SimpleFunc.integrable (f : α →₁ₛ[μ] E) :
    Integrable (lp.simpleFunc.toSimpleFunc f) μ := by rw [← mem_ℒp_one_iff_integrable];
  exact Lp.simple_func.mem_ℒp f
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
    ∀ ⦃f : α → E⦄ (hf : Integrable f μ), P f :=
  by
  simp only [← mem_ℒp_one_iff_integrable] at *
  exact mem_ℒp.induction one_ne_top P h_ind h_add h_closed h_ae
#align measure_theory.integrable.induction MeasureTheory.Integrable.induction

end Integrable

end MeasureTheory

