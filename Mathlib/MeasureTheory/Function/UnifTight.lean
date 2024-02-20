/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
import Mathlib.Order.Filter.IndicatorFunction
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform tightness

This file contains the definitions for uniform tightness for a family of Lp functions.
It is used as a hypothesis to the version of Vitali's convergence theorem for Lp spaces
that works also for spaces of infinite measure. This version of Vitali's theorem
is also proved later in the file.

## Main definitions

* `MeasureTheory.UnifTight`:
  A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
  exists some measurable set `s` with finite measure such that the Lp-norm of
  `f i` restricted to `sᶜ` is smaller than `ε` for all `i`.

# Main results

* `MeasureTheory.unifTight_finite`: a finite sequence of Lp functions is uniformly
  tight.
* `MeasureTheory.tendsto_Lp_notFinite_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable and uniformly tight converges in Lp if they converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_notFinite_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable,
  uniformly tight and converges in measure.

## Tags
uniform integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/


namespace MeasureTheory

open Classical Set Filter Topology MeasureTheory NNReal ENNReal

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]


/- Counterpart of `tendsto_indicator_ge` from `MeasureTheory.Function.UniformIntegrable`.
   It is used in `lintegral_indicator_compl_le`, so it is more convenient
   to formulate it for `f` valued in `ENNReal`. Could be wrapped with `nnnorm` to make it
   more general. -/
theorem tendsto_ENNReal_indicator_lt (f : α → ℝ≥0∞) (x : α) :
    Tendsto (fun M : ℕ => { x | f x < 1 / (↑M + 1) }.indicator f x) atTop (𝓝 0) := by
  by_cases hfx : f x ≠ 0
  · refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (1 / f x).toReal) fun n hn => ?_
    rw [Set.indicator_of_not_mem]
    simp only [not_lt, Set.mem_setOf_eq, one_div, inv_le_iff_inv_le]
    simp only [one_div, ge_iff_le, Nat.ceil_le] at hn
    calc
      (f x)⁻¹ = .ofReal (f x)⁻¹.toReal := (ofReal_toReal (inv_ne_top.mpr hfx)).symm
      _       ≤ .ofReal n              := ENNReal.ofReal_le_ofReal hn
      _       = ↑n                     := by norm_cast
      _       ≤ ↑n + 1                 := by norm_num
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
    simp only [ne_eq, not_not] at hfx
    simp only [mem_setOf_eq, not_lt, indicator_apply_eq_zero]
    intro; assumption


section UnifTight

/- This follows closely the `UnifIntegrable` section
   from `MeasureTheory.Functions.UniformIntegrable`.-/

variable {f g : ι → α → β} {p : ℝ≥0∞}


/-- Definition of being Uniformly Tight. -/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ε

namespace UnifTight

theorem eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ s in μ.cofinite.smallSets, ∀ i, snorm (s.indicator (f i)) p μ ≤ ε := by
  rcases hf (pos_iff_ne_zero.2 hε) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i ↦ hfs i⟩
  · intro s t hst ht i
    exact (snorm_mono <| norm_indicator_le_of_subset hst _).trans (ht i)
  · rwa [Measure.compl_mem_cofinite, lt_top_iff_ne_top]

protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ε :=
  let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩

protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ := fun ε hε ↦ by
  rcases exists_Lp_half β μ p hε.ne' with ⟨η, hη_pos, hη⟩
  obtain ⟨s, hμs, hsm, hfs, hgs⟩ :
      ∃ s ∈ μ.cofinite, MeasurableSet s ∧
        (∀ i, snorm (s.indicator (f i)) p μ ≤ η) ∧ (∀ i, snorm (s.indicator (g i)) p μ ≤ η) :=
    ((hf.eventually_cofinite_indicator hη_pos.ne').and
      (hg.eventually_cofinite_indicator hη_pos.ne')).exists_measurable_mem_of_smallSets
  refine ⟨sᶜ, ne_of_lt hμs, fun i ↦ ?_⟩
  calc
    snorm (indicator sᶜᶜ (f i + g i)) p μ = snorm (indicator s (f i) + indicator s (g i)) p μ := by
      rw [compl_compl, indicator_add']
    _ ≤ ε := le_of_lt <|
      hη _ _ ((hf_meas i).indicator hsm) ((hg_meas i).indicator hsm)
        (hfs i) (hgs i)

protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ := by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', snorm_neg]
  exact hf

protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg


protected theorem ae_eq (hf : UnifTight f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight g p μ := by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| snorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, ite_not, hx]

end UnifTight


--XXX: this proof is rather hacked together, should be cleaned up
--     probably belongs in `Mathlib.Data.ENNReal.Operations`
theorem _root_.ENNReal.add_sub_add_comm {a b c d : ENNReal}
      (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) (hd : d ≠ ∞)
      (hac : c ≤ a) (hbd : d ≤ b) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  apply calc
    _ = _ := (ENNReal.ofReal_toReal _).symm
    _ = _ := ?cast_goal
    _ = _ := (ENNReal.ofReal_toReal _)
  case cast_goal =>
    rw [ENNReal.ofReal_eq_ofReal_iff toReal_nonneg toReal_nonneg]
    repeat rw [ENNReal.toReal_add ?_, ENNReal.toReal_sub_of_le ?_ ?_]
    linarith
    repeat tauto
    exact add_le_add hac hbd
    repeat aesop
  aesop
  aesop


/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral over any measurable set. -/
theorem exists_measurable_le_set_lintegral_eq_of_integrable {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞) :
    ∃ (g : α → ℝ≥0∞), Measurable g ∧ g ≤ f ∧ ∀ (s : Set α) (_hms : MeasurableSet s),
      ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  obtain ⟨g, hmg, hgf, hifg⟩ := exists_measurable_le_lintegral_eq (μ := μ) f
  use g, hmg, hgf
  intro s hms
  have hisf := (lintegral_add_compl (μ := μ) f hms).symm
  have hisg := (lintegral_add_compl (μ := μ) g hms).symm
  have := hisg ▸ hisf ▸ hifg
  have hisfg := hisf ▸ tsub_self (∫⁻ a, f a ∂μ)
  rw (config := { occs := .pos [2] }) [this] at hisfg
  replace hisf := add_ne_top.mp (hisf ▸ hf)
  replace hisg := add_ne_top.mp (hisg ▸ hifg ▸ hf)
  replace hisfg := _root_.ENNReal.add_sub_add_comm
    hisf.1 hisf.2 hisg.1 hisg.2 (lintegral_mono hgf) (lintegral_mono hgf) ▸ hisfg
  replace hisfg := (add_eq_zero.mp hisfg).left
  replace hisfg := tsub_eq_zero_iff_le.mp hisfg
  replace hisfg := le_antisymm hisfg (lintegral_mono hgf)
  use hisfg

/-- Core lemma to be used in `MeasureTheory.Memℒp.snorm_indicator_compl_le`. -/
theorem lintegral_indicator_compl_le
    {g : α → ℝ≥0∞} (hg : ∫⁻ a, g a ∂μ ≠ ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧
      ∫⁻ a in sᶜ, g a ∂μ ≤ ε := by
  -- come up with a measurable replacement `f` for `g`
  obtain ⟨f, hmf, _hfg, hsgf⟩ := exists_measurable_le_set_lintegral_eq_of_integrable hg
  replace hg := lt_top_iff_ne_top.mpr hg
  have hf := calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := μ.restrict_univ ▸ (hsgf univ (by measurability)).symm
    _            < ∞ := hg
  have hmeas_lt : ∀ M : ℕ, MeasurableSet { x | f x < 1 / (↑M + 1) } := by
    intro M
    apply measurableSet_lt hmf measurable_const
  have hmeas : ∀ M : ℕ, Measurable ({ x | f x < 1 / (↑M + 1) }.indicator f) := by
    intro M
    apply hmf.indicator
    apply hmeas_lt M
  -- show that the sequence a.e. converges to 0
  have htendsto :
      ∀ᵐ x ∂μ, Tendsto (fun M : ℕ => { x | f x < 1 / (↑M + 1) }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_ENNReal_indicator_lt f x)
  -- use Lebesgue dominated convergence to show that the integrals eventually go to zero
  have : Tendsto (fun n : ℕ ↦ ∫⁻ a, { x | f x < 1 / (↑n + 1) }.indicator f a ∂μ)
      atTop (𝓝 (∫⁻ (_ : α), 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence _ hmeas ?_ hf.ne htendsto
    -- show that the sequence is bounded by f (which is integrable)
    refine fun n => univ_mem' (id fun x => ?_)
    by_cases hx : f x < 1 / (↑n + 1)
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_not_mem]
      · exact zero_le _
      · assumption
  -- rewrite limit to be more usable and get the sufficiently large M, so the integral is < ε
  rw [lintegral_zero, ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this ε hε
  simp (config := { zeta := false } /- prevent let expansion -/)
    only [true_and_iff, ge_iff_le, zero_tsub, zero_le, sub_zero, zero_add, coe_nnnorm,
      Set.mem_Icc] at hM
  -- the target estimate is now in hM
  have hM := hM M le_rfl
  -- let s be the complement of the integration domain in hM,
  -- prove its measurability and finite measure
  have : { x | f x < 1 / (↑M + 1) } = { x | 1 / (↑M + 1) ≤ f x }ᶜ := by
    apply Set.ext; intro x
    simp only [mem_compl_iff, mem_setOf_eq, not_le]
  have hms := (hmeas_lt M).compl
  rw [this] at hM hms
  rw [compl_compl] at hms
  have hμs := calc
    μ { x | 1 / (↑M + 1) ≤ f x }
      ≤ (∫⁻ a, f a ∂μ) / (1 / (↑M + 1)) :=
        meas_ge_le_lintegral_div hmf.aemeasurable (by norm_num) (by norm_num)
    _ < ∞ := by apply div_lt_top hf.ne (by norm_num)
  set s := { x | 1 / (↑M + 1) ≤ f x }
  -- replace `f` by `g`
  rw [lintegral_indicator _ hms.compl, ← hsgf sᶜ hms.compl] at hM
  -- fulfill the goal
  use s, hms, hμs, hM

/-- A single function that is `Memℒp f p μ` is tight wrt to `μ`. -/
theorem Memℒp.snorm_indicator_compl_le (hp_top : p ≠ ∞)
    {f : α → β} (hf : Memℒp f p μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ snorm (sᶜ.indicator f) p μ ≤ ε := by
  -- The proof unwraps `Memℒp f p μ` and applies the analogous result for `lintegral`.
  by_cases hfinε : ε ≠ ∞; swap -- first take care of `ε = ∞`
  · rw [not_ne_iff.mp hfinε]; exact ⟨∅, by measurability⟩
  by_cases hp_nz : p ≠ 0; swap -- first take care of `p = 0`
  · simp only [ne_eq, not_not] at hp_nz
    use ∅, by measurability, by measurability
    simp only [compl_empty, indicator_univ]
    calc
      snorm f p μ = snorm f 0 μ := by congr
      _           = 0           := snorm_exponent_zero
      _           ≤ ε           := zero_le _
  -- do some arithmetic that will come in useful
  have hrp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_nz hp_top
  have hirp_pos : 0 < 1 / p.toReal := div_pos (by norm_num) hrp_pos
  have hεp : 0 < ε ^ p.toReal := ENNReal.rpow_pos hε hfinε
  -- decode Memℒp into a.e. strong measurability and finite snorm
  obtain ⟨_haesmf, hsnf⟩ := hf
  -- transform snorm to lintegral
  rw [snorm_eq_lintegral_rpow_nnnorm hp_nz hp_top] at hsnf
  replace hsnf := (rpow_lt_top_iff_of_pos hirp_pos).mp hsnf
  -- use core result for lintegral (needs only AEMeasurable), the target estimate will be in `hsfε`
  obtain ⟨s, hms, hμs, hsfε⟩ := lintegral_indicator_compl_le hsnf.ne hεp
  rw [← lintegral_indicator _ hms.compl] at hsfε
  use s, hms, hμs
  -- move indicator through function compositions, XXX: is this simp-able?
  rw [← Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal)] at hsfε
  rw [← Function.comp_def ENNReal.ofNNReal] at hsfε
  rw [← Function.comp_def nnnorm] at hsfε
  rw [sᶜ.indicator_comp_of_zero (@ENNReal.zero_rpow_of_pos p.toReal hrp_pos)] at hsfε
  rw [sᶜ.indicator_comp_of_zero ENNReal.coe_zero] at hsfε
  rw [sᶜ.indicator_comp_of_zero nnnorm_zero] at hsfε
  rw [Function.comp_def nnnorm] at hsfε
  rw [Function.comp_def ENNReal.ofNNReal] at hsfε
  rw [Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal)] at hsfε
  -- commute ENNReal coersion with rpow, use rpow monotonicity
  rw [← ENNReal.rpow_le_rpow_iff hirp_pos, ENNReal.rpow_inv_rpow_self hrp_pos.ne'] at hsfε
  -- convert lintegral to snorm
  rw [← snorm_eq_lintegral_rpow_nnnorm hp_nz hp_top] at hsfε
  exact hsfε

/-- A constant function is tight. -/
theorem unifTight_const {g : α → β} (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.snorm_indicator_compl_le hp_ne_top hε
  exact ⟨s, ne_of_lt hμs, fun _ => hgε⟩

/-- A single function is tight. -/
theorem unifTight_subsingleton [Subsingleton ι] (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by measurability, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
  case neg => exact ⟨∅, (by measurability), fun i => False.elim <| hι <| Nonempty.intro i⟩
  cases' hι with i
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).snorm_indicator_compl_le hp_top hε
  refine ⟨s, ne_of_lt hμs, fun j => ?_⟩
  convert hfε


/-- This lemma is less general than `MeasureTheory.unifTight_finite` which applies to
all sequences indexed by a finite type. -/
theorem unifTight_fin (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := by
  revert f
  induction' n with n h
  · intro f hf
    have : Subsingleton (Fin Nat.zero) := subsingleton_fin_zero -- Porting note: Added this instance
    exact unifTight_subsingleton hp_top hf
  intro f hfLp ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  let g : Fin n → α → β := fun k => f k
  have hgLp : ∀ i, Memℒp (g i) p μ := fun i => hfLp i
  obtain ⟨S, hμS, hFε⟩ := h hgLp hε
  obtain ⟨s, _, hμs, hfε⟩ := (hfLp n).snorm_indicator_compl_le hp_top hε
  refine ⟨s ∪ S, (by measurability), fun i => ?_⟩
  by_cases hi : i.val < n
  · rw [(_ : f i = g ⟨i.val, hi⟩)]
    · rw [compl_union, ← indicator_indicator]
      apply (snorm_indicator_le _).trans
      exact hFε (Fin.castLT i hi)
    · simp only [Fin.coe_eq_castSucc, Fin.castSucc_mk, Fin.eta]
  · rw [(_ : i = n)]
    · rw [compl_union, inter_comm, ← indicator_indicator]
      apply (snorm_indicator_le _).trans
      convert hfε
    · have hi' := Fin.is_lt i
      rw [Nat.lt_succ_iff] at hi'
      rw [not_lt] at hi
      -- Porting note: Original proof was `simp [← le_antisymm hi' hi]`
      ext; symm; rw [Fin.coe_ofNat_eq_mod, le_antisymm hi' hi, Nat.mod_succ_eq_iff_lt, Nat.lt_succ]

/-- A finite sequence of Lp functions is uniformly tight. -/
theorem unifTight_finite [Finite ι] (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  set g : Fin n → α → β := f ∘ hn.some.symm
  have hg : ∀ i, Memℒp (g i) p μ := fun _ => hf _
  obtain ⟨s, hμs, hfε⟩ := unifTight_fin hp_top hg hε
  refine ⟨s, hμs, fun i => ?_⟩
  specialize hfε (hn.some i)
  unfold_let g at hfε
  simp_rw [Function.comp_apply, Equiv.symm_apply_apply] at hfε
  assumption

end UnifTight


section VitaliConvergence

variable {μ : Measure α} {p : ℝ≥0∞}

variable {f : ℕ → α → β} {g : α → β}

/- Both directions and an iff version of Vitali's convergence theorem on measure spaces
   of not necesserily finite volume. See `Thm III.6.15` of Dunford & Schwartz, Part I (1958). -/

/- We start with the reverse direction. We only need to show that uniform tightness follows
   from convergence in Lp. Mathlib already has the analogous `unifIntegrable_of_tendsto_Lp`
   and `tendstoInMeasure_of_tendsto_snorm`. -/

/-- Intermediate lemma for `unifTight_of_tendsto_Lp`. -/
theorem unifTight_of_tendsto_Lp_zero (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => snorm (f n) p μ) atTop (𝓝 0)) : UnifTight f p μ := fun ε hε ↦by
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto ε (by simpa only [gt_iff_lt, ofReal_pos])
  let F : Fin N → α → β := fun n => f n
  have hF : ∀ n, Memℒp (F n) p μ := fun n => hf n
  obtain ⟨s, hμs, hFε⟩ := unifTight_fin hp' hF hε
  refine ⟨s, hμs, fun n => ?_⟩
  by_cases hn : n < N
  · exact hFε ⟨n, hn⟩
  · exact (snorm_indicator_le _).trans (hNε n (not_lt.mp hn))

/-- Convergence in Lp implies uniform tightness. -/
theorem unifTight_of_tendsto_Lp (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hg : Memℒp g p μ) (hfg : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifTight f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifTight.add ?_ ?_ (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp' (fun n => (hf n).sub hg) hfg


/- Next we deal with the forward direction. The `Memℒp` and `TendstoInMeasure` hypotheses
   are unwrapped and strengthened to by known lemmas to have in addition `StronglyMeasurable`
   and a.e. convergence. The bulk of the proof is done under these stronger hyptheses. -/

theorem tendsto_Lp_notFinite_of_tendsto_ae_of_meas (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε ≠ ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  by_cases hμ : μ = 0
  · rw [hμ]; use 0; intro n _; rw [snorm_measure_zero]; exact zero_le ε
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne' (coe_ne_top)
  -- use tightness to divide the domain into interior and exterior
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ := Memℒp.snorm_indicator_compl_le hp' hg' hε' --hrε'
  obtain ⟨Ef, hmEf, hμEf, hfε⟩ := hut.exists_measurableSet_indicator hε'.ne'
  have hmE := hmEf.union hmEg
  have hfmE := (measure_union_le Ef Eg).trans_lt (add_lt_top.mpr ⟨hμEf, hμEg⟩)
  set E : Set α := Ef ∪ Eg
  -- use uniform integrability to get control on the limit over E
  have hgE' := Memℒp.restrict E hg'
  have huiE := hui.restrict  E
  have hfgE : (∀ᵐ x ∂(μ.restrict E), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :=
    ae_restrict_of_ae hfg
  -- `tendsto_Lp_of_tendsto_ae_of_meas` needs to
  -- synthesize an argument `[IsFiniteMeasure (μ.restrict E)]`.
  -- It is enough to have in the context a term of `Fact (μ E < ∞)`, which is our `ffmE` below,
  -- which is automatically fed into `Restrict.isFiniteInstance`.
  have ffmE : Fact _ := { out := hfmE }
  have hInner := tendsto_Lp_of_tendsto_ae_of_meas hp hp' hf hg hgE' huiE hfgE
  rw [ENNReal.tendsto_atTop_zero] at hInner
  -- get a sufficiently large N for given ε, and consider any n ≥ N
  obtain ⟨N, hfngε⟩ := hInner (ε / 3) hε'
  use N; intro n hn
  -- get interior estimates
  have hmfngE : AEStronglyMeasurable _ μ := (((hf n).sub hg).indicator hmE).aestronglyMeasurable
  have hfngEε := calc
    snorm (E.indicator (f n - g)) p μ
      = snorm (f n - g) p (μ.restrict E) := snorm_indicator_eq_snorm_restrict hmE
    _ ≤ ε / 3                            := hfngε n hn
  -- get exterior estimates
  have hmgEc : AEStronglyMeasurable _ μ := (hg.indicator hmE.compl).aestronglyMeasurable
  have hgEcε := calc
    snorm (Eᶜ.indicator g) p μ
      ≤ snorm (Efᶜ.indicator (Egᶜ.indicator g)) p μ := by
        unfold_let E; rw [compl_union, ← indicator_indicator]
    _ ≤ snorm (Egᶜ.indicator g) p μ := snorm_indicator_le _
    _ ≤ ε / 3 := hgε
  have hmfnEc : AEStronglyMeasurable _ μ := ((hf n).indicator hmE.compl).aestronglyMeasurable
  have hfnEcε : snorm (Eᶜ.indicator (f n)) p μ ≤ ε / 3 := calc
    snorm (Eᶜ.indicator (f n)) p μ
      ≤ snorm (Egᶜ.indicator (Efᶜ.indicator (f n))) p μ := by
        unfold_let E; rw [compl_union, inter_comm, ← indicator_indicator]
    _ ≤ snorm (Efᶜ.indicator (f n)) p μ := snorm_indicator_le _
    _ ≤ ε / 3 := hfε n
  have hmfngEc : AEStronglyMeasurable _ μ :=
    (((hf n).sub hg).indicator hmE.compl).aestronglyMeasurable
  have hfngEcε := calc
    snorm (Eᶜ.indicator (f n - g)) p μ
      = snorm (Eᶜ.indicator (f n) - Eᶜ.indicator g) p μ := by
        rw [(Eᶜ.indicator_sub' _ _)]
    _ ≤ snorm (Eᶜ.indicator (f n)) p μ + snorm (Eᶜ.indicator g) p μ := by
        apply snorm_sub_le (by assumption) (by assumption) hp
    _ ≤ ε / 3 + ε / 3 := add_le_add hfnEcε hgEcε
  -- finally, combine interior and exterior estimates
  calc
    snorm (f n - g) p μ
      = snorm (Eᶜ.indicator (f n - g) + E.indicator (f n - g)) p μ := by
        congr; exact (E.indicator_compl_add_self _).symm
    _ ≤ snorm (indicator Eᶜ (f n - g)) p μ + snorm (indicator E (f n - g)) p μ := by
        apply snorm_add_le (by assumption) (by assumption) hp
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add hfngEcε hfngEε
    _ = ε := by simp only [ENNReal.add_thirds] --ENNReal.add_thirds ε

/- Lemma used in `tendsto_Lp_notFinite_of_tendsto_ae`.
   XXX: Alternative name: `ae_tendsto_ae_congr`? -/
theorem tendsto_ae_congr_ae {f f' : ℕ → α → β} {g g' : α → β}
    (hff' : ∀ (n : ℕ), f n =ᵐ[μ] f' n) (hgg' : g =ᵐ[μ] g')
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)) := by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx

theorem tendsto_Lp_notFinite_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.ae_eq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_mk
  have hgg' := hg'.aestronglyMeasurable.ae_eq_mk (μ := μ)
  have hg'' := hg'.ae_eq hgg'
  have haefg' := tendsto_ae_congr_ae hff' hgg' hfg
  set f' := fun n => (haef n).mk (μ := μ)
  set g' := hg'.aestronglyMeasurable.mk (μ := μ)
  have haefg (n : ℕ) : f n - g =ᵐ[μ] f' n - g' := (hff' n).sub hgg'
  have hsnfg (n : ℕ) := snorm_congr_ae (p := p) (haefg n)
  apply Filter.Tendsto.congr (fun n => (hsnfg n).symm)
  exact tendsto_Lp_notFinite_of_tendsto_ae_of_meas hp hp' hf hg hg'' hui' hut' haefg'


/-- Forward direction of Vitali's convergence theorem (non-finite version):
    if `f` is a sequence of uniformly integrable, uniformly tight functions that converge in
    measure to some function `g` in a finite measure space, then `f` converge in Lp to `g`. -/
theorem tendsto_Lp_notFinite_of_tendstoInMeasure (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Memℒp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_notFinite_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => -- `UnifIntegrable` on a subsequence
        let ⟨δ, hδ, hδ'⟩ := hui hε
        ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      (fun ε hε => -- `UnifTight` on a subsequence
        let ⟨s, hμs, hfε⟩ := hut hε
        ⟨s, hμs, fun i => hfε _⟩)
      hms'⟩


/-- **Vitali's convergence theorem** (non-finite measure version):
    A sequence of functions `f` converges to `g` in Lp
    if and only if it is uniformly integrable, uniformly tight and to `g` in measure. -/
-- XXX: logically, this should be renamed to `tendstoInMeasure_iff_tendsto_Lp`, while
--  the current version of that could be renamed to `tendstoInMeasure_iff_tendsto_Lp_of_isFinite`.
theorem tendstoInMeasure_notFinite_iff_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, Memℒp (f n) p μ) (hg : Memℒp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_notFinite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1,
    fun h =>
    ⟨tendstoInMeasure_of_tendsto_snorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h,
      unifTight_of_tendsto_Lp hp' hf hg h⟩⟩


end VitaliConvergence


end MeasureTheory
