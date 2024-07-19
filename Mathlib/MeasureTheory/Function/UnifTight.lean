/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
import Mathlib.MeasureTheory.Function.LpSpace

/-!
# Uniform tightness

This file contains the definitions for uniform tightness for a family of Lp functions.
It is used as a hypothesis to the version of Vitali's convergence theorem for Lp spaces
that works also for spaces of infinite measure.

## Main definitions

* `MeasureTheory.UnifTight`:
  A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
  exists some measurable set `s` with finite measure such that the Lp-norm of
  `f i` restricted to `sᶜ` is smaller than `ε` for all `i`.

# Main results

* `MeasureTheory.unifTight_finite`: a finite sequence of Lp functions is uniformly
  tight.

## Tags

uniform integrable, uniformly tight, Vitali convergence theorem
-/


namespace MeasureTheory

open Classical Set Filter Topology MeasureTheory NNReal ENNReal

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]



section UnifTight

/- This follows closely the `UnifIntegrable` section
from `MeasureTheory.Functions.UniformIntegrable`.-/

variable {f g : ι → α → β} {p : ℝ≥0∞}


/-- A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
exists some measurable set `s` with finite measure such that the Lp-norm of
`f i` restricted to `sᶜ` is smaller than `ε` for all `i`. -/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ε

theorem unifTight_iff_ennreal {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
    UnifTight f p μ ↔ ∀ ⦃ε : ℝ≥0∞⦄, 0 < ε → ∃ s : Set α,
      μ s ≠ ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ε := by
  simp only [ENNReal.forall_ennreal, ENNReal.coe_pos]
  refine (and_iff_left ?_).symm
  simp [-ne_eq, zero_lt_top, le_top]
  use ∅; simpa only [measure_empty] using zero_ne_top

theorem unifTight_iff_real {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) :
    UnifTight f p μ ↔ ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ s : Set α,
      μ s ≠ ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ .ofReal ε := by
  refine ⟨fun hut rε hrε ↦ hut (Real.toNNReal_pos.mpr hrε), fun hut ε hε ↦ ?_⟩
  obtain ⟨s, hμs, hfε⟩ := hut hε
  use s, hμs; intro i
  exact (hfε i).trans_eq (ofReal_coe_nnreal (p := ε))

namespace UnifTight

theorem eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∀ᶠ s in μ.cofinite.smallSets, ∀ i, snorm (s.indicator (f i)) p μ ≤ ε := by
  rcases hf (pos_iff_ne_zero.2 hε) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i ↦ hfs i⟩
  · intro s t hst ht i
    exact (snorm_mono <| norm_indicator_le_of_subset hst _).trans (ht i)
  · rwa [Measure.compl_mem_cofinite, lt_top_iff_ne_top]

protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ε :=
  let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩

protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ := fun ε hε ↦ by
  rcases exists_Lp_half β μ p (coe_ne_zero.mpr hε.ne') with ⟨η, hη_pos, hη⟩
  by_cases hη_top : η = ∞
  · replace hη := hη_top ▸ hη
    refine ⟨∅, (by measurability), fun i ↦ ?_⟩
    simp only [compl_empty, indicator_univ, Pi.add_apply]
    exact (hη (f i) (g i) (hf_meas i) (hg_meas i) le_top le_top).le
  have nnη_nz := (toNNReal_ne_zero.mpr ⟨hη_pos.ne',hη_top⟩)
  obtain ⟨s, hμs, hsm, hfs, hgs⟩ :
      ∃ s ∈ μ.cofinite, MeasurableSet s ∧
        (∀ i, snorm (s.indicator (f i)) p μ ≤ η.toNNReal) ∧
        (∀ i, snorm (s.indicator (g i)) p μ ≤ η.toNNReal) :=
    ((hf.eventually_cofinite_indicator nnη_nz).and
      (hg.eventually_cofinite_indicator nnη_nz)).exists_measurable_mem_of_smallSets
  refine ⟨sᶜ, ne_of_lt hμs, fun i ↦ ?_⟩
  have η_cast : ↑η.toNNReal = η := coe_toNNReal hη_top
  calc
    snorm (indicator sᶜᶜ (f i + g i)) p μ = snorm (indicator s (f i) + indicator s (g i)) p μ := by
      rw [compl_compl, indicator_add']
    _ ≤ ε := le_of_lt <|
      hη _ _ ((hf_meas i).indicator hsm) ((hg_meas i).indicator hsm)
        (η_cast ▸ hfs i) (η_cast ▸ hgs i)

protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ := by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', snorm_neg]
  exact hf

protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg

protected theorem aeeq (hf : UnifTight f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight g p μ := by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| snorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, ite_not, hx]

end UnifTight

/-- If two functions agree a.e., then one is tight iff the other is tight. -/
theorem unifTight_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight f p μ ↔ UnifTight g p μ :=
  ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩

/-- A constant sequence is tight. -/
theorem unifTight_const {g : α → β} (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_snorm_indicator_compl_lt hp_ne_top (coe_ne_zero.mpr hε.ne')
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩

/-- A single function is tight. -/
theorem unifTight_of_subsingleton [Subsingleton ι] (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by measurability, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
  case neg => exact ⟨∅, (by measurability), fun i => False.elim <| hι <| Nonempty.intro i⟩
  cases' hι with i
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_snorm_indicator_compl_lt hp_top (coe_ne_zero.mpr hε.ne')
  refine ⟨s, ne_of_lt hμs, fun j => ?_⟩
  convert hfε.le

/-- This lemma is less general than `MeasureTheory.unifTight_finite` which applies to
all sequences indexed by a finite type. -/
private theorem unifTight_fin (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := by
  revert f
  induction' n with n h
  · intro f hf
    have : Subsingleton (Fin Nat.zero) := subsingleton_fin_zero -- Porting note: Added this instance
    exact unifTight_of_subsingleton hp_top hf
  intro f hfLp ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  let g : Fin n → α → β := fun k => f k
  have hgLp : ∀ i, Memℒp (g i) p μ := fun i => hfLp i
  obtain ⟨S, hμS, hFε⟩ := h hgLp hε
  obtain ⟨s, _, hμs, hfε⟩ :=(hfLp n).exists_snorm_indicator_compl_lt hp_top (coe_ne_zero.mpr hε.ne')
  refine ⟨s ∪ S, (by measurability), fun i => ?_⟩
  by_cases hi : i.val < n
  · rw [(_ : f i = g ⟨i.val, hi⟩)]
    · rw [compl_union, ← indicator_indicator]
      apply (snorm_indicator_le _).trans
      exact hFε (Fin.castLT i hi)
    · simp only [Fin.coe_eq_castSucc, Fin.castSucc_mk, g]
  · rw [(_ : i = n)]
    · rw [compl_union, inter_comm, ← indicator_indicator]
      apply (snorm_indicator_le _).trans
      convert hfε.le
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
  simpa only [g, Function.comp_apply, Equiv.symm_apply_apply] using hfε (hn.some i)

end UnifTight

end MeasureTheory
