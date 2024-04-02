/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
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

/-- A constant function is tight. -/
theorem unifTight_const {g : α → β} (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by measurability), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_snorm_indicator_compl_lt hp_ne_top hε.ne'
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩

/-- A single function is tight. -/
theorem unifTight_subsingleton [Subsingleton ι] (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := fun ε hε ↦ by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by measurability, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
  case neg => exact ⟨∅, (by measurability), fun i => False.elim <| hι <| Nonempty.intro i⟩
  cases' hι with i
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_snorm_indicator_compl_lt hp_top hε.ne'
  refine ⟨s, ne_of_lt hμs, fun j => ?_⟩
  convert hfε.le


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
  obtain ⟨s, _, hμs, hfε⟩ := (hfLp n).exists_snorm_indicator_compl_lt hp_top hε.ne'
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
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ := Memℒp.exists_snorm_indicator_compl_lt hp' hg' hε'.ne' --hrε'
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
    _ ≤ ε / 3 := hgε.le
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
