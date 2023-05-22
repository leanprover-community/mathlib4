/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.constructions.borel_space.metrizable
! leanprover-community/mathlib commit bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic
import Mathbin.Topology.MetricSpace.Metrizable

/-!
# Measurable functions in (pseudo-)metrizable Borel spaces
-/


open Filter MeasureTheory TopologicalSpace

open Classical Topology NNReal ENNReal MeasureTheory

variable {α β : Type _} [MeasurableSpace α]

section Limits

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]

open Metric

/-- A limit (over a general filter) of measurable `ℝ≥0∞` valued functions is measurable. -/
theorem measurable_of_tendsto_ennreal' {ι} {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} (u : Filter ι)
    [NeBot u] [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  rcases u.exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_pi_nhds] at lim
  have : (fun y => liminf (fun n => (f (x n) y : ℝ≥0∞)) at_top) = g :=
    by
    ext1 y
    exact ((limUnder y).comp hx).liminf_eq
  rw [← this]
  show Measurable fun y => liminf (fun n => (f (x n) y : ℝ≥0∞)) at_top
  exact measurable_liminf fun n => hf (x n)
#align measurable_of_tendsto_ennreal' measurable_of_tendsto_ennreal'

/-- A sequential limit of measurable `ℝ≥0∞` valued functions is measurable. -/
theorem measurable_of_tendsto_eNNReal {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_ennreal' atTop hf limUnder
#align measurable_of_tendsto_ennreal measurable_of_tendsto_eNNReal

/-- A limit (over a general filter) of measurable `ℝ≥0` valued functions is measurable. -/
theorem measurable_of_tendsto_nnreal' {ι} {f : ι → α → ℝ≥0} {g : α → ℝ≥0} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  simp_rw [← measurable_coe_nnreal_ennreal_iff] at hf⊢
  refine' measurable_of_tendsto_ennreal' u hf _
  rw [tendsto_pi_nhds] at lim⊢
  exact fun x => (ennreal.continuous_coe.tendsto (g x)).comp (limUnder x)
#align measurable_of_tendsto_nnreal' measurable_of_tendsto_nnreal'

/-- A sequential limit of measurable `ℝ≥0` valued functions is measurable. -/
theorem measurable_of_tendsto_nNReal {f : ℕ → α → ℝ≥0} {g : α → ℝ≥0} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_nnreal' atTop hf limUnder
#align measurable_of_tendsto_nnreal measurable_of_tendsto_nNReal

/-- A limit (over a general filter) of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
theorem measurable_of_tendsto_metrizable' {ι} {f : ι → α → β} {g : α → β} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g :=
  by
  letI : PseudoMetricSpace β := pseudo_metrizable_space_pseudo_metric β
  apply measurable_of_is_closed'
  intro s h1s h2s h3s
  have : Measurable fun x => inf_nndist (g x) s :=
    by
    suffices : tendsto (fun i x => inf_nndist (f i x) s) u (𝓝 fun x => inf_nndist (g x) s)
    exact measurable_of_tendsto_nnreal' u (fun i => (hf i).infNndist) this
    rw [tendsto_pi_nhds] at lim⊢
    intro x
    exact ((continuous_inf_nndist_pt s).Tendsto (g x)).comp (limUnder x)
  have h4s : g ⁻¹' s = (fun x => inf_nndist (g x) s) ⁻¹' {0} :=
    by
    ext x
    simp [h1s, ← h1s.mem_iff_inf_dist_zero h2s, ← NNReal.coe_eq_zero]
  rw [h4s]
  exact this (measurable_set_singleton 0)
#align measurable_of_tendsto_metrizable' measurable_of_tendsto_metrizable'

/-- A sequential limit of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
theorem measurable_of_tendsto_metrizable {f : ℕ → α → β} {g : α → β} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_metrizable' atTop hf limUnder
#align measurable_of_tendsto_metrizable measurable_of_tendsto_metrizable

theorem aEMeasurable_of_tendsto_metrizable_ae {ι} {μ : Measure α} {f : ι → α → β} {g : α → β}
    (u : Filter ι) [hu : NeBot u] [IsCountablyGenerated u] (hf : ∀ n, AEMeasurable (f n) μ)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) : AEMeasurable g μ :=
  by
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  have h'f : ∀ n, AEMeasurable (f (v n)) μ := fun n => hf (v n)
  set p : α → (ℕ → β) → Prop := fun x f' => tendsto (fun n => f' n) at_top (𝓝 (g x))
  have hp : ∀ᵐ x ∂μ, p x fun n => f (v n) x := by
    filter_upwards [h_tendsto]with x hx using hx.comp hv
  set ae_seq_lim := fun x => ite (x ∈ aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty β).some with hs
  refine'
    ⟨ae_seq_lim,
      measurable_of_tendsto_metrizable' at_top (aeSeq.measurable h'f p)
        (tendsto_pi_nhds.mpr fun x => _),
      _⟩
  · simp_rw [aeSeq, ae_seq_lim]
    split_ifs with hx
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      exact @aeSeq.fun_prop_of_mem_aeSeqSet _ α β _ _ _ _ _ h'f x hx
    · exact tendsto_const_nhds
  ·
    exact
      (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨f (v 0) x⟩ : Nonempty β).some) (aeSeqSet h'f p)
          (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm
#align ae_measurable_of_tendsto_metrizable_ae aEMeasurable_of_tendsto_metrizable_ae

theorem aEMeasurable_of_tendsto_metrizable_ae' {μ : Measure α} {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : AEMeasurable g μ :=
  aEMeasurable_of_tendsto_metrizable_ae atTop hf h_ae_tendsto
#align ae_measurable_of_tendsto_metrizable_ae' aEMeasurable_of_tendsto_metrizable_ae'

theorem aEMeasurable_of_unif_approx {β} [MeasurableSpace β] [PseudoMetricSpace β] [BorelSpace β]
    {μ : Measure α} {g : α → β}
    (hf : ∀ ε > (0 : ℝ), ∃ f : α → β, AEMeasurable f μ ∧ ∀ᵐ x ∂μ, dist (f x) (g x) ≤ ε) :
    AEMeasurable g μ :=
  by
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  choose f Hf using fun n : ℕ => hf (u n) (u_pos n)
  have : ∀ᵐ x ∂μ, tendsto (fun n => f n x) at_top (𝓝 (g x)) :=
    by
    have : ∀ᵐ x ∂μ, ∀ n, dist (f n x) (g x) ≤ u n := ae_all_iff.2 fun n => (Hf n).2
    filter_upwards [this]
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hx u_lim
  exact aEMeasurable_of_tendsto_metrizable_ae' (fun n => (Hf n).1) this
#align ae_measurable_of_unif_approx aEMeasurable_of_unif_approx

theorem measurable_of_tendsto_metrizable_ae {μ : Measure α} [μ.IsComplete] {f : ℕ → α → β}
    {g : α → β} (hf : ∀ n, Measurable (f n))
    (h_ae_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g :=
  aemeasurable_iff_measurable.mp
    (aEMeasurable_of_tendsto_metrizable_ae' (fun i => (hf i).AEMeasurable) h_ae_tendsto)
#align measurable_of_tendsto_metrizable_ae measurable_of_tendsto_metrizable_ae

theorem measurable_limit_of_tendsto_metrizable_ae {ι} [Countable ι] [Nonempty ι] {μ : Measure α}
    {f : ι → α → β} {L : Filter ι} [L.IsCountablyGenerated] (hf : ∀ n, AEMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) L (𝓝 l)) :
    ∃ (f_lim : α → β)(hf_lim_meas : Measurable f_lim),
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) :=
  by
  inhabit ι
  rcases eq_or_ne L ⊥ with (rfl | hL)
  · exact ⟨(hf default).mk _, (hf default).measurable_mk, eventually_of_forall fun x => tendsto_bot⟩
  haveI : ne_bot L := ⟨hL⟩
  let p : α → (ι → β) → Prop := fun x f' => ∃ l : β, tendsto (fun n => f' n) L (𝓝 l)
  have hp_mem : ∀ x ∈ aeSeqSet hf p, p x fun n => f n x := fun x hx =>
    aeSeq.fun_prop_of_mem_aeSeqSet hf hx
  have h_ae_eq : ∀ᵐ x ∂μ, ∀ n, aeSeq hf p n x = f n x := aeSeq.aeSeq_eq_fun_ae hf h_ae_tendsto
  let f_lim : α → β := fun x =>
    dite (x ∈ aeSeqSet hf p) (fun h => (hp_mem x h).some) fun h => (⟨f default x⟩ : Nonempty β).some
  have hf_lim : ∀ x, tendsto (fun n => aeSeq hf p n x) L (𝓝 (f_lim x)) :=
    by
    intro x
    simp only [f_lim, aeSeq]
    split_ifs
    · refine' (hp_mem x h).choose_spec.congr fun n => _
      exact (aeSeq.mk_eq_fun_of_mem_aeSeqSet hf h n).symm
    · exact tendsto_const_nhds
  have h_ae_tendsto_f_lim : ∀ᵐ x ∂μ, tendsto (fun n => f n x) L (𝓝 (f_lim x)) :=
    h_ae_eq.mono fun x hx => (hf_lim x).congr hx
  have h_f_lim_meas : Measurable f_lim :=
    measurable_of_tendsto_metrizable' L (aeSeq.measurable hf p)
      (tendsto_pi_nhds.mpr fun x => hf_lim x)
  exact ⟨f_lim, h_f_lim_meas, h_ae_tendsto_f_lim⟩
#align measurable_limit_of_tendsto_metrizable_ae measurable_limit_of_tendsto_metrizable_ae

end Limits

