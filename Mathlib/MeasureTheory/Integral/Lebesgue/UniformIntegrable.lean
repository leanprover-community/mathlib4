/-
Copyright (c) 2026 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Hitting time and hitting map in measured dynamical systems
In this file, we define first hitting maps in measured dynamical systems.

## Main definitions
- `HitTime`: given a map `f : α → α` and a set `s`, the first positive time at which an iteration of
  `f` hits `s`. Its value is `0` if no iteration hits `s`.
- `HitMap`: given a map `f : α → α` and a set `s`, the point at which an iteration of `f` first hits
  `s`.
- `ExcursionSum` : given a map `f : α → α` a set `s` and an `ℝ≥0∞`-valued function `w` on `α`, the
  sum of `w` on an orbit until this orbit first hits `s`.

## Implementation notes
The hitting time of a set `s` for a point `x` under a transformation `f` is defined as the `sInf`
of all positive times `n` such that `f^[n] x ∈ s`. By default, `sInf ∅ = 0`. Hence, if the orbit
starting from `x` never returns to `s`, then `HitTime f s x = 0`. This convention differs from the
usual convention on the subject, for which `HitTime f s x = +∞` if the orbit starting from `x`
never returns to `s`. The convention adopted therein has some upsides (e.g. `HitMap` is defined
everywhere, `s` is stable under `HitMap`), but also some limitations one should keep in mind
(e.g. `HitTime f s` is not antitone in `s`).

## TODO
Prove:
- That `HitMap f s` is measure-preserving if `f` is measure-preserving and `s` recurrent.
- If possible, remove the hypothesis that `s` has finite measure in the previous theorem.
- Kac's lemma (or rather, its generalization for nonnegative functions): if `f` is
measure-preserving and `s` recurrent, then
`∫⁻ x in (⋃ n, f^[n] ⁻¹' s), w x ∂μ = ∫⁻ x in s, ExcursionSum f s x ∂μ`.

## Tags
hitting time, hitting map, induction, recurrent set
-/

public section

noncomputable section

namespace MeasureTheory

open ENNReal Filter Function Measure Set Topology

@[instance] theorem _root_.ENNReal.NeZero.top : NeZero ∞ := { out := zero_ne_top.symm }

variable {α ι : Type*} [MeasurableSpace α] {F G : ι → α → ℝ≥0∞} {μ : Measure α}

/-! ### Uniform integrability -/

def UnifLIntegrable (F : ι → α → ℝ≥0∞) (μ : Measure α) :=
  Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : μ A ≤ ε), ∫⁻ x in A, F i x ∂μ) (𝓝 0) (𝓝 0)

lemma unifLIntegrable_def :
    UnifLIntegrable F μ ↔ Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : μ A ≤ ε),
    ∫⁻ x in A, F i x ∂μ) (𝓝 0) (𝓝 0) := by rfl

lemma unifLIntegrable_mk :
    UnifLIntegrable F μ ↔ Tendsto (fun ε ↦ ⨆ (i : ι) (A : Set α) (_ : MeasurableSet A)
    (_ : μ A ≤ ε), ∫⁻ x in A, F i x ∂μ) (𝓝 0) (𝓝 0) := by
  rw [unifLIntegrable_def, iff_iff_eq]; congr 2; ext ε
  refine iSup_congr fun i ↦ le_antisymm (iSup₂_le fun A hAμ ↦ ?_) (iSup_mono fun A ↦ by simp)
  obtain ⟨B, hAB, hB, hBμ⟩ := exists_measurable_superset μ A
  rw [← hBμ] at hAμ
  apply (le_iSup _ B).trans'
  apply (le_iSup _ hB).trans'
  apply (le_iSup _ hAμ).trans'
  exact lintegral_mono_set hAB

lemma UnifLIntegrable.mono_ae (hG : UnifLIntegrable G μ) (h : ∀ i, F i ≤ᵐ[μ] G i) :
    UnifLIntegrable F μ := by
  rw [unifLIntegrable_mk] at hG ⊢
  refine tendsto_nhds_bot_mono hG (Eventually.of_forall fun a ↦ ?_)
  apply iSup_mono fun i ↦ iSup_mono fun A ↦ iSup_mono fun hA ↦ iSup_mono fun hAμ ↦ ?_
  exact lintegral_mono_ae (Eventually.filter_mono ae_restrict_le (h i))

lemma unifLIntegrable_congr_ae (h : ∀ i, F i =ᵐ[μ] G i) :
    UnifLIntegrable F μ ↔ UnifLIntegrable G μ :=
  ⟨fun h' ↦ h'.mono_ae fun i ↦ (h i).symm.le, fun h' ↦ h'.mono_ae fun i ↦ (h i).le⟩

lemma UnifLIntegrable.restrict (s : Set α) (h : UnifLIntegrable F μ) :
    UnifLIntegrable F (μ.restrict s) := by
  rw [unifLIntegrable_mk] at ⊢
  refine tendsto_nhds_bot_mono h (Eventually.of_forall fun a ↦ iSup_mono fun i ↦ ?_)
  simp only [iSup_le_iff]
  intro A hA hAμ
  rw [Measure.restrict_apply hA] at hAμ
  apply (le_iSup _ (A ∩ s)).trans_eq'
  rw [iSup_pos hAμ]
  simp [hA]

lemma UnifLIntegrable.tendsto_comp_set {A : ι → Set α} {l : Filter ι} (h : UnifLIntegrable F μ)
    (h' : Tendsto (μ ∘ A) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x in A i, F i x ∂μ) l (𝓝 0) := by
  have key := h.comp h'
  rw [← bot_eq_zero] at key ⊢
  refine tendsto_nhds_bot_mono' key (fun i ↦ ?_)
  simp only [comp_apply]
  apply (le_iSup _ i).trans'
  apply (le_iSup _ (A i)).trans'
  simp

lemma tendsto_iSup_setLIntegral_zero {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun ε ↦ ⨆ (A : Set α) (_ : μ A ≤ ε), ∫⁻ x in A, f x ∂μ) (𝓝 0) (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  rw [nhds_zero_basis.eventually_iff]
  obtain ⟨δ, hδ, hfδ⟩ := exists_pos_setLIntegral_lt_of_measure_lt h hε.ne.symm
  refine ⟨δ, hδ, fun a ha ↦ ?_⟩
  simp only [iSup_le_iff]
  exact fun s hs ↦ (hfδ s (hs.trans_lt (mem_Iio.1 ha))).le

lemma unifLIntegrable_empty [IsEmpty ι] : UnifLIntegrable F μ := by simp [UnifLIntegrable]

lemma unifLIntegrable_const {f : α → ℝ≥0∞} (h : ∀ i, F i = f) (h' : ∫⁻ x, f x ∂μ ≠ ∞) :
    UnifLIntegrable F μ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact unifLIntegrable_empty
  simp only [unifLIntegrable_def, h, ciSup_const]
  exact tendsto_iSup_setLIntegral_zero h'

lemma unifLIntegrable_of_finite [Finite ι] (h : ∀ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    UnifLIntegrable F μ := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have key := fun i ↦ tendsto_iSup_setLIntegral_zero (h i)
  simp only [ENNReal.tendsto_nhds_zero] at key
  filter_upwards [eventually_all.2 (fun i ↦ key i ε hε)] with a ha
  exact iSup_le ha

lemma UnifLIntegrable.add (h : ∀ i, AEMeasurable (G i) μ) (hF : UnifLIntegrable F μ)
    (hG : UnifLIntegrable G μ) :
    UnifLIntegrable (F + G) μ := by
  rw [unifLIntegrable_mk]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hF (ε / 2) (ε.half_pos hε.ne.symm),
    ENNReal.tendsto_nhds_zero.1 hG (ε / 2) (ε.half_pos hε.ne.symm)] with a haF haG
  simp only [iSup_le_iff, Pi.add_apply] at haF haG ⊢
  intro i A hA hAμ
  rw [← lintegral_indicator hA, indicator_add, lintegral_add_right' _ ((h i).indicator hA),
    lintegral_indicator hA, lintegral_indicator hA, ← ε.add_halves]
  exact add_le_add (haF i A hAμ) (haG i A hAμ)

/-! ### Uniform tails -/

def UniformTail (F : ι → α → ℝ≥0∞) (μ : Measure α) :=
  Tendsto (fun a ↦ ⨆ i, μ (F i ⁻¹' Ici a)) (𝓝 ∞) (𝓝 0)

lemma uniformTail_def :
    UniformTail F μ
      ↔ Tendsto (fun a ↦ ⨆ i, μ (F i ⁻¹' Ici a)) (𝓝 ∞) (𝓝 0) := by rfl

lemma UniformTail.mono_ae (h : ∀ i, F i ≤ᵐ[μ] G i) (h' : UniformTail G μ) :
    UniformTail F μ := by
  refine tendsto_nhds_bot_mono h' (Eventually.of_forall fun a ↦ ?_)
  refine iSup_mono fun i ↦ measure_mono_ae ?_
  filter_upwards [h i] with x hx hxF
  exact mem_Ici.2 ((mem_Ici.1 hxF).trans hx)

lemma uniformTail_congr_ae (h : ∀ i, F i =ᵐ[μ] G i) :
    UniformTail F μ ↔ UniformTail G μ :=
  ⟨fun h' ↦ h'.mono_ae fun i ↦ (h i).symm.le, fun h' ↦ h'.mono_ae fun i ↦ (h i).le⟩

lemma UniformTail.restrict (s : Set α) (h : UniformTail F μ) :
    UniformTail F (μ.restrict s) :=
  tendsto_nhds_bot_mono h (Eventually.of_forall fun _ ↦ iSup_mono fun _ ↦ μ.restrict_apply_le s _)

lemma uniformTail_of_lintegral_lt_top (h : ∀ i, AEMeasurable (F i) μ)
    (h' : ⨆ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    UniformTail F μ := by
  apply tendsto_nhds_bot_mono (f := fun a ↦ (⨆ i, ∫⁻ x, F i x ∂μ) / a)
  · have := Tendsto.const_div (a := ⨆ i, ∫⁻ x, F i x ∂μ) (b := ∞) tendsto_id (.inr h')
    simp only [id_eq, div_top] at this
    rwa [ENNReal.bot_eq_zero]
  · refine (eventually_gt_nhds zero_lt_top).mono fun a ha₀ ↦ ?_
    simp only [ENNReal.iSup_div]
    refine iSup_mono fun i ↦ ?_
    rcases eq_or_ne a ⊤ with rfl | ha
    · simp only [Ici_top, div_top, nonpos_iff_eq_zero]
      exact measure_eq_top_of_lintegral_ne_top (h i) ((le_iSup _ i).trans_lt h'.lt_top).ne
    · exact meas_ge_le_lintegral_div (h i) ha₀.ne.symm ha

lemma uniformTail_empty [IsEmpty ι] : UniformTail F μ := by simp [UniformTail]

lemma uniformTail_const {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf' : ∫⁻ x, f x ∂μ ≠ ∞)
    (h : ∀ i, F i = f) :
    UniformTail F μ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact uniformTail_empty
  · exact uniformTail_of_lintegral_lt_top (fun i ↦ (h i) ▸ hf) (by simpa [h])

lemma tendsto_measure_preimage_zero {f : α → ℝ≥0∞} (h : AEMeasurable f μ) (h' : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun a ↦ μ (f ⁻¹' Ici a)) (𝓝 ∞) (𝓝 0) := by
  suffices hF : UniformTail (ι := {g // g = f}) (fun g x ↦ g.1 x) μ by
    simp only [UniformTail, ciSup_unique] at hF
    exact hF
  exact uniformTail_const h h' (by simp)

lemma uniformTail_of_finite [Finite ι] (h : ∀ i, AEMeasurable (F i) μ)
    (h' : ∀ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    UniformTail F μ := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have key := fun i ↦ tendsto_measure_preimage_zero (h i) (h' i)
  simp only [ENNReal.tendsto_nhds_zero] at key
  filter_upwards [eventually_all.2 (fun i ↦ key i ε hε)] with a ha
  exact iSup_le ha

lemma UniformTail.add (hF : UniformTail F μ) (hG : UniformTail G μ) :
    UniformTail (F + G) μ := by
  -- If `c ≤ F i + G i`, then either `c / 2 ≤ F i` or `c / 2 ≤ G i`.
  -- By this observation, `{c ≤ F i + G i} ⊆ {c / 2 ≤ F i} ∪ {c / 2 ≤ G i}`,
  -- and we can control the measure of the latter set.
  rw [UniformTail, ENNReal.tendsto_nhds_zero] at hF hG ⊢
  intro ε hε
  obtain ⟨a, ha, haμ⟩ := _root_.nhds_top_basis.eventually_iff.1 (hF (ε / 2) (ε.half_pos hε.ne.symm))
  obtain ⟨b, hb, hbμ⟩ := _root_.nhds_top_basis.eventually_iff.1 (hG (ε / 2) (ε.half_pos hε.ne.symm))
  refine _root_.nhds_top_basis.eventually_iff.2 ⟨max (2 * a) (2 * b), ?_, fun c hc ↦ ?_⟩
  · exact (max_ne_top (mul_ne_top ofNat_ne_top ha.ne) (mul_ne_top ofNat_ne_top hb.ne)).lt_top
  simp only [mem_Ioi, sup_lt_iff, iSup_le_iff, Pi.add_apply] at hc haμ hbμ ⊢
  intro i
  apply le_trans (b := μ ((F i ⁻¹' Ici (c / 2)) ∪ G i ⁻¹' Ici (c / 2)))
  · refine measure_mono fun x ↦ ?_
    contrapose
    simp only [mem_union, mem_preimage, mem_Ici, not_or, not_le, Pi.add_apply, and_imp]
    exact fun hFx hGx ↦ (ENNReal.add_lt_add hFx hGx).trans_eq c.add_halves
  · rw [mul_comm 2 _, ← ENNReal.lt_div_iff_mul_lt (.inl two_ne_zero) (.inl ofNat_ne_top),
      mul_comm 2 _, ← ENNReal.lt_div_iff_mul_lt (.inl two_ne_zero) (.inl ofNat_ne_top)] at hc
    apply (measure_union_le _ _).trans
    exact (add_le_add (haμ hc.1 i) (hbμ hc.2 i)).trans_eq ε.add_halves

/-! ### Equi-integrability -/

def UniformLIntegrable (F : ι → α → ℝ≥0∞) (μ : Measure α) :=
  Tendsto (fun a ↦ ⨆ i, ∫⁻ x in F i ⁻¹' Ici a, F i x ∂μ) (𝓝 ∞) (𝓝 0)

lemma uniformLIntegrable_def :
    UniformLIntegrable F μ
      ↔ Tendsto (fun a ↦ ⨆ i, ∫⁻ x in F i ⁻¹' Ici a, F i x ∂μ) (𝓝 ∞) (𝓝 0) := by rfl

lemma UniformLIntegrable.mono_ae (hG : UniformLIntegrable G μ) (h : ∀ i, F i ≤ᵐ[μ] G i) :
    UniformLIntegrable F μ := by
  refine tendsto_nhds_bot_mono hG (Eventually.of_forall fun a ↦ iSup_mono fun i ↦ ?_)
  apply le_trans (b :=  ∫⁻ (x : α) in G i ⁻¹' Ici a, F i x ∂μ)
  · apply lintegral_mono_set'
    filter_upwards [h i] with x hx hxF
    exact mem_Ici.2 ((mem_Ici.1 hxF).trans hx)
  · exact lintegral_mono_ae (Eventually.filter_mono ae_restrict_le (h i))

lemma uniforLIntegrable_congr_ae (h : ∀ i, F i =ᵐ[μ] G i) :
    UniformLIntegrable F μ ↔ UniformLIntegrable G μ :=
  ⟨fun p ↦ p.mono_ae (fun i ↦ (h i).symm.le), fun p ↦ p.mono_ae (fun i ↦ (h i).le)⟩

lemma UniformLIntegrable.restrict (s : Set α) (h : UniformLIntegrable F μ) :
    UniformLIntegrable F (μ.restrict s) := by
  refine tendsto_nhds_bot_mono h (Eventually.of_forall fun a ↦ iSup_mono fun i ↦ ?_)
  exact lintegral_mono' (Measure.restrict_mono_measure μ.restrict_le_self _) (le_refl _)

-- Auxiliary lemma to prove that `UniformLIntegrable` families are `UnifLIntegrable`.
private lemma setLIntegral_le_add_lintegral (f : α → ℝ≥0∞) (A : Set α) (a : ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ ≤ a * μ A + ∫⁻ x in f ⁻¹' Ici a, f x ∂μ := by
  -- Without loss of generality, `A` can be assumed measurable.
  obtain ⟨B, hAB, hB, hBμ⟩ := exists_measurable_superset μ A
  apply (lintegral_mono_set hAB).trans
  rw [← hBμ]; clear hBμ hAB A
  -- We replace `f` by a measurable approximation `g` of `f`.
  obtain ⟨g, hg, hfg, hgμ⟩ := exists_measurable_le_lintegral_eq (μ.restrict B) f
  rw [hgμ]
  apply le_trans (b := a * μ B + ∫⁻ x in g ⁻¹' Ici a, g x ∂μ)
  -- Main argument : on `(g ⁻¹' Ici a)ᶜ`, the function `g` is bounded by `a`.
  · rw [← lintegral_inter_add_sdiff g B (.preimage (measurableSet_Ici (a := a)) hg), add_comm]
    apply add_le_add _ (lintegral_mono_set inter_subset_right)
    rw [← setLIntegral_const]
    apply (setLIntegral_mono (measurable_const (a := a)) (by grind)).trans
    exact lintegral_mono_set sdiff_subset
  -- We finally relate bound `∫⁻ x in g ⁻¹' Ici a, g x ∂μ` with `∫⁻ x in f ⁻¹' Ici a, f x ∂μ`.
  · apply add_le_add_right
    exact (lintegral_mono hfg).trans (lintegral_mono_set fun x hx ↦ hx.trans (Pi.le_def.1 hfg x))

lemma UniformLIntegrable.unifLIntegrable (h : UniformLIntegrable F μ) : UnifLIntegrable F μ := by
  -- The key is Lemma `setLIntegral_le_add_lintegral`.
  -- Choose `a` large enough that `∫⁻ x in f ⁻¹' Ici a, f x ∂μ` is small.
  -- Then, choose `μ A` small enough that `a * μ A` is also small.
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ nhds_zero_basis.eventually_iff.2 ?_
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨a, ha, haF⟩ :=
    ENNReal.nhds_top_basis.eventually_iff.1 (ENNReal.tendsto_nhds_zero.1 h δ hδ)
  obtain ⟨b, hab, hb⟩ := exists_between ha
  have hδε' : ε - δ ≠ 0 := fun p ↦ hδε.not_ge (tsub_eq_zero_iff_le.1 p)
  obtain ⟨κ, hκ, hκb⟩ := ENNReal.exists_pos_mul_lt hb.ne hδε'
  refine ⟨κ, hκ, fun γ hγ ↦ ?_⟩
  specialize haF (mem_Ioi.2 hab)
  simp only [iSup_le_iff] at haF ⊢
  intro i A hAμ
  apply (setLIntegral_le_add_lintegral (F i) A b).trans
  rw [← tsub_add_cancel_of_le hδε.le, mul_comm (a := b)]
  apply add_le_add (hκb.le.trans' _) (haF i)
  exact mul_le_mul_left (hAμ.trans (mem_Iio.1 hγ).le) b

lemma UniformLIntegrable.uniformTail (h : ∀ i, AEMeasurable (F i) μ) (h' : UniformLIntegrable F μ) :
    UniformTail F μ := by
  apply tendsto_nhds_bot_mono (f := fun a ↦ 1 / a)
  · have := Tendsto.const_div (a := 1) (b := ∞) tendsto_id (.inr one_ne_top)
    simp only [id_eq, div_top] at this
    exact this
  · filter_upwards [ENNReal.tendsto_nhds_zero.1 h' 1 zero_lt_one] with a ha
    simp only [iSup_le_iff, one_div, le_inv_iff_mul_le] at ha ⊢
    refine fun i ↦ (ha i).trans' ?_
    apply (iInf_mul_le_setLIntegral₀ _ ((h i).nullMeasurableSet_preimage (by measurability))).trans'
    rw [mul_comm]
    apply mul_le_mul_left
    simp

lemma UnifLIntegrable.uniformLIntegrable (h : UnifLIntegrable F μ) (h' : UniformTail F μ) :
    UniformLIntegrable F μ := by
  refine tendsto_nhds_bot_mono' (h.comp h') fun a ↦ ?_
  simp only [comp_apply, iSup_le_iff]
  intro i
  apply (le_iSup _ i).trans'
  apply (le_iSup _ ((F i) ⁻¹' Ici a)).trans'
  rw [iSup_pos]
  exact le_iSup (α := ℝ≥0∞) _ i

lemma uniformLIntegrable_iff_unifLIntegrable_uniformTail (h : ∀ i, AEMeasurable (F i) μ) :
    UniformLIntegrable F μ ↔ UnifLIntegrable F μ ∧ UniformTail F μ :=
  ⟨fun h' ↦ ⟨h'.unifLIntegrable, h'.uniformTail h⟩, fun h' ↦ h'.1.uniformLIntegrable h'.2⟩

lemma UniformLIntegrable.lintegral_lt_top_of_isFinite (h : IsFiniteMeasure μ)
    (hF : UniformLIntegrable F μ) :
    ⨆ i, ∫⁻ x, F i x ∂μ < ∞ := by
  have key := (ENNReal.tendsto_nhds_zero.1 hF 1 zero_lt_one).and_frequently (frequently_lt_nhds ∞)
  obtain ⟨a, ha, a_top⟩ := key.exists
  apply lt_of_le_of_lt (b := a * μ univ + 1)
  · simp only [iSup_le_iff] at ha ⊢
    intro i
    rw [← setLIntegral_univ (F i)]
    apply (setLIntegral_le_add_lintegral (F i) univ a).trans
    exact add_le_add_right (ha i) (a * μ univ)
  · exact add_lt_top.2 ⟨mul_lt_top a_top ((isFiniteMeasure_iff μ).1 h), one_lt_top⟩

lemma uniformLIntegrable_empty [IsEmpty ι] : UniformLIntegrable F μ := by simp [UniformLIntegrable]

lemma uniformLIntegrable_const {f : α → ℝ≥0∞} (h : ∀ i, F i = f) (hf : AEMeasurable f μ)
    (hf' : ∫⁻ x, f x ∂μ ≠ ∞) :
    UniformLIntegrable F μ :=
  (unifLIntegrable_const h hf').uniformLIntegrable (uniformTail_const hf hf' h)

lemma tendsto_setLIntegral_preimage_zero {f : α → ℝ≥0∞} (h : AEMeasurable f μ)
    (h' : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun a ↦ ∫⁻ x in f ⁻¹' Ici a, f x ∂μ) (𝓝 ∞) (𝓝 0) := by
  suffices hF : UniformLIntegrable (ι := {g // g = f}) (fun g x ↦ g.1 x) μ by
    simp only [UniformLIntegrable, ciSup_unique] at hF
    exact hF
  exact uniformLIntegrable_const (by simp) h h'

lemma _root_.Finite.uniformLIntegrable [Finite ι] (h : ∀ i, AEMeasurable (F i) μ)
    (h' : ∀ i, ∫⁻ x, F i x ∂μ ≠ ∞) :
    UniformLIntegrable F μ := by
  apply (uniformLIntegrable_iff_unifLIntegrable_uniformTail h).2
  exact ⟨unifLIntegrable_of_finite h', uniformTail_of_finite h h'⟩

lemma UniformLIntegrable.add (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hF' : UniformLIntegrable F μ) (hG' : UniformLIntegrable G μ) :
    UniformLIntegrable (F + G) μ := by
  rw [uniformLIntegrable_iff_unifLIntegrable_uniformTail (by simp [fun i ↦ (hF i).add (hG i)])]
  refine ⟨hF'.unifLIntegrable.add hG hG'.unifLIntegrable, ?_⟩
  exact (hF'.uniformTail hF).add (hG'.uniformTail hG)

end MeasureTheory
