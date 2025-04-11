/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Dominated convergence theorem

Lebesgue's dominated convergence theorem states that the limit and Lebesgue integral of
a sequence of (almost everywhere) measurable functions can be swapped if the functions are
pointwise dominated by a fixed function. This file provides a few variants of the result.
-/

open Filter ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} (g : α → ℝ≥0∞) (hf_meas : ∀ n, Measurable (f n))
    (h_bound : ∀ n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => f n a) atTop ∂μ :=
  calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ a, ⨆ i ≥ n, f i a ∂μ := iInf_mono fun _ => iSup₂_lintegral_le _
    _ = ∫⁻ a, ⨅ n : ℕ, ⨆ i ≥ n, f i a ∂μ := by
      refine (lintegral_iInf ?_ ?_ ?_).symm
      · intro n
        exact .biSup _ (Set.to_countable _) (fun i _ ↦ hf_meas i)
      · intro n m hnm a
        exact iSup_le_iSup_of_subset fun i hi => le_trans hnm hi
      · refine ne_top_of_le_ne_top h_fin (lintegral_mono_ae ?_)
        refine (ae_all_iff.2 h_bound).mono fun n hn => ?_
        exact iSup_le fun i => iSup_le fun _ => hn i
    _ = ∫⁻ a, limsup (fun n => f n a) atTop ∂μ := by simp only [limsup_eq_iInf_iSup_of_nat]

/-- **Dominated convergence theorem** for nonnegative `Measurable` functions. -/
theorem tendsto_lintegral_of_dominated_convergence {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : ℕ => F n a) atTop ∂μ :=
        lintegral_congr_ae <| h_lim.mono fun _ h => h.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : ℕ => ∫⁻ a, F n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => F n a) atTop ∂μ :=
        limsup_lintegral_le _ hF_meas h_bound h_fin
      _ = ∫⁻ a, f a ∂μ := lintegral_congr_ae <| h_lim.mono fun _ h => h.limsup_eq)

/-- **Dominated convergence theorem** for nonnegative `AEMeasurable` functions. -/
theorem tendsto_lintegral_of_dominated_convergence' {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, AEMeasurable (F n) μ) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) := by
  have : ∀ n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this
    filter_upwards [this, h_lim] with a H H'
    simp_rw [H]
    exact H'
  · intro n
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H'
    rwa [H'] at H

/-- **Dominated convergence theorem** for filters with a countable basis. -/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, Measurable (F n)) (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence ?_ ?_ ?_ ?_ ?_
  · exact bound
  · intro
    refine (h _ ?_).1
    exact Nat.le_add_left _ _
  · intro
    refine (h _ ?_).2
    exact Nat.le_add_left _ _
  · assumption
  · refine h_lim.mono fun a h_lim => ?_
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rw [tendsto_add_atTop_iff_nat]
    assumption

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. Auxiliary version assuming moreover that the
functions in the sequence are ae measurable. -/
lemma tendsto_of_lintegral_tendsto_of_monotone_aux {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hf_meas : ∀ n, AEMeasurable (f n) μ) (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) (h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have h_bound_finite : ∀ᵐ a ∂μ, F a ≠ ∞ := by
    filter_upwards [ae_lt_top' hF_meas h_int_finite] with a ha using ha.ne
  have h_exists : ∀ᵐ a ∂μ, ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := by
    filter_upwards [h_bound, h_bound_finite, hf_mono] with a h_le h_fin h_mono
    have h_tendsto : Tendsto (fun i ↦ f i a) atTop atTop ∨
        ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := tendsto_of_monotone h_mono
    rcases h_tendsto with h_absurd | h_tendsto
    · rw [tendsto_atTop_atTop_iff_of_monotone h_mono] at h_absurd
      obtain ⟨i, hi⟩ := h_absurd (F a + 1)
      refine absurd (hi.trans (h_le _)) (not_le.mpr ?_)
      exact ENNReal.lt_add_right h_fin one_ne_zero
    · exact h_tendsto
  classical
  let F' : α → ℝ≥0∞ := fun a ↦ if h : ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F' ≤ᵐ[μ] F := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact le_of_tendsto' h_tendsto (fun m ↦ h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ from
    ae_eq_of_ae_le_of_lintegral_le hF'_le (this ▸ h_int_finite) hF_meas this.symm.le
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_monotone hf_meas hf_mono hF'_tendsto

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
lemma tendsto_of_lintegral_tendsto_of_monotone {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) (h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f n ∧ ∫⁻ a, f n a ∂μ = ∫⁻ a, g a ∂μ :=
    fun n ↦ exists_measurable_le_lintegral_eq _ _
  choose g gmeas gf hg using this
  let g' : ℕ → α → ℝ≥0∞ := Nat.rec (g 0) (fun n I x ↦ max (g (n+1) x) (I x))
  have M n : Measurable (g' n) := by
    induction n with
    | zero => simp [g', gmeas 0]
    | succ n ih => exact Measurable.max (gmeas (n+1)) ih
  have I : ∀ n x, g n x ≤ g' n x := by
    intro n x
    cases n with | zero | succ => simp [g']
  have I' : ∀ᵐ x ∂μ, ∀ n, g' n x ≤ f n x := by
    filter_upwards [hf_mono] with x hx n
    induction n with
    | zero => simpa [g'] using gf 0 x
    | succ n ih => exact max_le (gf (n+1) x) (ih.trans (hx (Nat.le_succ n)))
  have Int_eq n : ∫⁻ x, g' n x ∂μ = ∫⁻ x, f n x ∂μ := by
    apply le_antisymm
    · apply lintegral_mono_ae
      filter_upwards [I'] with x hx using hx n
    · rw [hg n]
      exact lintegral_mono (I n)
  have : ∀ᵐ a ∂μ, Tendsto (fun i ↦ g' i a) atTop (𝓝 (F a)) := by
    apply tendsto_of_lintegral_tendsto_of_monotone_aux _ hF_meas _ _ _ h_int_finite
    · exact fun n ↦ (M n).aemeasurable
    · simp_rw [Int_eq]
      exact hf_tendsto
    · exact Eventually.of_forall (fun x ↦ monotone_nat_of_le_succ (fun n ↦ le_max_right _ _))
    · filter_upwards [h_bound, I'] with x h'x hx n using (hx n).trans (h'x n)
  filter_upwards [this, I', h_bound] with x hx h'x h''x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds h'x h''x

/-- If an antitone sequence of functions has a lower bound and the sequence of integrals of these
functions tends to the integral of the lower bound, then the sequence of functions converges
almost everywhere to the lower bound. -/
lemma tendsto_of_lintegral_tendsto_of_antitone {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hf_meas : ∀ n, AEMeasurable (f n) μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, F a ≤ f i a) (h0 : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞ := by
    refine ((lintegral_mono_ae ?_).trans_lt h0.lt_top).ne
    filter_upwards [h_bound] with a ha using ha 0
  have h_exists : ∀ᵐ a ∂μ, ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := by
    filter_upwards [hf_mono] with a h_mono
    rcases _root_.tendsto_of_antitone h_mono with h | h
    · refine ⟨0, h.mono_right ?_⟩
      rw [OrderBot.atBot_eq]
      exact pure_le_nhds _
    · exact h
  classical
  let F' : α → ℝ≥0∞ := fun a ↦ if h : ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F ≤ᵐ[μ] F' := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact ge_of_tendsto' h_tendsto (fun m ↦ h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ by
    refine (ae_eq_of_ae_le_of_lintegral_le hF'_le h_int_finite ?_ this.le).symm
    exact ENNReal.aemeasurable_of_tendsto hf_meas hF'_tendsto
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_antitone hf_meas hf_mono h0 hF'_tendsto

end MeasureTheory
