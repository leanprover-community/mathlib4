/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Functions which vanish as distributions vanish as functions

In a finite-dimensional normed real vector space endowed with a Borel measure, consider a locally
integrable function whose integral against all compactly supported smooth functions vanishes. Then
the function is almost everywhere zero.
This is proved in `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

A version for two functions having the same integral when multiplied by smooth compactly supported
functions is also given in `ae_eq_of_integral_contDiff_smul_eq`.

These are deduced from the same results on finite-dimensional real manifolds, given respectively
as `ae_eq_zero_of_integral_contMDiff_smul_eq_zero` and `ae_eq_of_integral_contMDiff_smul_eq`.
-/

@[expose] public section

open MeasureTheory Filter Metric Function Set TopologicalSpace

open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Manifold

variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M]
  {f f' : M → F} {μ : Measure M}

/-- If a locally integrable function `f` on a finite-dimensional real manifold has zero integral
when multiplied by any smooth compactly supported function, then `f` vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_contMDiff_smul_eq_zero [SigmaCompactSpace M]
    (hf : LocallyIntegrable f μ)
    (h : ∀ g : M → ℝ, CMDiff ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 := by
  -- record topological properties of `M`
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  -- it suffices to show that the integral of the function vanishes on any compact set `s`
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hf (fun s hs ↦ Eq.symm ?_)
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ IsCompact (cthickening δ s) := hs.exists_isCompact_cthickening
  -- choose a sequence of smooth functions `gₙ` equal to `1` on `s` and vanishing outside of the
  -- `uₙ`-neighborhood of `s`, where `uₙ` tends to zero. Then each integral `∫ gₙ f` vanishes,
  -- and by dominated convergence these integrals converge to `∫ x in s, f`.
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 δ)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' δpos
  let v : ℕ → Set M := fun n ↦ thickening (u n) s
  obtain ⟨K, K_compact, vK⟩ : ∃ K, IsCompact K ∧ ∀ n, v n ⊆ K :=
    ⟨_, hδ, fun n ↦ thickening_subset_cthickening_of_le (u_pos n).2.le _⟩
  have : ∀ n, ∃ (g : M → ℝ), support g = v n ∧ CMDiff ∞ g ∧ Set.range g ⊆ Set.Icc 0 1
          ∧ ∀ x ∈ s, g x = 1 := by
    intro n
    rcases exists_contMDiff_support_eq_eq_one_iff I isOpen_thickening hs.isClosed
      (self_subset_thickening (u_pos n).1 s) with ⟨g, g_smooth, g_range, g_supp, hg⟩
    exact ⟨g, g_supp, g_smooth, g_range, fun x hx ↦ (hg x).1 hx⟩
  choose g g_supp g_diff g_range hg using this
  -- main fact: the integral of `∫ gₙ f` tends to `∫ x in s, f`.
  have L : Tendsto (fun n ↦ ∫ x, g n x • f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    rw [← integral_indicator hs.measurableSet]
    let bound : M → ℝ := K.indicator (fun x ↦ ‖f x‖)
    have A : ∀ n, AEStronglyMeasurable (fun x ↦ g n x • f x) μ :=
      fun n ↦ (g_diff n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable
    have B : Integrable bound μ := by
      rw [integrable_indicator_iff K_compact.measurableSet]
      exact (hf.integrableOn_isCompact K_compact).norm
    have C : ∀ n, ∀ᵐ x ∂μ, ‖g n x • f x‖ ≤ bound x := by
      intro n
      filter_upwards with x
      rw [norm_smul]
      refine le_indicator_apply (fun _ ↦ ?_) (fun hxK ↦ ?_)
      · have : ‖g n x‖ ≤ 1 := by
          have := g_range n (mem_range_self (f := g n) x)
          rw [Real.norm_of_nonneg this.1]
          exact this.2
        exact mul_le_of_le_one_left (norm_nonneg _) this
      · have : g n x = 0 := by rw [← notMem_support, g_supp]; contrapose! hxK; exact vK n hxK
        simp [this]
    have D : ∀ᵐ x ∂μ, Tendsto (fun n => g n x • f x) atTop (𝓝 (s.indicator f x)) := by
      filter_upwards with x
      by_cases hxs : x ∈ s
      · have : ∀ n, g n x = 1 := fun n ↦ hg n x hxs
        simp [this, indicator_of_mem hxs f]
      · simp_rw [indicator_of_notMem hxs f]
        apply tendsto_const_nhds.congr'
        suffices H : ∀ᶠ n in atTop, g n x = 0 by
          filter_upwards [H] with n hn using by simp [hn]
        obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε s := by
          rw [← hs.isClosed.closure_eq, closure_eq_iInter_thickening s] at hxs
          simpa using hxs
        filter_upwards [(tendsto_order.1 u_lim).2 _ εpos] with n hn
        rw [← notMem_support, g_supp]
        contrapose! hε
        exact thickening_mono hn.le s hε
    exact tendsto_integral_of_dominated_convergence bound A B C D
  -- deduce that `∫ x in s, f = 0` as each integral `∫ gₙ f` vanishes by assumption
  have : ∀ n, ∫ x, g n x • f x ∂μ = 0 := by
    refine fun n ↦ h _ (g_diff n) ?_
    apply HasCompactSupport.of_support_subset_isCompact K_compact
    simpa [g_supp] using vK n
  simpa [this] using L

@[deprecated (since := "2025-12-17")]
alias ae_eq_zero_of_integral_smooth_smul_eq_zero := ae_eq_zero_of_integral_contMDiff_smul_eq_zero

-- An instance with keys containing `Opens`
instance (U : Opens M) : BorelSpace U := inferInstanceAs% (BorelSpace (U : Set M))

/-- If a function `f` locally integrable on an open subset `U` of a finite-dimensional real
  manifold has zero integral when multiplied by any smooth function compactly supported
  in `U`, then `f` vanishes almost everywhere in `U`. -/
theorem IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero' {U : Set M} (hU : IsOpen U)
    (hSig : IsSigmaCompact U) (hf : LocallyIntegrableOn f U μ)
    (h : ∀ g : M → ℝ,
      CMDiff ∞ g → HasCompactSupport g → tsupport g ⊆ U → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 := by
  have meas_U := hU.measurableSet
  rw [← ae_restrict_iff' meas_U, ae_restrict_iff_subtype meas_U]
  let U : Opens M := ⟨U, hU⟩
  change ∀ᵐ (x : U) ∂_, _
  haveI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp hSig
  refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I ?_ fun g g_smth g_supp ↦ ?_
  · exact (locallyIntegrable_comap meas_U).mpr hf
  specialize h (Subtype.val.extend g 0) (g_smth.extend_zero g_supp)
    (g_supp.extend_zero continuous_subtype_val) ((g_supp.tsupport_extend_zero_subset
      continuous_subtype_val).trans <| Subtype.coe_image_subset _ _)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) fun x hx ↦ ?_] at h
  · rw [← integral_subtype_comap] at h
    · simp_rw [Subtype.val_injective.extend_apply] at h; exact h
    · exact meas_U
  rw [Function.extend_apply' _ _ _ (mt _ hx)]
  · apply zero_smul
  · rintro ⟨x, rfl⟩; exact x.2

@[deprecated (since := "2025-12-17")]
alias IsOpen.ae_eq_zero_of_integral_smooth_smul_eq_zero' :=
  IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero'

variable [SigmaCompactSpace M]

theorem IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero {U : Set M} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U μ)
    (h : ∀ g : M → ℝ,
      CMDiff ∞ g → HasCompactSupport g → tsupport g ⊆ U → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 :=
  haveI := I.locallyCompactSpace
  haveI := ChartedSpace.locallyCompactSpace H M
  haveI := hU.locallyCompactSpace
  haveI := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H M
  hU.ae_eq_zero_of_integral_contMDiff_smul_eq_zero' _
    (isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance) hf h

@[deprecated (since := "2025-12-17")]
alias IsOpen.ae_eq_zero_of_integral_smooth_smul_eq_zero :=
  IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero

/-- If two locally integrable functions on a finite-dimensional real manifold have the same integral
when multiplied by any smooth compactly supported function, then they coincide almost everywhere. -/
theorem ae_eq_of_integral_contMDiff_smul_eq
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : ∀ (g : M → ℝ),
      CMDiff ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) :
    ∀ᵐ x ∂μ, f x = f' x := by
  have : ∀ᵐ x ∂μ, (f - f') x = 0 := by
    apply ae_eq_zero_of_integral_contMDiff_smul_eq_zero I (hf.sub hf')
    intro g g_diff g_supp
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub, sub_eq_zero]
    · exact h g g_diff g_supp
    · exact hf.integrable_smul_left_of_hasCompactSupport g_diff.continuous g_supp
    · exact hf'.integrable_smul_left_of_hasCompactSupport g_diff.continuous g_supp
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

@[deprecated (since := "2025-12-17")]
alias ae_eq_of_integral_smooth_smul_eq := ae_eq_of_integral_contMDiff_smul_eq

end Manifold

section VectorSpace

variable [MeasurableSpace E] [BorelSpace E] {f f' : E → F} {μ : Measure E}

/-- If a locally integrable function `f` on a finite-dimensional real vector space has zero integral
when multiplied by any smooth compactly supported function, then `f` vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf : LocallyIntegrable f μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 :=
  ae_eq_zero_of_integral_contMDiff_smul_eq_zero 𝓘(ℝ, E) hf
    (fun g g_diff g_supp ↦ h g g_diff.contDiff g_supp)

/-- If two locally integrable functions on a finite-dimensional real vector space have the same
integral when multiplied by any smooth compactly supported function, then they coincide almost
everywhere. -/
theorem ae_eq_of_integral_contDiff_smul_eq
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : ∀ (g : E → ℝ),
      ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) :
    ∀ᵐ x ∂μ, f x = f' x :=
  ae_eq_of_integral_contMDiff_smul_eq 𝓘(ℝ, E) hf hf'
    (fun g g_diff g_supp ↦ h g g_diff.contDiff g_supp)

/-- If a function `f` locally integrable on an open subset `U` of a finite-dimensional real
  vector space has zero integral when multiplied by any smooth function compactly supported
  in `U`, then `f` vanishes almost everywhere in `U`. -/
theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero {U : Set E} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
        ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 :=
  hU.ae_eq_zero_of_integral_contMDiff_smul_eq_zero 𝓘(ℝ, E) hf
    (fun g g_diff g_supp ↦ h g g_diff.contDiff g_supp)

end VectorSpace
