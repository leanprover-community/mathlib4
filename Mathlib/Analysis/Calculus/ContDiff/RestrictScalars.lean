/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
### Restricting Scalars in Iterated Fréchet Derivatives

This file establishes standard theorems on restriction of scalars for iterated Fréchet derivatives,
comparing iterated derivatives with respect to a field `𝕜'` to iterated derivatives with respect to
a subfield `𝕜 ⊆ 𝕜'`. The results are analogous to those found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E → F} {n : ℕ} {s : Set E}

open ContinuousMultilinearMap Topology

private lemma fderiv_restrictScalarsLinear_comp
    {φ : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)} (h : DifferentiableAt 𝕜' φ x) :
    fderiv 𝕜 ((restrictScalarsLinear 𝕜) ∘ φ) x
      = (restrictScalars 𝕜) ∘ ((fderiv 𝕜' φ x).restrictScalars 𝕜) := by
  rw [fderiv_comp _ (by fun_prop) (h.restrictScalars 𝕜), ContinuousLinearMap.fderiv]
  ext a b
  simp [h.fderiv_restrictScalars 𝕜]

private lemma fderivWithin_restrictScalarsLinear_comp
    {φ : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)}
    (h : DifferentiableWithinAt 𝕜' φ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 ((restrictScalarsLinear 𝕜) ∘ φ) s x
      = (restrictScalars 𝕜) ∘ ((fderivWithin 𝕜' φ s x).restrictScalars 𝕜) := by
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs, ContinuousLinearMap.fderiv]
  ext a b
  simp [h.fderivWithin_restrictScalars 𝕜 hs]

theorem UniqueDiffWithinAt.mono_field (h₂s : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  rw [uniqueDiffWithinAt_iff] at *
  simp_all only [and_true]
  apply Dense.mono _ h₂s.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x))
  · apply Submodule.span_mono
    intro α hα
    simp [tangentConeAt] at hα ⊢
    obtain ⟨c, d, ⟨a, h₁a⟩, h₁, h₂⟩ := hα
    use (Algebra.algebraMap ∘ c), d
    constructor
    · use a
    · constructor
      · intro β hβ
        apply Filter.mem_map.mpr
        apply Filter.mem_atTop_sets.mpr
        let γ : Set 𝕜 := (Algebra.algebraMap)⁻¹' β
        have hγ :  γ ∈ Bornology.cobounded 𝕜 := by
          rw [← Bornology.isCobounded_def, Metric.isCobounded_iff_closedBall_compl_subset 0]
          sorry
        have h₂γ := h₁ hγ
        rw [Filter.mem_map, Filter.mem_atTop_sets] at h₂γ
        obtain ⟨n, hn⟩ := h₂γ
        use n
        intro b hb
        simp_all
        have := hn b hb
        tauto
      · sorry
  · sorry

theorem xx (h₂s : UniqueDiffOn 𝕜' s) : UniqueDiffOn 𝕜 s := by
  sorry

theorem ContDiffWithinAt.iteratedFDeriv_restrictScalars_eventuallyEq
    (h : ContDiffWithinAt 𝕜' n f s x) (hs : UniqueDiffOn 𝕜 s) (h₂s : UniqueDiffOn 𝕜' s)
    (hx : x ∈ s) :
    (restrictScalarsLinear 𝕜) ∘ (iteratedFDerivWithin 𝕜' n f s)
      =ᶠ[𝓝[s] x] (iteratedFDerivWithin 𝕜 n f s) := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp [iteratedFDeriv_zero_apply m]
  | succ n hn =>
    have t₀ := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₁ := eventually_eventually_nhdsWithin.2 (hn t₀)
    have t₃ := eventually_mem_nhdsWithin (a := x) (s := s)
    have t₄ : ∀ᶠ (y : E) in 𝓝[s] x, ContDiffWithinAt 𝕜' (↑(n + 1)) f s y := by
      nth_rw 2 [← s.insert_eq_of_mem hx]
      apply h.eventually (by simp)
    filter_upwards [t₁, t₄, t₃] with a h₁a h₃a h₄a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [restrictScalarsLinear_apply, Function.comp_apply, coe_restrictScalars,
      iteratedFDerivWithin_succ_apply_left]
    rw [← (h₁a.fderivWithin' (by tauto)).eq_of_nhdsWithin h₄a,
      fderivWithin_restrictScalarsLinear_comp]
    · simp
    · apply h₃a.differentiableWithinAt_iteratedFDerivWithin
      · rw [Nat.cast_lt]
        simp
      · simpa [s.insert_eq_of_mem h₄a]
    apply hs a h₄a

/--
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet derivative with respect
to `𝕜'`.
-/
theorem ContDiffAt.iteratedFDeriv_restrictScalars_eventuallyEq (h : ContDiffAt 𝕜' n f x) :
    (restrictScalarsLinear 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] (iteratedFDeriv 𝕜 n f) := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp [iteratedFDeriv_zero_apply m]
  | succ n hn =>
    have : ContDiffAt 𝕜' n f x := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₀ := hn this
    have t₁ := this.eventually
    simp only [ne_eq, ENat.natCast_ne_coe_top, not_false_eq_true, forall_const] at t₁
    filter_upwards [t₀.eventually_nhds, t₁.eventually_nhds,
      h.eventually (by simp)] with a h₁a h₂a h₃a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [restrictScalarsLinear_apply, Function.comp_apply, coe_restrictScalars,
      iteratedFDeriv_succ_apply_left]
    rw [← h₁a.fderiv_eq, fderiv_restrictScalarsLinear_comp]
    · simp
    · apply h₃a.differentiableAt_iteratedFDeriv
      rw [Nat.cast_lt]
      simp

/--
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet derivative with respect
to `𝕜'`.
-/
theorem ContDiffAt.iteratedFDeriv_restrictScalars (h : ContDiffAt 𝕜' n f x) :
    ((restrictScalarsLinear 𝕜) ∘ iteratedFDeriv 𝕜' n f) x = iteratedFDeriv 𝕜 n f x :=
  h.iteratedFDeriv_restrictScalars_eventuallyEq.eq_of_nhds
