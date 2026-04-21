/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
### Restricting Scalars in Iterated Fréchet Derivatives

This file establishes standard theorems on restriction of scalars for iterated Fréchet derivatives,
comparing iterated derivatives with respect to a field `𝕜'` to iterated derivatives with respect to
a subfield `𝕜 ⊆ 𝕜'`. The results are analogous to those found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/
set_option backward.defeqAttrib.useBackward true

public section

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E → F} {n : ℕ} {s : Set E}

open ContinuousMultilinearMap Topology

/-- Derivation rule for compositions of scalar restriction with continuous multilinear maps. -/
lemma fderivWithin_restrictScalars_comp
    {φ : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)}
    (h : DifferentiableWithinAt 𝕜' φ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 ((restrictScalars 𝕜) ∘ φ) s x
      = (restrictScalars 𝕜) ∘ ((fderivWithin 𝕜' φ s x).restrictScalars 𝕜) := by
  simp only [← restrictScalarsLinear_apply]
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs, ContinuousLinearMap.fderiv]
  ext a b
  simp [h.restrictScalars_fderivWithin 𝕜 hs]

/--
If `f` is `n` times continuously differentiable at `x` within `s`, then the `n`th iterated Fréchet
derivative within `s` with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet
derivative within `s` with respect to `𝕜'`.
-/
theorem ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq
    (h : ContDiffWithinAt 𝕜' n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    (restrictScalars 𝕜) ∘ (iteratedFDerivWithin 𝕜' n f s)
      =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp
  | succ n hn =>
    have t₀ := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₁ : ∀ᶠ (y : E) in 𝓝[s] x, ContDiffWithinAt 𝕜' (↑(n + 1)) f s y := by
      nth_rw 2 [← s.insert_eq_of_mem hx]
      apply h.eventually (by simp)
    filter_upwards [eventually_eventually_nhdsWithin.2 (hn t₀), t₁,
      eventually_mem_nhdsWithin (a := x) (s := s)] with a h₁a h₃a h₄a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [Function.comp_apply, coe_restrictScalars, iteratedFDerivWithin_succ_apply_left]
    rw [← (h₁a.fderivWithin' (by tauto)).eq_of_nhdsWithin h₄a,
      fderivWithin_restrictScalars_comp]
    · simp
    · apply h₃a.differentiableWithinAt_iteratedFDerivWithin
      · rw [Nat.cast_lt]
        simp
      · have : UniqueDiffOn 𝕜' s := hs.mono_field
        simpa [s.insert_eq_of_mem h₄a]
    apply hs a h₄a

/--
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet derivative with respect
to `𝕜'`.
-/
theorem ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq (h : ContDiffAt 𝕜' n f x) :
    (restrictScalars 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f := by
  have h' : ContDiffWithinAt 𝕜' n f Set.univ x := h
  convert (h'.restrictScalars_iteratedFDerivWithin_eventuallyEq _ trivial)
  <;> simp [iteratedFDerivWithin_univ.symm, uniqueDiffOn_univ]

/--
If `f` is `n` times continuously differentiable at `x`, then the `n`th iterated Fréchet derivative
with respect to `𝕜` equals scalar restriction of the `n`th iterated Fréchet derivative with respect
to `𝕜'`.
-/
theorem ContDiffAt.restrictScalars_iteratedFDeriv (h : ContDiffAt 𝕜' n f x) :
    ((restrictScalars 𝕜) ∘ iteratedFDeriv 𝕜' n f) x = iteratedFDeriv 𝕜 n f x :=
  h.restrictScalars_iteratedFDeriv_eventuallyEq.eq_of_nhds
