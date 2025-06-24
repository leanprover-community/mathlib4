/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
### Restricting Scalars in Iterated Derivatives

This file establishes standard theorems on restriction of scalars for iterated Fréchet derivatives,
comparing iterated derivatives with respect to a field `𝕜'` to iterated derivatives with respect to
a subfield `𝕜 ⊆ 𝕜'`. The result are analogous to thouse found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E → F} {n : ℕ}

open ContinuousMultilinearMap Topology

private lemma fderiv_restrictScalarsLinear_comp
    {φ : E → (ContinuousMultilinearMap 𝕜' (fun _ : Fin n ↦ E) F)} (h : DifferentiableAt 𝕜' φ x) :
    fderiv 𝕜 ((restrictScalarsLinear 𝕜) ∘ φ) x
      = (restrictScalars 𝕜) ∘ ((fderiv 𝕜' φ x).restrictScalars 𝕜) := by
  rw [fderiv_comp _ (by fun_prop) (h.restrictScalars 𝕜), ContinuousLinearMap.fderiv]
  ext a b
  simp [h.fderiv_restrictScalars 𝕜]

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
@[simp]
theorem ContDiffAt.iteratedFDeriv_restrictScalars (h : ContDiffAt 𝕜' n f x) :
    ((restrictScalarsLinear 𝕜) ∘ iteratedFDeriv 𝕜' n f) x = iteratedFDeriv 𝕜 n f x :=
  h.iteratedFDeriv_restrictScalars_eventuallyEq.eq_of_nhds
