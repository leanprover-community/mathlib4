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

/--
If a predicate is true in a neighbourhood of `x` within `s`, then for `y ∈ s` sufficiently close to
`x` this predicate is true in a neighbourhood of `y` within `s`.
-/
theorem Filter.Eventually.eventually_nhdsWithin
    {X : Type*} [inst : TopologicalSpace X] {x : X} {s : Set X} {p : X → Prop}
    (h : ∀ᶠ y in 𝓝[s] x, p y) :
    ∀ᶠ y in 𝓝[s] x, ∀ᶠ x in 𝓝[s] y, p x := by
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h.eventually_nhds] with a ha h₂a
  simpa [eventually_nhdsWithin_iff]

theorem ContDiffWithinAt.iteratedFDeriv_restrictScalars_eventuallyEq
    (h : ContDiffWithinAt 𝕜' n f s x) :
    (restrictScalarsLinear 𝕜) ∘ (iteratedFDerivWithin 𝕜' n f s)
      =ᶠ[𝓝[insert x s] x] (iteratedFDerivWithin 𝕜 n f s) := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp [iteratedFDeriv_zero_apply m]
  | succ n hn =>
    have : ContDiffWithinAt 𝕜' n f s x := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₀ := hn this
    have t₁ := this.eventually
    simp only [ne_eq, ENat.natCast_ne_coe_top, not_false_eq_true, forall_const] at t₁
    have := t₀.eventually_nhdsWithin
    filter_upwards [t₀.eventually_nhdsWithin, t₁.eventually_nhdsWithin,
      h.eventually (by simp)] with a h₁a h₂a h₃a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [restrictScalarsLinear_apply, Function.comp_apply, coe_restrictScalars,
      iteratedFDerivWithin_succ_apply_left]
    have := h₁a.fderivWithin_eq_of_insert (s := s) (𝕜 := 𝕜) (F := ContinuousMultilinearMap 𝕜 (fun i ↦ E) F)
    rw [← h₁a.fderivWithin_eq_of_insert, fderiv_restrictScalarsLinear_comp]
    · simp
    · apply h₃a.differentiableAt_iteratedFDeriv
      rw [Nat.cast_lt]
      simp

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
