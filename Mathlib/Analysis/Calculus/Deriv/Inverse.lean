/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Inverse function theorem - the easy half

In this file we prove that `g' (f x) = (f' x)⁻¹` provided that `f` is strictly differentiable at
`x`, `f' x ≠ 0`, and `g` is a local left inverse of `f` that is continuous at `f x`. This is the
easy half of the inverse function theorem: the harder half states that `g` exists.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, inverse function
-/


universe u v

open scoped Topology
open Filter Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}
variable {f' : F}
variable {s : Set 𝕜} {x : 𝕜} {c : F}

theorem HasStrictDerivAt.hasStrictFDerivAt_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
    (hf : HasStrictDerivAt f f' x) (hf' : f' ≠ 0) :
    HasStrictFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf

theorem HasDerivAt.hasFDerivAt_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : HasDerivAt f f' x)
    (hf' : f' ≠ 0) :
    HasFDerivAt f (ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
  hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasStrictDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasStrictDerivAt g f'⁻¹ a :=
  (hf.hasStrictFDerivAt_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem OpenPartialHomeomorph.hasStrictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : HasStrictDerivAt f f' (f.symm a)) :
    HasStrictDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasDerivAt.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜} (hg : ContinuousAt g a)
    (hf : HasDerivAt f f' (g a)) (hf' : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
    HasDerivAt g f'⁻¹ a :=
  (hf.hasFDerivAt_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is an open partial homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem OpenPartialHomeomorph.hasDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜}
    (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : HasDerivAt f f' (f.symm a)) :
    HasDerivAt f.symm f'⁻¹ a :=
  htff'.of_local_left_inverse (f.symm.continuousAt ha) hf' (f.eventually_right_inverse ha)

theorem HasDerivWithinAt.eventually_ne (h : HasDerivWithinAt f f' s x) (hf' : f' ≠ 0) :
    ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ c :=
  h.hasFDerivWithinAt.eventually_ne
    ⟨‖f'‖⁻¹, fun z => by simp [norm_smul]; field_simp; rfl⟩

theorem HasDerivAt.eventually_ne (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ c := by
  simpa only [compl_eq_univ_diff] using (hasDerivWithinAt_univ.2 h).eventually_ne hf'

theorem HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] f x) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h.continuousAt.continuousWithinAt
    (h.eventually_ne hf')

@[deprecated (since := "2025-03-02")]
alias HasDerivAt.tendsto_punctured_nhds := HasDerivAt.tendsto_nhdsNE

/-- If a function is equal to a constant at a set of points that accumulates to `x` in `s`,
then its derivative within `s` at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
theorem derivWithin_zero_of_frequently_const {c} (h : ∃ᶠ y in 𝓝[s \ {x}] x, f y = c) :
    derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose h
    rw [not_frequently]
    exact hf.hasDerivWithinAt.eventually_ne h
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

/-- If a function is equal to a constant at a set of points that accumulates to `x`,
then its derivative at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
theorem deriv_zero_of_frequently_const {c} (h : ∃ᶠ y in 𝓝[≠] x, f y = c) : deriv f x = 0 := by
  rw [← derivWithin_univ, derivWithin_zero_of_frequently_const]
  rwa [← compl_eq_univ_diff]

theorem not_differentiableWithinAt_of_local_left_inverse_hasDerivWithinAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    {s t : Set 𝕜} (ha : a ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s a) (hf : HasDerivWithinAt f 0 t (g a))
    (hst : MapsTo g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) : ¬DifferentiableWithinAt 𝕜 g s a := by
  intro hg
  have := (hf.comp a hg.hasDerivWithinAt hst).congr_of_eventuallyEq_of_mem hfg.symm ha
  simpa using hsu.eq_deriv _ this (hasDerivWithinAt_id _ _)

theorem not_differentiableAt_of_local_left_inverse_hasDerivAt_zero {f g : 𝕜 → 𝕜} {a : 𝕜}
    (hf : HasDerivAt f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) : ¬DifferentiableAt 𝕜 g a := by
  intro hg
  have := (hf.comp a hg.hasDerivAt).congr_of_eventuallyEq hfg.symm
  simpa using this.unique (hasDerivAt_id a)
