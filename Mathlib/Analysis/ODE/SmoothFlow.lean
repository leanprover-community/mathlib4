/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Smooth dependence on initial condition

We prove that the solution of a $C^n$ vector field has $C^n$ dependence on the initial condition.

## Main definitions and results



## Implementation notes



## Tags

differential equation, dynamical system, initial value problem

-/

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace SmoothFlow

/-
We want to define a function `f : E × F → F`, where `F = C(Icc tmin tmax, E)`. The form of `f x₀ α`
is `fun t ↦ x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax .. τ))`. Since `f` is only assumed to
be ContDiffOn an open `u : Set E`, this is only well defined when the range of `α` is contained in
`u`. Thus, we define `f` as a piecewise function conditioned on whether `x₀` and `α` stay within
`u`.
-/

-- noncomputable def implicitFunAux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E}
--     {u : Set E} (hf : ContDiffOn ℝ 1 f u) {x₀ : E} (hx : x₀ ∈ u) {t₀ tmin tmax : ℝ}
--     (α : C(Icc tmin tmax, E))






namespace test

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

/-- We wish to apply the implicit function theorem on an implicit equation `f(x, α) = 0`, where
`x : E` and `α : C(Icc tmin tmax, E)`. This `funSpace` is the open subset of `C(Icc tmin tmax, E)`
containing curves bounded by `u`. -/
def funSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (tmin tmax : ℝ) (u : Set E) := { α : C(Icc tmin tmax, E) | range α ⊆ u }

lemma isOpen_funSpace (hu : IsOpen u) : IsOpen (funSpace tmin tmax u) := by
  simpa [funSpace, range_subset_iff, ← mapsTo_univ_iff] using
    ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu

/-- The implicit function `f : E × C(Icc tmin tmax, E) → C(Icc tmin tmax, E)`, whose level set of
`(x, α)` contains the solutions to the initial value problem. -/
noncomputable def implicitFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) :
    C(Icc tmin tmax, E) where
  toFun := fun t ↦
    x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax (nonempty_Icc.mp ⟨t₀.val, t₀.property⟩) τ))
  continuous_toFun := by
    have h : tmin ≤ tmax := nonempty_Icc.mp ⟨t₀.val, t₀.property⟩
    refine Continuous.add ?_ ?_
    · exact Continuous.sub continuous_const α.continuous
    · have : (fun t : Icc tmin tmax ↦ ∫ τ in t₀..t, f (α (projIcc tmin tmax h τ))) =
          (fun t : ℝ ↦ ∫ τ in t₀..t, f (α (projIcc tmin tmax h τ))) ∘ (fun t : Icc tmin tmax ↦ t) :=
        rfl
      rw [this]
      apply Continuous.comp _ continuous_subtype_val
      apply intervalIntegral.continuous_primitive
      intro t₁ t₂
      apply Continuous.intervalIntegrable
      apply Continuous.comp hf.continuous
      -- need `α` to stay within `u` and `f` to be continuous on `u`
      sorry

-- generalise!
def fderivImplicitFun₁ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    E →L[ℝ] C(Icc tmin tmax, E) where
  toFun dx := ContinuousMap.const (Icc tmin tmax) dx
  map_add' x y := by congr
  map_smul' r x := by congr
  cont := sorry

-- WRITE ALL THIS DOWN SO WE KNOW WHAT'S GOING ON!

noncomputable def fderivImplicitFun₂Fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (f' : E → E →L[ℝ] E) (α : C(Icc tmin tmax, E))
    (dα : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
  toFun t := -dα t + ∫ τ in t₀..t, f' (α t) (dα t)
  continuous_toFun := sorry

noncomputable def fderivImplicitFun₂ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (f' : E → E →L[ℝ] E) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) where
  toFun dα := fderivImplicitFun₂Fun t₀ f' α dα  -- need to define a continuous curve first
  map_add' α β := sorry
  map_smul' r α := sorry
  cont := sorry

lemma hasFDerivAt_implicitFun₁ (x₀ : E) (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) :
    HasFDerivAt (fun x ↦ implicitFun f x α t₀) (fderivImplicitFun₁ x₀) x₀ := sorry

lemma hasFDerivAt_implicitFun₂ {f' : E → E →L[ℝ] E} (hf : ∀ x ∈ u, HasFDerivAt f (f' x) x) (x₀ : E)
    (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) :
    HasFDerivAt (fun α ↦ implicitFun f x₀ α t₀) (fderivImplicitFun₂ t₀ f' α) α := sorry

end test

end SmoothFlow
