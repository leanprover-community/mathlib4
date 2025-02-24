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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

namespace SmoothFlow

def funSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (tmin tmax : ℝ) (u : Set E) := { α : C(Icc tmin tmax, E) | range α ⊆ u }

lemma isOpen_funSpace (hu : IsOpen u) : IsOpen (funSpace tmin tmax u) := by
  simpa [funSpace, range_subset_iff, ← mapsTo_univ_iff] using
    ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu

noncomputable def implicitFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
    (x₀ : E) (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) : C(Icc tmin tmax, E) where
  toFun := fun t ↦ x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax sorry τ))
  continuous_toFun := sorry

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


end SmoothFlow
