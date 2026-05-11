/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main results

* `ContinuousAffineMap.contDiff`: a continuous affine map is smooth.
* `AffineMap.lineMap_contDiff_uncurry`, `AffineMap.lineMap_contDiff`,
  `ContDiff.lineMap` and variants: `AffineMap.lineMap` is smooth in its three
  arguments, jointly and pointwise.

-/

public section
namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
theorem contDiff {n : WithTop ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

end ContinuousAffineMap

namespace AffineMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- `AffineMap.lineMap` is smooth in all three arguments. -/
@[fun_prop]
theorem lineMap_contDiff_uncurry {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun pqc : V × V × 𝕜 ↦ AffineMap.lineMap pqc.1 pqc.2.1 pqc.2.2) := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

/-- `AffineMap.lineMap` is smooth as a function `𝕜 → V`. -/
theorem lineMap_contDiff (p₀ p₁ : V) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (AffineMap.lineMap p₀ p₁ : 𝕜 → V) := by
  fun_prop

end AffineMap

section LineMapComp

variable {𝕜 V E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f₁ f₂ : E → V} {g : E → 𝕜} {s : Set E} {x : E} {n : WithTop ℕ∞}

@[fun_prop]
theorem ContDiffWithinAt.lineMap (h₁ : ContDiffWithinAt 𝕜 n f₁ s x)
    (h₂ : ContDiffWithinAt 𝕜 n f₂ s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s x := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

theorem ContDiffAt.lineMap (h₁ : ContDiffAt 𝕜 n f₁ x)
    (h₂ : ContDiffAt 𝕜 n f₂ x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) x := by
  fun_prop

theorem ContDiffOn.lineMap (h₁ : ContDiffOn 𝕜 n f₁ s)
    (h₂ : ContDiffOn 𝕜 n f₂ s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s := by
  fun_prop

theorem ContDiff.lineMap (h₁ : ContDiff 𝕜 n f₁)
    (h₂ : ContDiff 𝕜 n f₂) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)) := by
  fun_prop

end LineMapComp
