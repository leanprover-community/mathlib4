/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Lipschitz smoothness

A function `f : E → F` between normed vector spaces over a nontrivially normed field `𝕜` is
**`K`-smooth** if it is Fréchet differentiable and its first-order Taylor remainder is bounded
quadratically:

`‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ (K / 2) * dist x y ^ 2`.

We define global and setwise versions.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜)

/-- A function `f : E → F` is **`K`-smooth** if it is Fréchet differentiable and its
first-order Taylor remainder is bounded by `K / 2 * dist x y ^ 2` for all `x` and `y`. -/
structure LipschitzSmoothWith (K : NNReal) (f : E → F) : Prop where
  differentiable : Differentiable 𝕜 f
  fderiv_norm_le : ∀ x y,
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2

/-- A function `f : E → F` is **`K`-smooth on `s`** if it is Fréchet differentiable within
`s` and its first-order Taylor remainder is bounded by `K / 2 * dist x y ^ 2` for all
`x`, `y ∈ s`. -/
structure LipschitzSmoothOnWith (K : NNReal) (f : E → F) (s : Set E) : Prop where
  differentiableOn : DifferentiableOn 𝕜 f s
  fderivWithin_norm_le : ∀ x ∈ s, ∀ y ∈ s,
    ‖f y - f x - fderivWithin 𝕜 f s x (y - x)‖ ≤ K / 2 * dist x y ^ 2

variable {𝕜}

@[simp]
theorem lipschitzSmoothOnWith_empty (K : NNReal) (f : E → F) :
    LipschitzSmoothOnWith 𝕜 K f ∅ :=
  ⟨differentiableOn_empty, fun _ hx ↦ hx.elim⟩

@[simp]
theorem lipschitzSmoothOnWith_univ {K : NNReal} {f : E → F} :
    LipschitzSmoothOnWith 𝕜 K f Set.univ ↔ LipschitzSmoothWith 𝕜 K f := by
  constructor
  · rintro ⟨hf, hbound⟩
    exact ⟨differentiableOn_univ.mp hf, by
      simpa only [Set.mem_univ, forall_const, fderivWithin_univ] using hbound⟩
  · rintro ⟨hf, hbound⟩
    exact ⟨differentiableOn_univ.mpr hf, by
      simpa only [Set.mem_univ, forall_const, fderivWithin_univ] using hbound⟩
