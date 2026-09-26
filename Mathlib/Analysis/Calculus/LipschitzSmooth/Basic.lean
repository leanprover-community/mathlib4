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

/-- Construct global Lipschitz smoothness using a specified Fréchet derivative. -/
theorem LipschitzSmoothWith.of_hasFDerivAt {K : NNReal} {f : E → F}
    {f' : E → E →L[𝕜] F} (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hbound : ∀ x y, ‖f y - f x - f' x (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    LipschitzSmoothWith 𝕜 K f :=
  ⟨fun x ↦ (hf x).differentiableAt, fun x y ↦ by
    rw [(hf x).fderiv]
    exact hbound x y⟩

/-- Construct setwise Lipschitz smoothness using a specified Fréchet derivative within the
set. -/
theorem LipschitzSmoothOnWith.of_hasFDerivWithinAt {K : NNReal} {f : E → F} {s : Set E}
    {f' : E → E →L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, ‖f y - f x - f' x (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    LipschitzSmoothOnWith 𝕜 K f s :=
  ⟨fun x hx ↦ (hf x hx).differentiableWithinAt, fun x hx y hy ↦ by
    rw [(hf x hx).fderivWithin (hs.uniqueDiffWithinAt hx)]
    exact hbound x hx y hy⟩

@[simp]
theorem lipschitzSmoothOnWith_empty (K : NNReal) (f : E → F) :
    LipschitzSmoothOnWith 𝕜 K f ∅ :=
  ⟨differentiableOn_empty, fun _ hx ↦ hx.elim⟩

@[simp]
theorem lipschitzSmoothOnWith_univ {K : NNReal} {f : E → F} :
    LipschitzSmoothOnWith 𝕜 K f Set.univ ↔ LipschitzSmoothWith 𝕜 K f := by
  constructor <;>
    rintro ⟨hf, hbound⟩ <;>
    exact ⟨by simpa only [differentiableOn_univ] using hf, by
      simpa only [Set.mem_univ, forall_const, fderivWithin_univ] using hbound⟩

/-- Lipschitz smoothness within a uniquely differentiable set is monotone in the set. -/
theorem LipschitzSmoothOnWith.mono {K : NNReal} {f : E → F} {s t : Set E}
    (h : LipschitzSmoothOnWith 𝕜 K f t) (hs : UniqueDiffOn 𝕜 s) (hst : s ⊆ t) :
    LipschitzSmoothOnWith 𝕜 K f s := by
  refine ⟨h.differentiableOn.mono hst, fun x hx y hy ↦ ?_⟩
  rw [fderivWithin_subset hst (hs.uniqueDiffWithinAt hx) (h.differentiableOn x (hst hx))]
  exact h.fderivWithin_norm_le x (hst hx) y (hst hy)

/-- A globally Lipschitz-smooth function is Lipschitz smooth on every uniquely differentiable
set. -/
protected theorem LipschitzSmoothWith.lipschitzSmoothOnWith {K : NNReal} {f : E → F}
    (h : LipschitzSmoothWith 𝕜 K f) {s : Set E} (hs : UniqueDiffOn 𝕜 s) :
    LipschitzSmoothOnWith 𝕜 K f s :=
  (lipschitzSmoothOnWith_univ.mpr h).mono hs (Set.subset_univ s)
