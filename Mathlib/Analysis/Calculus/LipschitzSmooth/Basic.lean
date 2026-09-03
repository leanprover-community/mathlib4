/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Lipschitz smoothness

A function `f : E → F` between normed vector spaces over a nontrivially normed field `𝕜` is
**`K`-smooth** if its first-order Taylor remainder is bounded quadratically:

`‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ (K / 2) * dist x y ^ 2`.

We define global and setwise versions. Each notion includes enough control to imply the
corresponding Fréchet differentiability property.
-/

public section

open scoped Topology

open Asymptotics Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜)

/-- `LipschitzSmoothWith 𝕜 K f` means that the first-order Taylor remainder from `fderiv` is
bounded by `K / 2 * dist x y ^ 2` for all `x` and `y`. -/
def LipschitzSmoothWith (K : NNReal) (f : E → F) : Prop :=
  ∀ x y, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2

/-- `LipschitzSmoothOnWith 𝕜 K f s` means that `f` is Fréchet differentiable within `s` and
its first-order Taylor remainder is bounded by `K / 2 * dist x y ^ 2` for all `x` and `y` in `s`.

The derivative is given as a witness rather than by `fderivWithin` so that this property is
preserved when restricting to a subset. -/
def LipschitzSmoothOnWith (K : NNReal) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x ∧
    ∀ y ∈ s, ‖f y - f x - f' (y - x)‖ ≤ K / 2 * dist x y ^ 2

theorem lipschitzSmoothWith_iff_fderiv {K : NNReal} {f : E → F} :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  Iff.rfl

theorem lipschitzSmoothOnWith_iff {K : NNReal} {f : E → F} {s : Set E} :
    LipschitzSmoothOnWith 𝕜 K f s ↔
      ∀ x ∈ s, ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x ∧
        ∀ y ∈ s, ‖f y - f x - f' (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  Iff.rfl

variable {𝕜}

private theorem hasFDerivAt_of_eventually_norm_le {K : NNReal} {f : E → F} {x : E}
    {f' : E →L[𝕜] F}
    (h : ∀ᶠ y in 𝓝 x,
      ‖f y - f x - f' (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    HasFDerivAt f f' x := by
  apply HasFDerivAt.of_isLittleO
  refine (IsBigO.of_bound (K / 2) ?_).trans_isLittleO
    (isLittleO_pow_sub_sub x one_lt_two)
  filter_upwards [h] with y hy
  simpa [dist_eq_norm, norm_sub_rev] using hy

namespace LipschitzSmoothOnWith

variable {K : NNReal} {f : E → F} {s t : Set E} {x : E}

/-- Extract a derivative witness and the corresponding quadratic bound at a point of the set. -/
theorem exists_hasFDerivWithinAt_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s) (hx : x ∈ s) :
    ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x ∧
      ∀ y ∈ s, ‖f y - f x - f' (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  h x hx

/-- A function Lipschitz smooth on a set is Fréchet differentiable within that set. -/
theorem differentiableOn (h : LipschitzSmoothOnWith 𝕜 K f s) : DifferentiableOn 𝕜 f s := by
  intro x hx
  obtain ⟨f', hf', -⟩ := h.exists_hasFDerivWithinAt_norm_le hx
  exact hf'.differentiableWithinAt

/-- Being Lipschitz smooth on a set is preserved when restricting to a subset. -/
theorem mono (h : LipschitzSmoothOnWith 𝕜 K f t) (hst : s ⊆ t) :
    LipschitzSmoothOnWith 𝕜 K f s := by
  rw [lipschitzSmoothOnWith_iff]
  intro x hx
  obtain ⟨f', hf', hbound⟩ := h.exists_hasFDerivWithinAt_norm_le (hst hx)
  exact ⟨f', hf'.mono hst, fun y hy ↦ hbound y (hst hy)⟩

/-- The defining bound expressed using `fderivWithin` on a set with unique derivatives. -/
theorem fderivWithin_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    ‖f y - f x - fderivWithin 𝕜 f s x (y - x)‖ ≤ K / 2 * dist x y ^ 2 := by
  obtain ⟨f', hf', hbound⟩ := h.exists_hasFDerivWithinAt_norm_le hx
  rw [hf'.fderivWithin (hs x hx)]
  exact hbound y hy

end LipschitzSmoothOnWith

@[simp]
theorem lipschitzSmoothOnWith_empty (K : NNReal) (f : E → F) :
    LipschitzSmoothOnWith 𝕜 K f ∅ := by
  rw [lipschitzSmoothOnWith_iff]
  simp

theorem lipschitzSmoothOnWith_iff_fderivWithin {K : NNReal} {f : E → F} {s : Set E}
    (hs : UniqueDiffOn 𝕜 s) :
    LipschitzSmoothOnWith 𝕜 K f s ↔ DifferentiableOn 𝕜 f s ∧
      ∀ x ∈ s, ∀ y ∈ s,
        ‖f y - f x - fderivWithin 𝕜 f s x (y - x)‖ ≤ K / 2 * dist x y ^ 2 := by
  constructor
  · intro h
    exact ⟨h.differentiableOn, fun x hx y hy ↦ h.fderivWithin_norm_le hs hx hy⟩
  · rintro ⟨hdf, hbound⟩
    rw [lipschitzSmoothOnWith_iff]
    exact fun x hx ↦
      ⟨fderivWithin 𝕜 f s x, (hdf x hx).hasFDerivWithinAt, hbound x hx⟩

theorem IsOpen.lipschitzSmoothOnWith_iff_fderiv {K : NNReal} {f : E → F} {s : Set E}
    (hs : IsOpen s) :
    LipschitzSmoothOnWith 𝕜 K f s ↔
      ∀ x ∈ s, ∀ y ∈ s,
        ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 := by
  rw [lipschitzSmoothOnWith_iff_fderivWithin hs.uniqueDiffOn]
  constructor
  · rintro ⟨-, hbound⟩ x hx y hy
    simpa only [fderivWithin_of_isOpen hs hx] using hbound x hx y hy
  · intro hbound
    refine ⟨fun x hx ↦ ?_, ?_⟩
    · apply (hasFDerivAt_of_eventually_norm_le
        (K := K) (f' := fderiv 𝕜 f x) ?_).differentiableAt.differentiableWithinAt
      filter_upwards [hs.mem_nhds hx] with y hy
      exact hbound x hx y hy
    · intro x hx y hy
      simpa only [fderivWithin_of_isOpen hs hx] using hbound x hx y hy

namespace LipschitzSmoothWith

variable {K : NNReal} {f : E → F}

/-- The defining quadratic bound on the first-order Taylor remainder. -/
theorem fderiv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  h x y

/-- A globally Lipschitz-smooth function is Fréchet differentiable. -/
theorem differentiable (h : LipschitzSmoothWith 𝕜 K f) :
    Differentiable 𝕜 f :=
  fun x ↦ (hasFDerivAt_of_eventually_norm_le (f' := fderiv 𝕜 f x) <|
    Eventually.of_forall fun y ↦ h.fderiv_norm_le x y).differentiableAt

/-- A globally Lipschitz-smooth function is Lipschitz smooth on every set. -/
theorem lipschitzSmoothOnWith (h : LipschitzSmoothWith 𝕜 K f) (s : Set E) :
    LipschitzSmoothOnWith 𝕜 K f s := by
  rw [lipschitzSmoothOnWith_iff]
  exact fun x _ ↦ ⟨fderiv 𝕜 f x, (h.differentiable x).hasFDerivAt.hasFDerivWithinAt,
    fun y _ ↦ h.fderiv_norm_le x y⟩

end LipschitzSmoothWith

@[simp]
theorem lipschitzSmoothOnWith_univ {K : NNReal} {f : E → F} :
    LipschitzSmoothOnWith 𝕜 K f Set.univ ↔ LipschitzSmoothWith 𝕜 K f := by
  constructor
  · intro h x y
    simpa only [fderivWithin_univ] using
      h.fderivWithin_norm_le uniqueDiffOn_univ (Set.mem_univ x) (Set.mem_univ y)
  · exact fun h ↦ h.lipschitzSmoothOnWith Set.univ
