/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LipschitzSmooth.Gradient
public import Mathlib.Analysis.Convex.Gradient

/-!
# Baillon-Haddad theorem

For a differentiable convex function on a Hilbert space, `K`-smoothness implies
`K`-cocoercivity of the gradient (the Baillon-Haddad theorem). Combined with the
descent lemma, this yields the pairwise iff equivalences between
`LipschitzSmoothWith`, `LipschitzWith (fderiv ℝ f)`, `LipschitzWith (∇ f)`, and
`CocoerciveWith`.
-/

public section

namespace ConvexOn

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

/-- Core Baillon-Haddad estimate (`K > 0` case): for convex differentiable `K`-smooth `f`,
`‖∇f y - ∇f x‖² ≤ 2K · (f y - f x - ⟪∇f x, y - x⟫)`. Direct proof via the descent inequality
applied at the auxiliary point `u := y - (1/K) · (∇f y - ∇f x)` combined with the
first-order convexity inequality at `(x, u)`. -/
private theorem norm_gradient_sub_sq_le_aux (hc : ConvexOn ℝ Set.univ f)
    (hf : Differentiable ℝ f) (hs : LipschitzSmoothWith K f) (hKp : 0 < (K : ℝ)) (x y : F) :
    ‖∇ f y - ∇ f x‖ ^ 2 ≤ 2 * K * (f y - f x - ⟪∇ f x, y - x⟫) := by
  set g := ∇ f y - ∇ f x with hg
  -- Combining convex FOC at `(x, u)` with K-smooth descent at `(y, u)` for the step
  -- `u := y - (1/K) • g`, then substituting the shape of `u - x`, `u - y`, `‖u - y‖²`.
  have h_chain : f x + ⟪∇ f x, y - x⟫_ℝ - 1 / K * ⟪∇ f x, g⟫_ℝ ≤
      f y - 1 / K * ⟪∇ f y, g⟫_ℝ + ‖g‖ ^ 2 / (2 * K) := by
    set u := y - (1 / (K : ℝ)) • g with hu
    calc f x + ⟪∇ f x, y - x⟫_ℝ - 1 / K * ⟪∇ f x, g⟫_ℝ
        = f x + ⟪∇ f x, u - x⟫_ℝ := by
          simp only [hu, inner_sub_right, inner_smul_right]; ring
      _ ≤ f u := hc.add_inner_gradient_le (Set.mem_univ x) (Set.mem_univ u) (hf x)
      _ ≤ f y + ⟪∇ f y, u - y⟫_ℝ + K / 2 * ‖u - y‖ ^ 2 :=
          hs.inner_gradient_descent_le y u (hf y)
      _ = f y - 1 / K * ⟪∇ f y, g⟫_ℝ + ‖g‖ ^ 2 / (2 * K) := by
          simp only [hu, sub_sub_cancel_left, inner_neg_right, inner_smul_right, norm_neg,
            norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          field_simp; ring
  -- Inner-product self identity: `(1/K) · (⟪∇f y, g⟫ - ⟪∇f x, g⟫) = ‖g‖²/K = 2 · ‖g‖²/(2K)`.
  have h_inner : 1 / K * ⟪∇ f y, g⟫_ℝ - 1 / K * ⟪∇ f x, g⟫_ℝ
      = 2 * (‖g‖ ^ 2 / (2 * K)) := by
    rw [← mul_sub, ← inner_sub_left, ← hg, real_inner_self_eq_norm_sq]; field_simp
  calc ‖∇ f y - ∇ f x‖ ^ 2
      = 2 * K * (‖g‖ ^ 2 / (2 * K)) := by rw [hg]; field_simp
    _ ≤ 2 * K * (f y - f x - ⟪∇ f x, y - x⟫_ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith [h_chain, h_inner]) (by positivity)

/-- **Baillon-Haddad theorem.** A differentiable convex `K`-smooth function on a Hilbert
space is `K`-cocoercive.

The standard proof, here inlined without introducing `φₓ` explicitly: define
`φₓ(z) := f(z) - ⟨∇f(x), z⟩`, which is convex and `K`-smooth with minimum at `x`
(since `∇φₓ(x) = 0`). Apply the descent inequality of `φₓ` at `y`
stepping by `-∇φₓ(y) / K`; using `φₓ(x) = min φₓ` yields
`‖∇f(y) - ∇f(x)‖² ≤ 2K (f(y) - f(x) - ⟨∇f(x), y - x⟩)`. Sum with the symmetric bound from
`φᵧ`, and the linear terms in `f` cancel to give the cocoercive inequality. -/
theorem cocoerciveWith_of_lipschitzSmoothWith
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (hs : LipschitzSmoothWith K f) : CocoerciveWith K f := by
  intro x y
  by_cases hK : (K : ℝ) = 0
  · -- K = 0: descent + FOC pinch `f b = f a + ⟪∇f a, b - a⟫` to equality everywhere,
    -- forcing `f` affine and `∇f` constant. Both sides of the cocoercive bound are then 0.
    have h_eq : ∀ a b : F, f b = f a + ⟪∇ f a, b - a⟫_ℝ := fun a b =>
      le_antisymm (by simpa [hK] using hs.inner_gradient_descent_le a b (hf a))
        (hc.add_inner_gradient_le (Set.mem_univ a) (Set.mem_univ b) (hf a))
    have h_grad_eq : ∀ v : F, ⟪∇ f y, v⟫_ℝ = ⟪∇ f x, v⟫_ℝ := fun v => by
      have e1 := h_eq x (y + v)
      have e2 := h_eq y (y + v)
      have e3 := h_eq x y
      rw [show (y + v) - y = v from by abel] at e2
      rw [show (y + v) - x = (y - x) + v from by abel, inner_add_right] at e1
      linarith
    simp [ext_inner_right ℝ h_grad_eq]
  · have hKp : 0 < (K : ℝ) := lt_of_le_of_ne K.coe_nonneg (Ne.symm hK)
    -- Apply the core bound at `(x, y)` and `(y, x)`; sum cancels the linear-in-f terms.
    have h_sym : ‖∇ f x - ∇ f y‖ ^ 2 = ‖∇ f y - ∇ f x‖ ^ 2 := by rw [norm_sub_rev]
    have h_inner : ⟪∇ f x, y - x⟫_ℝ + ⟪∇ f y, x - y⟫_ℝ
        = -⟪∇ f y - ∇ f x, y - x⟫_ℝ := by
      rw [show (x - y : F) = -(y - x) from (neg_sub y x).symm, inner_neg_right,
        inner_sub_left]
      ring
    nlinarith [norm_gradient_sub_sq_le_aux hc hf hs hKp x y,
      norm_gradient_sub_sq_le_aux hc hf hs hKp y x, h_sym, h_inner, K.coe_nonneg]

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to `K`-cocoercivity. The forward direction is the Baillon-Haddad theorem; the backward
direction goes via `K`-Lipschitz gradient and the descent lemma, no convexity needed. -/
theorem lipschitzSmoothWith_iff_cocoerciveWith
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ CocoerciveWith K f :=
  ⟨hc.cocoerciveWith_of_lipschitzSmoothWith hf,
    fun h => hf.lipschitzSmoothWith_of_lipschitzWith_gradient h.lipschitzWith_gradient⟩

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to `K`-Lipschitz gradient. Forward: K-smooth → cocoercive (Baillon-Haddad) → Lipschitz
gradient. Backward: the descent lemma in Hilbert form. -/
theorem lipschitzSmoothWith_iff_lipschitzWith_gradient
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ LipschitzWith K (∇ f) :=
  ⟨fun hs => (hc.cocoerciveWith_of_lipschitzSmoothWith hf hs).lipschitzWith_gradient,
    hf.lipschitzSmoothWith_of_lipschitzWith_gradient⟩

/-- For a differentiable convex function on a Hilbert space, `K`-smoothness is equivalent
to a `K`-Lipschitz Fréchet derivative. -/
theorem lipschitzSmoothWith_iff_lipschitzWith_fderiv
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔ LipschitzWith K (fderiv ℝ f) :=
  (hc.lipschitzSmoothWith_iff_lipschitzWith_gradient hf).trans
    lipschitzWith_fderiv_iff_lipschitzWith_gradient.symm

/-- **Baillon-Haddad theorem** (`iff` form): for a differentiable convex function on a Hilbert
space, `K`-Lipschitz gradient is equivalent to `K`-cocoercivity. -/
theorem cocoerciveWith_iff_lipschitzWith_gradient
    (hc : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    CocoerciveWith K f ↔ LipschitzWith K (∇ f) :=
  (hc.lipschitzSmoothWith_iff_cocoerciveWith hf).symm.trans
    (hc.lipschitzSmoothWith_iff_lipschitzWith_gradient hf)

end ConvexOn
