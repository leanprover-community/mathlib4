/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Partial derivatives

This file concerns the partial derivatives of a bivariate function.

## Main results

- `hasStrictFDerivAt_uncurried_coprod`: establishing strict differentiability of the uncurried
  function in the product space, this requires validity of the mean value theorem in both underlying
  spaces.
-/

open scoped Topology

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
variable [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]

/-- If a bivariate function has partial derivatives $f_x$ and $f_y$ in a neighbourhood of a point
$(x_0,y_0)$, continuous at that point, then it is strictly differentiable there with derivative
$(\xi,\eta)\mapsto f_x(x_0,y_0)\cdot\xi + f_y(x_0,y_0)\cdot\eta$. -/
theorem hasStrictFDerivAt_uncurried_coprod [IsRCLikeNormedField 𝕜]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] {f : X → Y → Z} {x₀ : X} {y₀ : Y}
    {fx : X → Y → X →L[𝕜] Z} (cfx : ContinuousAt ↿fx (x₀, y₀))
    (dfx : ∀ᶠ z in 𝓝 (x₀, y₀), HasFDerivAt (f · z.2) (↿fx z) z.1)
    {fy : X → Y → Y →L[𝕜] Z} (cfy : ContinuousAt ↿fy (x₀, y₀))
    (dfy : ∀ᶠ z in 𝓝 (x₀, y₀), HasFDerivAt (f z.1 ·) ((↿fy) z) z.2) :
    HasStrictFDerivAt ↿f (.coprod (fx x₀ y₀) (fy x₀ y₀)) (x₀, y₀) := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hh⟩ : ∃ δ > 0, ∀ x y, x ∈ Metric.ball x₀ δ → y ∈ Metric.ball y₀ δ →
      (HasFDerivAt (f · y) (fx x y) x ∧ ‖fx x y - fx x₀ y₀‖ < c / 2) ∧
      (HasFDerivAt (f x ·) (fy x y) y ∧ ‖fy x y - fy x₀ y₀‖ < c / 2) := by
    simp_rw [← Set.forall_prod_set_iff, ball_prod_same]
    rw [← Metric.eventually_nhds_iff_ball]
    have cfx := cfx.eventually_mem (Metric.ball_mem_nhds (fx x₀ y₀) (half_pos hc))
    have cfy := cfy.eventually_mem (Metric.ball_mem_nhds (fy x₀ y₀) (half_pos hc))
    filter_upwards [dfx, cfx, dfy, cfy] with z dfx cfx dfy cfy using ⟨⟨dfx, cfx⟩, ⟨dfy, cfy⟩⟩
  rw [Metric.eventually_nhds_iff_ball]
  use δ, hδ
  intro ((x₁, y₁), (x₂, y₂)) hp
  rw [← ball_prod_same, ← ball_prod_same] at hp
  calc ‖f x₁ y₁ - f x₂ y₂ - (fx x₀ y₀ (x₁ - x₂) + fy x₀ y₀ (y₁ - y₂))‖
      = ‖(f x₁ y₁ - f x₂ y₁ - fx x₀ y₀ (x₁ - x₂)) + (f x₂ y₁ - f x₂ y₂ - fy x₀ y₀ (y₁ - y₂))‖ := by
        congr
        abel
    _ ≤ ‖f x₁ y₁ - f x₂ y₁ - fx x₀ y₀ (x₁ - x₂)‖ + ‖f x₂ y₁ - f x₂ y₂ - fy x₀ y₀ (y₁ - y₂)‖ := by
        apply norm_add_le
    _ ≤ c / 2 * ‖x₁ - x₂‖ + c / 2 * ‖y₁ - y₂‖ := by
        apply add_le_add
        · exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
            (fun x hx => (hh x y₁ hx hp.1.2).1.1.hasFDerivWithinAt)
            (fun x hx => le_of_lt (hh x y₁ hx hp.1.2).1.2) (convex_ball x₀ δ) hp.2.1 hp.1.1
        · exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
            (fun y hy => (hh x₂ y hp.2.1 hy).2.1.hasFDerivWithinAt)
            (fun y hy => le_of_lt (hh x₂ y hp.2.1 hy).2.2) (convex_ball y₀ δ) hp.2.2 hp.1.2
    _ ≤ c / 2 * ‖(x₁, y₁) - (x₂, y₂)‖ + c / 2 * ‖(x₁, y₁) - (x₂, y₂)‖ := by
        gcongr
        · apply le_max_left
        · apply le_max_right
    _ = c * ‖(x₁, y₁) - (x₂, y₂)‖ := by ring
