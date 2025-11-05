/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Equicontinuity in metric spaces

This file contains various facts about (uniform) equicontinuity in metric spaces. Most
importantly, we prove the usual characterization of equicontinuity of `F` at `x₀` in the case of
(pseudo) metric spaces: `∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε`,
and we prove that functions sharing a common (local or global) continuity modulus are
(locally or uniformly) equicontinuous.

## Main statements

* `Metric.equicontinuousAt_iff`: characterization of equicontinuity for families of functions
  between (pseudo) metric spaces.
* `Metric.equicontinuousAt_of_continuity_modulus`: convenient way to prove equicontinuity at a
  point of a family of functions to a (pseudo) metric space by showing that they share a common
  *local* continuity modulus.
* `Metric.uniformEquicontinuous_of_continuity_modulus`: convenient way to prove uniform
  equicontinuity of a family of functions to a (pseudo) metric space by showing that they share a
  common *global* continuity modulus.

## Tags

equicontinuity, continuity modulus
-/


open Filter Topology Uniformity

variable {α β ι : Type*} [PseudoMetricSpace α]

namespace Metric

/-- Characterization of equicontinuity for families of functions taking values in a (pseudo) metric
space. -/
theorem equicontinuousAt_iff_right {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) < ε :=
  uniformity_basis_dist.equicontinuousAt_iff_right

/-- Characterization of equicontinuity for families of functions between (pseudo) metric spaces. -/
theorem equicontinuousAt_iff {ι : Type*} [PseudoMetricSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε :=
  nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist

/-- Reformulation of `equicontinuousAt_iff_pair` for families of functions taking values in a
(pseudo) metric space. -/
protected theorem equicontinuousAt_iff_pair {ι : Type*} [TopologicalSpace β] {F : ι → β → α}
    {x₀ : β} :
    EquicontinuousAt F x₀ ↔
      ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ x' ∈ U, ∀ i, dist (F i x) (F i x') < ε := by
  rw [equicontinuousAt_iff_pair]
  constructor <;> intro H
  · intro ε hε
    exact H _ (dist_mem_uniformity hε)
  · intro U hU
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    refine Exists.imp (fun V => And.imp_right fun h => ?_) (H _ hε)
    exact fun x hx x' hx' i => hεU (h _ hx _ hx' i)

/-- Characterization of uniform equicontinuity for families of functions taking values in a
(pseudo) metric space. -/
theorem uniformEquicontinuous_iff_right {ι : Type*} [UniformSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔ ∀ ε > 0, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, dist (F i xy.1) (F i xy.2) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff_right

/-- Characterization of uniform equicontinuity for families of functions between
(pseudo) metric spaces. -/
theorem uniformEquicontinuous_iff {ι : Type*} [PseudoMetricSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist

/-- For a family of functions to a (pseudo) metric spaces, a convenient way to prove
equicontinuity at a point is to show that all of the functions share a common *local* continuity
modulus. -/
theorem equicontinuousAt_of_continuity_modulus {ι : Type*} [TopologicalSpace β] {x₀ : β}
    (b : β → ℝ) (b_lim : Tendsto b (𝓝 x₀) (𝓝 0)) (F : ι → β → α)
    (H : ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) ≤ b x) : EquicontinuousAt F x₀ := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε ε0
  filter_upwards [b_lim (Iio_mem_nhds ε0), H] using fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
uniform equicontinuity is to show that all of the functions share a common *global* continuity
modulus. -/
theorem uniformEquicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : UniformEquicontinuous F := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε ε0
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine ⟨δ, δ0, fun x y hxy i => ?_⟩
  calc
    dist (F i x) (F i y) ≤ b (dist x y) := H x y i
    _ ≤ |b (dist x y)| := le_abs_self _
    _ = dist (b (dist x y)) 0 := by simp [Real.dist_eq]
    _ < ε := hδ (by simpa only [Real.dist_eq, tsub_zero, abs_dist] using hxy)

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
equicontinuity is to show that all of the functions share a common *global* continuity modulus. -/
theorem equicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : Equicontinuous F :=
  (uniformEquicontinuous_of_continuity_modulus b b_lim F H).equicontinuous

end Metric
