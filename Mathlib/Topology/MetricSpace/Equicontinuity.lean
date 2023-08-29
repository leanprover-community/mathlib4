/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Equicontinuity

#align_import topology.metric_space.equicontinuity from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Equicontinuity in metric spaces

This files contains various facts about (uniform) equicontinuity in metric spaces. Most
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
#align metric.equicontinuous_at_iff_right Metric.equicontinuousAt_iff_right

/-- Characterization of equicontinuity for families of functions between (pseudo) metric spaces. -/
theorem equicontinuousAt_iff {ι : Type*} [PseudoMetricSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε :=
  nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist
#align metric.equicontinuous_at_iff Metric.equicontinuousAt_iff

/-- Reformulation of `equicontinuousAt_iff_pair` for families of functions taking values in a
(pseudo) metric space. -/
protected theorem equicontinuousAt_iff_pair {ι : Type*} [TopologicalSpace β] {F : ι → β → α}
    {x₀ : β} :
    EquicontinuousAt F x₀ ↔
      ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ x' ∈ U, ∀ i, dist (F i x) (F i x') < ε := by
  rw [equicontinuousAt_iff_pair]
  -- ⊢ (∀ (U : Set (α × α)), U ∈ 𝓤 α → ∃ V, V ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ V → ∀ (y : β) …
  constructor <;> intro H
  -- ⊢ (∀ (U : Set (α × α)), U ∈ 𝓤 α → ∃ V, V ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ V → ∀ (y : β) …
                  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ U, U ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ U → ∀ (x' : β), x' ∈ U → ∀ …
                  -- ⊢ ∀ (U : Set (α × α)), U ∈ 𝓤 α → ∃ V, V ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ V → ∀ (y : β), …
  · intro ε hε
    -- ⊢ ∃ U, U ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ U → ∀ (x' : β), x' ∈ U → ∀ (i : ι), dist (F i …
    exact H _ (dist_mem_uniformity hε)
    -- 🎉 no goals
  · intro U hU
    -- ⊢ ∃ V, V ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ V → ∀ (y : β), y ∈ V → ∀ (i : ι), (F i x, F i …
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    -- ⊢ ∃ V, V ∈ 𝓝 x₀ ∧ ∀ (x : β), x ∈ V → ∀ (y : β), y ∈ V → ∀ (i : ι), (F i x, F i …
    refine' Exists.imp (fun V => And.imp_right fun h => _) (H _ hε)
    -- ⊢ ∀ (x : β), x ∈ V → ∀ (y : β), y ∈ V → ∀ (i : ι), (F i x, F i y) ∈ U
    exact fun x hx x' hx' i => hεU (h _ hx _ hx' i)
    -- 🎉 no goals
#align metric.equicontinuous_at_iff_pair Metric.equicontinuousAt_iff_pair

/-- Characterization of uniform equicontinuity for families of functions taking values in a
(pseudo) metric space. -/
theorem uniformEquicontinuous_iff_right {ι : Type*} [UniformSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔ ∀ ε > 0, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, dist (F i xy.1) (F i xy.2) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff_right
#align metric.uniform_equicontinuous_iff_right Metric.uniformEquicontinuous_iff_right

/-- Characterization of uniform equicontinuity for families of functions between
(pseudo) metric spaces. -/
theorem uniformEquicontinuous_iff {ι : Type*} [PseudoMetricSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist
#align metric.uniform_equicontinuous_iff Metric.uniformEquicontinuous_iff

/-- For a family of functions to a (pseudo) metric spaces, a convenient way to prove
equicontinuity at a point is to show that all of the functions share a common *local* continuity
modulus. -/
theorem equicontinuousAt_of_continuity_modulus {ι : Type*} [TopologicalSpace β] {x₀ : β}
    (b : β → ℝ) (b_lim : Tendsto b (𝓝 x₀) (𝓝 0)) (F : ι → β → α)
    (H : ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) ≤ b x) : EquicontinuousAt F x₀ := by
  rw [Metric.equicontinuousAt_iff_right]
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∀ᶠ (x : β) in 𝓝 x₀, ∀ (i : ι), dist (F i x₀) (F i x) < ε
  intro ε ε0
  -- ⊢ ∀ᶠ (x : β) in 𝓝 x₀, ∀ (i : ι), dist (F i x₀) (F i x) < ε
  -- porting note: Lean 3 didn't need `Filter.mem_map.mp` here
  filter_upwards [Filter.mem_map.mp <| b_lim (Iio_mem_nhds ε0), H] using
    fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁
#align metric.equicontinuous_at_of_continuity_modulus Metric.equicontinuousAt_of_continuity_modulus

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
uniform equicontinuity is to show that all of the functions share a common *global* continuity
modulus. -/
theorem uniformEquicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : UniformEquicontinuous F := by
  rw [Metric.uniformEquicontinuous_iff]
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∃ δ, δ > 0 ∧ ∀ (x y : β), dist x y < δ → ∀ (i : ι), dist  …
  intro ε ε0
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (x y : β), dist x y < δ → ∀ (i : ι), dist (F i x) (F i y) < ε
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  -- ⊢ ∃ δ, δ > 0 ∧ ∀ (x y : β), dist x y < δ → ∀ (i : ι), dist (F i x) (F i y) < ε
  refine' ⟨δ, δ0, fun x y hxy i => _⟩
  -- ⊢ dist (F i x) (F i y) < ε
  calc
    dist (F i x) (F i y) ≤ b (dist x y) := H x y i
    _ ≤ |b (dist x y)| := (le_abs_self _)
    _ = dist (b (dist x y)) 0 := by simp [Real.dist_eq]
    _ < ε := hδ (by simpa only [Real.dist_eq, tsub_zero, abs_dist] using hxy)
#align metric.uniform_equicontinuous_of_continuity_modulus Metric.uniformEquicontinuous_of_continuity_modulus

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
equicontinuity is to show that all of the functions share a common *global* continuity modulus. -/
theorem equicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : Equicontinuous F :=
  (uniformEquicontinuous_of_continuity_modulus b b_lim F H).equicontinuous
#align metric.equicontinuous_of_continuity_modulus Metric.equicontinuous_of_continuity_modulus

end Metric
