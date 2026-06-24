/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!

# Epsilon dense

In this file, we prove [BGR, Prop 1.1.4./2][bosch-guntzer-remmert]: If `G` is a normed group and
`H` is a subgroup which is `ε`-dense, then it is dense.

## Main defintion
* `epsilonDense`: We say a subgroup `H` is `ε`-dense if for all `g : G` there exists a `h : H`,
  such that `‖g⁻¹ * (h : G)‖ ≤ ε * ‖g‖`.

## Main theorem
* `dense_epsilonDense`: A subgroup being `ε`-dense implies it is dense.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

-/

@[expose] public section

variable {G : Type*} [SeminormedGroup G] (H : Subgroup G)

namespace SeminormedGroup

open Metric

/-- We say a subgroup `H` is `ε`-dense if for all `g : G` there exists a `h : H`, such that
  `‖g⁻¹ * (h : G)‖ ≤ ε * ‖g‖`. -/
@[to_additive]
def epsilonDense (ε : ℝ) : Prop := ∀ g : G, ∃ h : H, ‖g⁻¹ * (h : G)‖ ≤ ε * ‖g‖

@[to_additive]
lemma epsilonDense_dist_eq_zero {ε : ℝ} (h1 : 0 < ε) (h2 : ε < 1)
    (h : epsilonDense H ε) (g : G) : infDist g H = 0 := by
  by_contra
  suffices ∃ h₁ : H, ‖g⁻¹ * h₁‖ < ε⁻¹ * infDist g H by
    obtain ⟨h₁, h₁_lt⟩ := this
    obtain ⟨h₂, h₂_le⟩ := h ((h₁ : G)⁻¹ * g)
    suffices dist g (↑h₁ * ↑h₂) < infDist g H by
      grind [infDist_le_dist_of_mem (x := g) (s := H) (y := h₁ * h₂) (by aesop)]
    calc _ = ‖((h₁ : G)⁻¹ * g)⁻¹ * h₂‖ := by rw [dist_eq]; group
         _ ≤ ε * ‖(h₁ : G)⁻¹ * g‖ := h₂_le
         _ = ε * ‖g⁻¹ * (h₁ : G)‖ := by rw [← dist_eq, dist_comm, dist_eq]
         _ < ε * (ε⁻¹ * Metric.infDist g H) := by gcongr
         _ = infDist g H := by grind
  suffices infDist g ↑H < ε⁻¹ * infDist g ↑H by
    obtain ⟨y, hy, _⟩ := (infDist_lt_iff ⟨1, H.one_mem⟩).mp this
    exact ⟨⟨y, hy⟩, by rwa [← dist_eq]⟩
  exact (lt_mul_iff_one_lt_left (by grind [infDist_nonneg])).mpr ((one_lt_inv₀ h1).mpr h2)

@[to_additive]
lemma dense_epsilonDense (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1) (h : epsilonDense H ε) :
    Dense (H : Set G) := by
  simp [dense_iff_closure_eq, Metric.closure_eq, epsilonDense_dist_eq_zero H h1 h2 h]

end SeminormedGroup
