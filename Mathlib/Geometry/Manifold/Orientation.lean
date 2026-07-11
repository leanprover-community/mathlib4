/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Manifold orientation helpers

This file defines orientation structures for manifolds.

## Main definitions

* `Manifold.Orientable`: manifold-level orientability predicate.
* `Manifold.Orientation`: orientation data, encoded by a `ℤˣ`-valued sign for the chart
  at each point, locally constant on the chart domain, with the compatibility that a coordinate
  change is orientation-preserving (positive Jacobian determinant) exactly when the two chart signs
  agree.
* `Manifold.OrientedManifold`: typeclass choosing a specific manifold orientation.

## Implementation note

A manifold orientation assigns, to the chart at each point `x`, a `ℤˣ`-valued sign function
`chartSign x : M → ℤˣ` (only meaningful on `(chartAt H x).source`). It is required to be
continuous (equivalently locally constant) on the chart domain, to equal `1` outside it (so that
equality of the data is equality of orientations), and to satisfy the compatibility condition that
the tangent coordinate change from chart `x` to chart `y` at a point `z` has positive determinant
iff `chartSign x z = chartSign y z`.

An intrinsic model via sections of an orientation bundle attached to the top exterior power of the
tangent bundle is deferred until that bundle infrastructure is available.
-/

@[expose] public section

noncomputable section

open scoped Manifold
open Set

namespace Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- Data of a chosen orientation on a manifold: a `ℤˣ`-valued sign for the chart at each point,
locally constant on the chart domain, compatible with the tangent coordinate changes. -/
@[ext]
structure Orientation (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] where
  /-- The sign of the chart at `x`, evaluated at each point; only meaningful on
  `(chartAt H x).source`. -/
  chartSign : M → M → ℤˣ
  /-- Each chart-sign is continuous (hence locally constant) on its chart domain. -/
  continuousOn_chartSign : ∀ x, ContinuousOn (chartSign x) (chartAt H x).source
  /-- The chart-sign is `1` outside the chart domain. -/
  chartSign_eq_one_of_notMem : ∀ x z, z ∉ (chartAt H x).source → chartSign x z = 1
  /-- The coordinate change from the chart at `x` to the chart at `y`, evaluated at `z`, has
  positive Jacobian determinant exactly when the two chart signs agree at `z`. -/
  compatible : ∀ x y z, z ∈ (chartAt H x).source → z ∈ (chartAt H y).source →
    (0 < LinearMap.det (tangentCoordChange I x y z).toLinearMap ↔
      chartSign x z = chartSign y z)

/-- A manifold is orientable if it admits a manifold orientation. -/
abbrev Orientable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] : Prop :=
  Nonempty (Orientation I M)

/-- Typeclass choosing a specific orientation on a manifold. -/
class OrientedManifold (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- The chosen orientation of the manifold. -/
  manifoldOrientation : Orientation I M

/-- An oriented manifold is orientable. -/
instance (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [o : OrientedManifold I M] : Orientable I M := ⟨o.manifoldOrientation⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

namespace Orientation

variable {I}

/-- The pointwise sign difference (in `ℤˣ`) between two manifold orientations, read off the
chart at each point. -/
def deltaFn (o₀ o : Orientation I M) (z : M) : ℤˣ :=
  o.chartSign z z * o₀.chartSign z z

/-- The sign difference can be computed from any chart whose domain contains the point. -/
theorem deltaFn_eq (o₀ o : Orientation I M) {x z : M} (hz : z ∈ (chartAt H x).source) :
    deltaFn o₀ o z = o.chartSign x z * o₀.chartSign x z := by
  have key : ∀ a b c d : ℤˣ, (a = b ↔ c = d) → a * c = b * d := by decide
  exact key _ _ _ _ ((o.compatible z x z (mem_chart_source H z) hz).symm.trans
    (o₀.compatible z x z (mem_chart_source H z) hz))

theorem isLocallyConstant_deltaFn (o₀ o : Orientation I M) :
    IsLocallyConstant (deltaFn o₀ o) := by
  rw [IsLocallyConstant.iff_continuous, continuous_iff_continuousAt]
  intro p
  refine ContinuousOn.continuousAt ?_
    ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  exact ((o.continuousOn_chartSign p).mul (o₀.continuousOn_chartSign p)).congr
    (fun z hz ↦ deltaFn_eq o₀ o hz)

/-- The sign difference between two manifold orientations, as a `LocallyConstant` function
`M → ℤˣ`. -/
def deltaLC (o₀ o : Orientation I M) : LocallyConstant M ℤˣ :=
  ⟨deltaFn o₀ o, isLocallyConstant_deltaFn o₀ o⟩

/-- Modify a manifold orientation by flipping every chart-sign according to a locally constant
`ℤˣ`-valued function. -/
def twist (o₀ : Orientation I M) (δ : LocallyConstant M ℤˣ) : Orientation I M where
  chartSign x z := open scoped Classical in
    if z ∈ (chartAt H x).source then δ z * o₀.chartSign x z else 1
  continuousOn_chartSign x :=
    (δ.continuous.continuousOn.mul (o₀.continuousOn_chartSign x)).congr
      (fun z hz ↦ by simp only [if_pos hz, Pi.mul_apply])
  chartSign_eq_one_of_notMem x z hz := if_neg hz
  compatible x y z hzx hzy := by
    simp only [if_pos hzx, if_pos hzy, mul_right_inj]
    exact o₀.compatible x y z hzx hzy

/-- Relative to a fixed base orientation `o₀`, the manifold orientations are in bijection with
locally constant `ℤˣ`-valued functions on `M`. -/
noncomputable def equivLocallyConstant (o₀ : Orientation I M) :
    Orientation I M ≃ LocallyConstant M ℤˣ where
  toFun o := deltaLC o₀ o
  invFun δ := twist o₀ δ
  left_inv o := by
    classical
    ext x z : 3
    by_cases hz : z ∈ (chartAt H x).source
    · change (if z ∈ (chartAt H x).source then (deltaLC o₀ o) z * o₀.chartSign x z else 1)
          = o.chartSign x z
      rw [if_pos hz]
      change deltaFn o₀ o z * o₀.chartSign x z = o.chartSign x z
      rw [deltaFn_eq o₀ o hz]
      exact (by decide : ∀ a b : ℤˣ, a * b * b = a) _ _
    · change (if z ∈ (chartAt H x).source then (deltaLC o₀ o) z * o₀.chartSign x z else 1)
          = o.chartSign x z
      rw [if_neg hz, o.chartSign_eq_one_of_notMem x z hz]
  right_inv δ := by
    classical
    ext z : 1
    change (if z ∈ (chartAt H z).source then δ z * o₀.chartSign z z else 1) * o₀.chartSign z z = δ z
    rw [if_pos (mem_chart_source H z)]
    exact (by decide : ∀ a b : ℤˣ, a * b * b = a) _ _

/-- The opposite of an orientation. -/
def opposite (o : Orientation I M) : Orientation I M :=
  twist o (LocallyConstant.const M (-1))

/-- An orientation on a nonempty manifold differs from its opposite. -/
theorem ne_opposite [Nonempty M] (o : Orientation I M) : o ≠ opposite o := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  apply (by decide : (1 : ℤˣ) ≠ -1)
  apply mul_right_cancel (b := o.chartSign x x)
  simpa only [opposite, twist, mem_chart_source, if_pos, LocallyConstant.coe_const,
    Function.const_apply, one_mul] using
    congrFun (congrFun (congrArg Orientation.chartSign h) x) x

/-- Two orientations of a preconnected manifold are equal or opposite. -/
theorem eq_or_eq_opposite [PreconnectedSpace M] (o o₀ : Orientation I M) :
    o = o₀ ∨ o = opposite o₀ := by
  let e := equivLocallyConstant o₀
  obtain ⟨δ, hδ⟩ := (deltaLC o₀ o).exists_eq_const
  change e o = _ at hδ
  rcases Int.units_eq_one_or δ with rfl | rfl
  · left
    apply e.injective
    exact hδ.trans (by ext z; simp [e, equivLocallyConstant, deltaLC, deltaFn])
  · right
    apply e.injective
    exact hδ.trans (by
      ext z
      simp [e, equivLocallyConstant, deltaLC, deltaFn, opposite, twist, mem_chart_source])

variable (I)

theorem natCard_eq_two_pow_of_natCard_connectedComponents_eq [Orientable I M]
    [Finite (ConnectedComponents M)] {n : ℕ}
    (hn : Nat.card (ConnectedComponents M) = n) :
    Nat.card (Orientation I M) = 2 ^ n := by
  letI : LocallyPathConnectedSpace (range I) := I.convex_range.locallyPathConnectedSpace
  letI : LocallyConnectedSpace H :=
    (I.leftInverse.isEmbedding I.continuous_symm I.continuous).toHomeomorph.locallyConnectedSpace
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let o₀ : Orientation I M := Classical.choice (show Nonempty (Orientation I M) from inferInstance)
  calc
    Nat.card (Orientation I M)
        = Nat.card (LocallyConstant M ℤˣ) :=
          Nat.card_congr (equivLocallyConstant o₀)
    _ = Nat.card (ConnectedComponents M → ℤˣ) :=
          Nat.card_congr LocallyConstant.equivConnectedComponents
    _ = Nat.card ℤˣ ^ Nat.card (ConnectedComponents M) := by
          simpa using (Nat.card_fun (α := ConnectedComponents M) (β := ℤˣ))
    _ = 2 ^ n := by rw [show Nat.card ℤˣ = 2 from by simp [Nat.card_eq_fintype_card], hn]

end Orientation

end Manifold
