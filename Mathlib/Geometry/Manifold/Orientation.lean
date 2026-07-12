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
# Orientations of manifolds

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

The model vector space is assumed finite-dimensional, as `LinearMap.det` is only geometrically
meaningful here under that hypothesis.

An intrinsic model via sections of an orientation bundle attached to the top exterior power of the
tangent bundle is deferred until that bundle infrastructure is available.
-/

@[expose] public section

noncomputable section

namespace Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- Data of a chosen orientation on a finite-dimensional manifold: a `ℤˣ`-valued sign for the chart
at each point, locally constant on the chart domain, compatible with the tangent coordinate changes.
-/
@[ext]
structure Orientation (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [FiniteDimensional ℝ E] where
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
class Orientable (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] : Prop where
  /-- An orientation witnessing orientability. -/
  nonemptyOrientation : Nonempty (Orientation I M)

/-- Typeclass choosing a specific orientation on a manifold. -/
class OrientedManifold (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- The chosen orientation of the manifold. -/
  manifoldOrientation : Orientation I M

/-- An oriented manifold is orientable. -/
instance (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [o : OrientedManifold I M] : Orientable I M := ⟨⟨o.manifoldOrientation⟩⟩

variable {I} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

namespace Orientation

/-- The pointwise sign difference (in `ℤˣ`) between two manifold orientations, read off the
chart at each point. -/
def deltaFn (o₀ o : Orientation I M) (z : M) : ℤˣ :=
  o.chartSign z z * o₀.chartSign z z

/-- The sign difference can be computed from any chart whose domain contains the point. -/
theorem deltaFn_eq (o₀ o : Orientation I M) {x z : M} (hz : z ∈ (chartAt H x).source) :
    deltaFn o₀ o z = o.chartSign x z * o₀.chartSign x z := by
  exact (by decide : ∀ a b c d : ℤˣ, (a = b ↔ c = d) → a * c = b * d) _ _ _ _
    ((o.compatible z x z (mem_chart_source H z) hz).symm.trans
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

@[simp]
theorem deltaLC_apply (o₀ o : Orientation I M) (z : M) : deltaLC o₀ o z = deltaFn o₀ o z :=
  rfl

/-- Modify a manifold orientation by flipping every chart-sign according to a locally constant
`ℤˣ`-valued function. -/
def twist (o₀ : Orientation I M) (δ : LocallyConstant M ℤˣ) : Orientation I M where
  chartSign x z := open scoped Classical in
    if z ∈ (chartAt H x).source then δ z * o₀.chartSign x z else 1
  continuousOn_chartSign x :=
    (δ.continuous.continuousOn.mul (o₀.continuousOn_chartSign x)).congr
      (fun z hz ↦ by simp [hz])
  chartSign_eq_one_of_notMem x z hz := if_neg hz
  compatible x y z hzx hzy := by
    simp only [if_pos hzx, if_pos hzy, mul_right_inj]
    exact o₀.compatible x y z hzx hzy

@[simp]
theorem twist_chartSign (o₀ : Orientation I M) (δ : LocallyConstant M ℤˣ) {x z : M}
    (hz : z ∈ (chartAt H x).source) :
    (twist o₀ δ).chartSign x z = δ z * o₀.chartSign x z := by
  simp [twist, hz]

/-- Relative to a fixed base orientation `o₀`, the manifold orientations are in bijection with
locally constant `ℤˣ`-valued functions on `M`. -/
noncomputable def equivLocallyConstant (o₀ : Orientation I M) :
    Orientation I M ≃ LocallyConstant M ℤˣ where
  toFun o := deltaLC o₀ o
  invFun δ := twist o₀ δ
  left_inv o := by
    ext x z : 3
    by_cases hz : z ∈ (chartAt H x).source
    · rw [twist_chartSign _ _ hz, deltaLC_apply, deltaFn_eq o₀ o hz]
      exact (by decide : ∀ a b : ℤˣ, a * b * b = a) _ _
    · rw [(twist o₀ (deltaLC o₀ o)).chartSign_eq_one_of_notMem x z hz,
        o.chartSign_eq_one_of_notMem x z hz]
  right_inv δ := by
    ext z : 1
    rw [deltaLC_apply, deltaFn, twist_chartSign _ _ (mem_chart_source H z)]
    exact (by decide : ∀ a b : ℤˣ, a * b * b = a) _ _

/-- Negating an orientation reverses all of its chart signs. -/
instance : InvolutiveNeg (Orientation I M) where
  neg o := twist o (LocallyConstant.const M (-1))
  neg_neg o := by
    ext x z : 3
    by_cases hz : z ∈ (chartAt H x).source
    · simp [twist, hz]
    · rw [(twist (twist o (LocallyConstant.const M (-1)))
          (LocallyConstant.const M (-1))).chartSign_eq_one_of_notMem x z hz,
        o.chartSign_eq_one_of_notMem x z hz]

@[simp]
theorem neg_chartSign (o : Orientation I M) {x z : M} (hz : z ∈ (chartAt H x).source) :
    (-o).chartSign x z = -o.chartSign x z := by
  rw [show -o = twist o (LocallyConstant.const M (-1)) from rfl,
    twist_chartSign _ _ hz]
  exact neg_one_mul _

/-- An orientation on a nonempty manifold differs from its negation. -/
theorem ne_neg [Nonempty M] (o : Orientation I M) : o ≠ -o := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  exact units_ne_neg_self (o.chartSign x x) <| by
    simpa using congrArg (fun o : Orientation I M ↦ o.chartSign x x) h

/-- Two orientations of a preconnected manifold are equal or negatives of each other. -/
theorem eq_or_eq_neg [PreconnectedSpace M] (o o₀ : Orientation I M) :
    o = o₀ ∨ o = -o₀ := by
  obtain ⟨δ, hδ⟩ := (deltaLC o₀ o).exists_eq_const
  rcases Int.units_eq_one_or δ with rfl | rfl
  · left
    apply (equivLocallyConstant o₀).injective
    exact hδ.trans (by ext z; simp [equivLocallyConstant, deltaLC, deltaFn])
  · right
    apply (equivLocallyConstant o₀).injective
    exact hδ.trans (by
      ext z
      simp [equivLocallyConstant, deltaLC, deltaFn, twist, mem_chart_source])

variable (I) in
theorem natCard_eq_two_pow_of_natCard_connectedComponents_eq [Orientable I M]
    [Finite (ConnectedComponents M)] {n : ℕ}
    (hn : Nat.card (ConnectedComponents M) = n) :
    Nat.card (Orientation I M) = 2 ^ n := by
  letI : LocallyConnectedSpace M := I.locallyConnectedSpace M
  let o₀ : Orientation I M := Classical.choice (Orientable.nonemptyOrientation (I := I) (M := M))
  calc
    Nat.card (Orientation I M)
    _ = Nat.card (LocallyConstant M ℤˣ) :=
          Nat.card_congr (equivLocallyConstant o₀)
    _ = Nat.card (ConnectedComponents M → ℤˣ) :=
          Nat.card_congr LocallyConstant.equivConnectedComponents
    _ = Nat.card ℤˣ ^ Nat.card (ConnectedComponents M) := by
          simpa using (Nat.card_fun (α := ConnectedComponents M) (β := ℤˣ))
    _ = 2 ^ n := by rw [show Nat.card ℤˣ = 2 from by simp [Nat.card_eq_fintype_card], hn]

end Orientation

end Manifold
