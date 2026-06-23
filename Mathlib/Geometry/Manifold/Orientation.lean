/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Manifold orientation helpers

This file defines orientation structures for manifolds.

## Main definitions

* `Manifold.Orientable`: manifold-level orientability predicate.
* `Manifold.ManifoldOrientation`: orientation data, encoded by a `ZMod 2`-valued sign for the chart
  at each point, locally constant on the chart domain, with the compatibility that a coordinate
  change is orientation-preserving (positive Jacobian determinant) exactly when the two chart signs
  agree.
* `Manifold.OrientedManifold`: typeclass choosing a specific manifold orientation.

## Implementation note

A manifold orientation assigns, to the chart at each point `x`, a `ZMod 2`-valued sign function
`chartSign x : M → ZMod 2` (only meaningful on `(chartAt H x).source`). It is required to be
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

section Orientable

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- Data of a chosen orientation on a manifold: a `ZMod 2`-valued sign for the chart at each point,
locally constant on the chart domain, compatible with the tangent coordinate changes. -/
@[ext]
structure ManifoldOrientation (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] where
  /-- The sign of the chart at `x`, evaluated at each point; only meaningful on
  `(chartAt H x).source`. -/
  chartSign : M → M → ZMod 2
  /-- Each chart-sign is continuous (hence locally constant) on its chart domain. -/
  continuousOn_chartSign : ∀ x, ContinuousOn (chartSign x) (chartAt H x).source
  /-- The chart-sign is `1` outside the chart domain. -/
  chartSign_eq_one_of_not_mem : ∀ x z, z ∉ (chartAt H x).source → chartSign x z = 1
  /-- The coordinate change from the chart at `x` to the chart at `y`, evaluated at `z`, has
  positive Jacobian determinant exactly when the two chart signs agree at `z`. -/
  compatible : ∀ x y z, z ∈ (chartAt H x).source → z ∈ (chartAt H y).source →
    (0 < LinearMap.det (((trivializationAt E (TangentSpace I) x).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) y) z).toLinearEquiv.toLinearMap) ↔
      chartSign x z = chartSign y z)

/-- A manifold is orientable if it admits a manifold orientation. -/
abbrev Orientable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] : Prop :=
  Nonempty (ManifoldOrientation I M)

/-- Typeclass choosing a specific orientation on a manifold. -/
class OrientedManifold (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- The chosen orientation of the manifold. -/
  manifoldOrientation : ManifoldOrientation I M

/-- An oriented manifold is orientable. -/
instance (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [o : OrientedManifold I M] : Orientable I M := ⟨o.manifoldOrientation⟩

theorem point_has_two_manifoldOrientations :
    ∃ oPos oNeg : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (EuclideanSpace ℝ (Fin 0)),
      oPos ≠ oNeg ∧
      ∀ o : ManifoldOrientation (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
        (EuclideanSpace ℝ (Fin 0)), o = oPos ∨ o = oNeg := by
  refine ⟨{ chartSign := fun _ _ => 0
            continuousOn_chartSign := fun _ => continuousOn_const
            chartSign_eq_one_of_not_mem := fun x z hz =>
              absurd (by rw [Subsingleton.elim z x]; exact mem_chart_source _ x) hz
            compatible := fun _ _ _ _ _ => iff_of_true
              (by rw [LinearMap.det_eq_one_of_finrank_eq_zero (by simp [finrank_euclideanSpace])]
                  exact one_pos) rfl },
          { chartSign := fun _ _ => 1
            continuousOn_chartSign := fun _ => continuousOn_const
            chartSign_eq_one_of_not_mem := fun x z hz =>
              absurd (by rw [Subsingleton.elim z x]; exact mem_chart_source _ x) hz
            compatible := fun _ _ _ _ _ => iff_of_true
              (by rw [LinearMap.det_eq_one_of_finrank_eq_zero (by simp [finrank_euclideanSpace])]
                  exact one_pos) rfl },
          ?_, ?_⟩
  · intro h
    exact absurd (congrFun (congrFun (congrArg ManifoldOrientation.chartSign h) default) default)
      (by decide)
  · intro o
    have hval : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    refine (hval (o.chartSign default default)).imp (fun h => ?_) (fun h => ?_) <;>
      exact ManifoldOrientation.ext (funext fun x => funext fun z => by
        rw [Subsingleton.elim x default, Subsingleton.elim z default]; exact h)

section Cardinality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The pointwise sign difference (in `ZMod 2`) between two manifold orientations, read off the
chart at each point. -/
def deltaFn (o₀ o : ManifoldOrientation I M) (z : M) : ZMod 2 :=
  o.chartSign z z + o₀.chartSign z z

/-- The sign difference can be computed from any chart whose domain contains the point. -/
theorem deltaFn_eq (o₀ o : ManifoldOrientation I M) {x z : M} (hz : z ∈ (chartAt H x).source) :
    deltaFn I o₀ o z = o.chartSign x z + o₀.chartSign x z := by
  have key : ∀ a b c d : ZMod 2, (a = b ↔ c = d) → a + c = b + d := by decide
  exact key _ _ _ _ ((o.compatible z x z (mem_chart_source H z) hz).symm.trans
    (o₀.compatible z x z (mem_chart_source H z) hz))

theorem deltaFn_isLocallyConstant (o₀ o : ManifoldOrientation I M) :
    IsLocallyConstant (deltaFn I o₀ o) := by
  rw [IsLocallyConstant.iff_continuous, continuous_iff_continuousAt]
  intro p
  refine ContinuousOn.continuousAt ?_
    ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  exact ((o.continuousOn_chartSign p).add (o₀.continuousOn_chartSign p)).congr
    (fun z hz => deltaFn_eq I o₀ o hz)

/-- The sign difference between two manifold orientations, as a `LocallyConstant` function
`M → ZMod 2`. -/
def deltaLC (o₀ o : ManifoldOrientation I M) : LocallyConstant M (ZMod 2) :=
  ⟨deltaFn I o₀ o, deltaFn_isLocallyConstant I o₀ o⟩

open Classical in
/-- Modify a manifold orientation by flipping every chart-sign according to a locally constant
`ZMod 2`-valued function. -/
def twist (o₀ : ManifoldOrientation I M) (δ : LocallyConstant M (ZMod 2)) :
    ManifoldOrientation I M where
  chartSign x z := if z ∈ (chartAt H x).source then δ z + o₀.chartSign x z else 1
  continuousOn_chartSign x :=
    (δ.continuous.continuousOn.add (o₀.continuousOn_chartSign x)).congr
      (fun z hz => by simp only [if_pos hz, Pi.add_apply])
  chartSign_eq_one_of_not_mem x z hz := if_neg hz
  compatible x y z hzx hzy := by
    simp only [if_pos hzx, if_pos hzy, add_right_inj]
    exact o₀.compatible x y z hzx hzy

/-- Relative to a fixed base orientation `o₀`, the manifold orientations are in bijection with
locally constant `ZMod 2`-valued functions on `M`. -/
noncomputable def manifoldOrientationEquivLocallyConstant (o₀ : ManifoldOrientation I M) :
    ManifoldOrientation I M ≃ LocallyConstant M (ZMod 2) where
  toFun o := deltaLC I o₀ o
  invFun δ := twist I o₀ δ
  left_inv o := by
    classical
    apply ManifoldOrientation.ext
    funext x z
    by_cases hz : z ∈ (chartAt H x).source
    · change (if z ∈ (chartAt H x).source then (deltaLC I o₀ o) z + o₀.chartSign x z else 1)
          = o.chartSign x z
      rw [if_pos hz]
      change deltaFn I o₀ o z + o₀.chartSign x z = o.chartSign x z
      rw [deltaFn_eq I o₀ o hz]
      exact (by decide : ∀ a b : ZMod 2, a + b + b = a) _ _
    · change (if z ∈ (chartAt H x).source then (deltaLC I o₀ o) z + o₀.chartSign x z else 1)
          = o.chartSign x z
      rw [if_neg hz, o.chartSign_eq_one_of_not_mem x z hz]
  right_inv δ := by
    classical
    ext z
    change (if z ∈ (chartAt H z).source then δ z + o₀.chartSign z z else 1) + o₀.chartSign z z = δ z
    rw [if_pos (mem_chart_source H z)]
    exact (by decide : ∀ a b : ZMod 2, a + b + b = a) _ _

/-- On a locally connected space, locally constant `ZMod 2`-valued functions correspond to
arbitrary functions on the connected components. -/
noncomputable def locallyConstantEquivConnectedComponents [LocallyConnectedSpace M] :
    LocallyConstant M (ZMod 2) ≃ (ConnectedComponents M → ZMod 2) where
  toFun f := Quotient.lift (fun x : M => f x) (by
    intro x y hxy
    have hyx : y ∈ connectedComponent x := by
      simpa [hxy.symm] using (mem_connectedComponent : y ∈ connectedComponent y)
    exact f.apply_eq_of_isPreconnected isConnected_connectedComponent.isPreconnected
      mem_connectedComponent hyx)
  invFun g :=
    ⟨fun x => g x,
      IsLocallyConstant.of_constant_on_connected_components (fun x y hy => by
        exact congrArg g (ConnectedComponents.coe_eq_coe'.2 hy))⟩
  left_inv f := by
    ext x
    rfl
  right_inv g := by
    funext c
    rcases ConnectedComponents.surjective_coe c with ⟨x, rfl⟩
    rfl

theorem natCard_manifoldOrientation_eq_two_pow_of_natCard_connectedComponents_eq
    [LocallyConnectedSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [Orientable I M]
    [Finite (ConnectedComponents M)] {n : ℕ}
    (hn : Nat.card (ConnectedComponents M) = n) :
    Nat.card (ManifoldOrientation I M) = 2 ^ n := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  classical
  let o₀ : ManifoldOrientation I M :=
    Classical.choice (show Nonempty (ManifoldOrientation I M) from ‹Orientable I M›)
  calc
    Nat.card (ManifoldOrientation I M)
        = Nat.card (LocallyConstant M (ZMod 2)) :=
          Nat.card_congr (manifoldOrientationEquivLocallyConstant I o₀)
    _ = Nat.card (ConnectedComponents M → ZMod 2) :=
          Nat.card_congr (locallyConstantEquivConnectedComponents)
    _ = Nat.card (ZMod 2) ^ Nat.card (ConnectedComponents M) := by
          simpa using (Nat.card_fun (α := ConnectedComponents M) (β := ZMod 2))
    _ = 2 ^ n := by simp [hn]

end Cardinality

end Orientable

end Manifold
