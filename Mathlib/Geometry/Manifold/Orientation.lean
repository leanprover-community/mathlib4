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
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Manifold orientation helpers

This file defines orientation structures for manifolds.

## Main definitions

* `Manifold.Orientable`: manifold-level orientability predicate.
* `Manifold.ManifoldOrientation`: orientation data encoded by a single `ZMod 2`-valued sign
  function on the manifold which is locally constant on each chart domain, after correcting by the
  chart-transition signs `Manifold.transSign`.
* `Manifold.OrientedManifold`: typeclass choosing a specific manifold orientation.

## Implementation note

A manifold orientation is encoded by a single `ZMod 2`-valued function `sign : M → ℤ/2`: the value
`sign z` records whether the chosen orientation at `z` agrees with the base orientation seen
through the chart at `z`. The continuity of the orientation is expressed by requiring, for each
chart `x`, that `z ↦ sign z + transSign x z` be continuous (equivalently locally constant) on
`(chartAt H x).source`, where `transSign x z` is the sign of the coordinate change from the chart
at `z` to the chart at `x`. This single-function model avoids the dependent types that arise when
storing locally constant data separately on each tangent trivialization domain.

An intrinsic model via sections of an orientation bundle attached to the top exterior power of the
tangent bundle is deferred until that bundle infrastructure is available.
-/

@[expose] public section

noncomputable section

open scoped Manifold
open Set

namespace Manifold

section Orientable

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- A fixed reference orientation on the model space. -/
noncomputable def baseOrientation : Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  (Module.finBasis ℝ E).orientation

/-- Apply a chart-sign bit to an orientation value: `0` keeps it, `1` flips it. -/
noncomputable def signedOrientation (s : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  if s = 0 then o else -o

omit [FiniteDimensional ℝ E] in
@[simp] theorem signedOrientation_zero (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    signedOrientation 0 o = o := if_pos rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem signedOrientation_one (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    signedOrientation 1 o = -o := if_neg (by decide)

omit [FiniteDimensional ℝ E] in
theorem signedOrientation_add (a b : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    signedOrientation (a + b) o =
      signedOrientation a (signedOrientation b o) := by
  by_cases ha : a = 0
  · subst ha
    simp [signedOrientation]
  · have ha1 : a = 1 := by
      fin_cases a
      · contradiction
      · rfl
    subst ha1
    by_cases hb : b = 0
    · subst hb
      simp [signedOrientation]
    · have hb1 : b = 1 := by
        fin_cases b
        · contradiction
        · rfl
      subst hb1
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [signedOrientation, h11]

omit [FiniteDimensional ℝ E] in
theorem signedOrientation_injective
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Function.Injective (fun s : ZMod 2 => signedOrientation s o) := by
  have key : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  intro a b h
  simp only [signedOrientation] at h
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · rw [if_pos ha, if_neg hb] at h
    exact absurd h (Module.Ray.ne_neg_self o)
  · rw [if_neg ha, if_pos hb] at h
    exact absurd h.symm (Module.Ray.ne_neg_self o)
  · rw [key a ha, key b hb]

namespace Orientation

omit [FiniteDimensional ℝ E] in
theorem map_signedOrientation (f : E ≃ₗ[ℝ] E) (s : ZMod 2)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation.map (Fin (Module.finrank ℝ E)) f (signedOrientation s o) =
      signedOrientation s (Orientation.map (Fin (Module.finrank ℝ E)) f o) := by
  by_cases hs : s = 0 <;> simp [signedOrientation, hs, Orientation.map_neg]

end Orientation

open Classical in
/-- The sign, relative to `baseOrientation`, of the coordinate change from the tangent
trivialization at `z` to the tangent trivialization at `x`, evaluated at `z`. It records whether
the base orientation seen through the chart at `z` agrees (`0`) or disagrees (`1`) with the one
seen through the chart at `x`. -/
noncomputable def transSign {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (x z : M) : ZMod 2 :=
  if Orientation.map (Fin (Module.finrank ℝ E))
      (((trivializationAt E (TangentSpace I) z).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) x) z).toLinearEquiv) baseOrientation = baseOrientation
    then 0 else 1

/-- The defining property of `transSign`: the coordinate change from the chart at `z` to the chart
at `x` sends `baseOrientation` to `signedOrientation (transSign I x z) baseOrientation`. -/
theorem transSign_baseOrientation_eq {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (x z : M) :
    Orientation.map (Fin (Module.finrank ℝ E))
        (((trivializationAt E (TangentSpace I) z).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) x) z).toLinearEquiv) baseOrientation =
      signedOrientation (transSign I x z) baseOrientation := by
  classical
  rw [transSign]
  split_ifs with h
  · rw [signedOrientation_zero]; exact h
  · rw [signedOrientation_one]
    exact ((Module.finBasis ℝ E).orientation_eq_or_eq_neg _).resolve_left h

/-- `transSign I x z` is `0` exactly when the coordinate change from the chart at `z` to the chart
at `x` is orientation-preserving, i.e. has positive determinant. -/
theorem transSign_eq_zero_iff {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (x z : M) :
    transSign I x z = 0 ↔
      0 < LinearMap.det (((trivializationAt E (TangentSpace I) z).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) x) z).toLinearEquiv : E →ₗ[ℝ] E) := by
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by simp
  rw [transSign]
  split_ifs with h
  · exact iff_of_true rfl ((baseOrientation.map_eq_iff_det_pos _ hcard).mp h)
  · exact iff_of_false (by decide)
      fun hdet => h ((baseOrientation.map_eq_iff_det_pos _ hcard).mpr hdet)

/-- Data of a chosen orientation on a manifold, encoded by a single `ZMod 2`-valued sign function
that is locally constant on each chart domain after correcting by the chart-transition signs. -/
@[ext]
structure ManifoldOrientation (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] where
  /-- The orientation sign at each point, measured against the base orientation seen through the
  chart at that point. -/
  sign : M → ZMod 2
  /-- Corrected by the chart transition, the sign is continuous (hence locally constant) on each
  chart domain. -/
  continuousOn_sign : ∀ x : M,
    ContinuousOn (fun z => sign z + transSign I x z) (chartAt H x).source

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
  have key : ∀ (s : EuclideanSpace ℝ (Fin 0) → ZMod 2) (x : EuclideanSpace ℝ (Fin 0)),
      ContinuousOn (fun z => s z + transSign 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) x z)
        (chartAt (EuclideanSpace ℝ (Fin 0)) x).source :=
    fun s x => Set.Subsingleton.continuousOn (fun a _ b _ => Subsingleton.elim a b) _
  refine ⟨⟨fun _ => 0, key _⟩, ⟨fun _ => 1, key _⟩, ?_, ?_⟩
  · intro h
    have : (0 : ZMod 2) = 1 := congrFun (congrArg ManifoldOrientation.sign h) default
    exact absurd this (by decide)
  · intro o
    have hval : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hval (o.sign default) with h | h
    · exact Or.inl (ManifoldOrientation.ext (funext fun x => by
        rw [Subsingleton.elim x default]; exact h))
    · exact Or.inr (ManifoldOrientation.ext (funext fun x => by
        rw [Subsingleton.elim x default]; exact h))

section Cardinality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The function recording, at each point of `M`, the sign difference (in `ZMod 2`)
between two manifold orientations. -/
def deltaFn (o₀ o : ManifoldOrientation I M) (z : M) : ZMod 2 := o.sign z - o₀.sign z

theorem deltaFn_isLocallyConstant (o₀ o : ManifoldOrientation I M) :
    IsLocallyConstant (deltaFn I o₀ o) := by
  rw [IsLocallyConstant.iff_continuous, continuous_iff_continuousAt]
  intro p
  refine ContinuousOn.continuousAt ?_
    ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  refine ((o.continuousOn_sign p).sub (o₀.continuousOn_sign p)).congr (fun z _ => ?_)
  simp only [deltaFn]
  ring

/-- The sign difference between two manifold orientations, as a `LocallyConstant` function
`M → ZMod 2`. -/
def deltaLC (o₀ o : ManifoldOrientation I M) : LocallyConstant M (ZMod 2) :=
  ⟨deltaFn I o₀ o, deltaFn_isLocallyConstant I o₀ o⟩

/-- Modify a manifold orientation by flipping its sign according to a locally constant
`ZMod 2`-valued function. -/
def twist (o₀ : ManifoldOrientation I M) (δ : LocallyConstant M (ZMod 2)) :
    ManifoldOrientation I M where
  sign z := δ z + o₀.sign z
  continuousOn_sign x := by
    simp only [add_assoc]
    exact δ.continuous.continuousOn.add (o₀.continuousOn_sign x)

/-- Relative to a fixed base orientation `o₀`, the manifold orientations are in bijection with
locally constant `ZMod 2`-valued functions on `M`. -/
noncomputable def manifoldOrientationEquivLocallyConstant (o₀ : ManifoldOrientation I M) :
    ManifoldOrientation I M ≃ LocallyConstant M (ZMod 2) where
  toFun o := deltaLC I o₀ o
  invFun δ := twist I o₀ δ
  left_inv o := by
    ext z
    change (o.sign z - o₀.sign z) + o₀.sign z = o.sign z
    ring
  right_inv δ := by
    ext z
    change (δ z + o₀.sign z) - o₀.sign z = δ z
    ring

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
