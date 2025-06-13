/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Connected.PathConnected

/-!
# Segment between 2 points as a bundled path

In this file we define `Path.segment a b : Path a b`
to be the path going from `a` to `b` along the straight segment with constant velocity `b - a`.

We also prove basic properties of this construction,
then use it to show that a nonempty convex set is path connected.
In particular, a topological vector space over `ℝ` is path connected.
-/

open Set
open scoped Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

namespace Path

/-- The path from `a` to `b` going along a straight line segment -/
@[simps]
protected def segment (a b : E) : Path a b where
  toFun t := AffineMap.lineMap a b (t : ℝ)
  source' := by simp
  target' := by simp

@[simp]
theorem range_segment (a b : E) : Set.range (Path.segment a b) = [a -[ℝ] b] := by
  rw [segment_eq_image_lineMap, image_eq_range]
  simp only [← segment_apply]

@[simp]
protected theorem segment_same (a : E) : Path.segment a a = .refl a := by ext; simp

@[simp]
protected theorem segment_symm (a b : E) : (Path.segment a b).symm = .segment b a := by
  ext; simp [AffineMap.lineMap_apply_one_sub]

@[simp]
theorem segment_add_segment (a b c d : E) :
    (Path.segment a b).add (.segment c d) = .segment (a + c) (b + d) := by
  ext
  simp [AffineMap.lineMap_apply_module, add_add_add_comm]

@[simp]
theorem cast_segment {a b c d : E} (hac : c = a) (hbd : d = b) :
    (Path.segment a b).cast hac hbd = .segment c d := by
  subst_vars; rfl

end Path

theorem JoinedIn.of_segment_subset {x y : E} {s : Set E} (h : [x -[ℝ] y] ⊆ s) : JoinedIn s x y := by
  use .segment x y
  rwa [← range_subset_iff, Path.range_segment]

protected theorem StarConvex.isPathConnected {s : Set E} {a : E} (h : StarConvex ℝ a s)
    (ha : a ∈ s) : IsPathConnected s :=
  ⟨a, ha, fun _y hy ↦ .of_segment_subset <| h.segment_subset hy⟩

/-- A nonempty convex set is path connected. -/
protected theorem Convex.isPathConnected {s : Set E} (hconv : Convex ℝ s) (hne : s.Nonempty) :
    IsPathConnected s :=
  let ⟨_a, ha⟩ := hne; (hconv ha).isPathConnected ha

/-- A nonempty convex set is connected. -/
protected theorem Convex.isConnected {s : Set E} (h : Convex ℝ s) (hne : s.Nonempty) :
    IsConnected s :=
  (h.isPathConnected hne).isConnected

/-- A convex set is preconnected. -/
protected theorem Convex.isPreconnected {s : Set E} (h : Convex ℝ s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected

/-- A subspace in a topological vector space over `ℝ` is path connected. -/
theorem Submodule.isPathConnected (s : Submodule ℝ E) : IsPathConnected (s : Set E) :=
  s.convex.isPathConnected s.nonempty

/-- Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected theorem IsTopologicalAddGroup.pathConnectedSpace : PathConnectedSpace E :=
  pathConnectedSpace_iff_univ.mpr <| convex_univ.isPathConnected ⟨(0 : E), trivial⟩

/-- Given two complementary subspaces `p` and `q` in `E`, if the complement of `{0}`
is path connected in `p` then the complement of `q` is path connected in `E`. -/
theorem isPathConnected_compl_of_isPathConnected_compl_zero {p q : Submodule ℝ E}
    (hpq : IsCompl p q) (hpc : IsPathConnected ({0}ᶜ : Set p)) : IsPathConnected (qᶜ : Set E) := by
  convert (hpc.image continuous_subtype_val).add q.isPathConnected using 1
  trans Submodule.prodEquivOfIsCompl p q hpq '' ({0}ᶜ ×ˢ univ)
  · rw [prod_univ, LinearEquiv.image_eq_preimage]
    ext
    simp
  · ext
    simp [mem_add, and_assoc]
