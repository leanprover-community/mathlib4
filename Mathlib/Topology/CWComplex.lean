/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Relative CW-complexes

In this file we define a relative CW-complex as the colimit of an expanding sequence of subspaces
`sk i` (called the `(i-1)`-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the `(-1)`-skeleton) is an
arbitrary topological space, and each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n`
(i.e., the `(n-1)`-skeleton) by attaching `n`-disks.

## References
The definition of CW complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

open CategoryTheory

universe u

namespace RelativeCWComplex

/-- The `n`-dimensional sphere is the set of points in ℝⁿ⁺¹ whose norm equals `1`, endowed with the
subspace topology. -/
noncomputable def sphere (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| Int.toNat <| n + 1) 1

/-- The `n`-dimensional closed disk is the set of points in ℝⁿ whose norm is at most `1`, endowed
with the subspace topology. -/
noncomputable def disk (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| Int.toNat n) 1

/-- `𝕊 n` denotes the `n`-dimensional sphere. -/
scoped notation "𝕊 "n => sphere n

/-- `𝔻 n` denotes the `n`-dimensional closed disk. -/
scoped notation "𝔻 "n => disk n

/-- The inclusion map from the `n`-sphere to the `(n+1)`-disk -/
def sphereInclusion (n : ℤ) : (𝕊 n) ⟶ (𝔻 n + 1) where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrt⟩, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst, ← hrt]
    tauto⟩

variable {S D : ℤ → TopCat.{u}} (f : ∀ n, S n ⟶ D (n + 1))

/-- The inclusion map from the disjoint union of `S n` (boundary of generalized `(n+1)`-cells) to
the disjoint union of `D (n + 1)` (generalized `(n+1)`-cells) where both of the disjoint unions are
indexed by `cells` -/
def generalizedSigmaSphereInclusion (n : ℤ) (cells : Type) :
    TopCat.of (Σ (_ : cells), S n) ⟶ TopCat.of (Σ (_ : cells), D (n + 1)) where
  toFun := Sigma.map id fun _ x ↦ (f n).toFun x
  continuous_toFun := Continuous.sigma_map fun _ ↦ (f n).continuous_toFun

/-- Given an attaching map for each `S n` (boundary of the generalized `(n+1)`-cell), we construct
the attaching map for the disjoint union of all the `S n`. -/
def generalizedSigmaAttachMap (X : TopCat.{u}) (n : ℤ) (cells : Type)
    (attach_maps : cells → C(S n, X)) : TopCat.of (Σ (_ : cells), S n) ⟶ X where
  toFun := fun ⟨i, x⟩ ↦ attach_maps i x
  continuous_toFun := continuous_sigma fun i ↦ (attach_maps i).continuous_toFun

/-- A type witnessing that `X'` is obtained from `X` by attaching generalized `(n+1)`-cells -/
structure AttachGeneralizedCells (X X' : TopCat.{u}) (n : ℤ) where
  /-- The index type over the `(n+1)`-disks -/
  cells : Type
  /-- For each `(n+1)`-disk, we have an attaching map from its boundary, namely an `n`-sphere,
  to `X`. -/
  attach_maps : cells → C(S n, X)
  /-- `X'` is the pushout obtained from `X` along `sigmaAttachMap`. -/
  iso_pushout : X' ≅ Limits.pushout (generalizedSigmaSphereInclusion f n cells)
    (generalizedSigmaAttachMap X n cells attach_maps)

/-- The inclusion map from the disjoint union of `n`-spheres to the disjoint union of `(n+1)`-disks,
where both of the disjoint unions are indexed by `cells` -/
noncomputable abbrev sigmaSphereInclusion := generalizedSigmaSphereInclusion sphereInclusion

/-- Given an attaching map for each `n`-sphere, we construct the attaching map for the disjoint
union of the `n`-spheres. -/
abbrev sigmaAttachMap := @generalizedSigmaAttachMap sphere

/-- A type witnessing that `X'` is obtained from `X` by attaching `(n+1)`-disks -/
abbrev AttachCells := AttachGeneralizedCells sphereInclusion

/-- The inclusion map from `X` to `X'`, given that `X'` is obtained from `X` by attaching
`(n+1)`-disks -/
noncomputable def AttachCells.inclusion (X X' : TopCat.{u}) (n : ℤ)
    (att : AttachCells X X' n) : X ⟶ X' :=
  @Limits.pushout.inr TopCat _ _ _ X
    (sigmaSphereInclusion n att.cells)
    (sigmaAttachMap X n att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

end RelativeCWComplex

/-- A relative CW-complex contains an expanding sequence of subspaces `sk i` (called the
`(i-1)`-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the `(-1)`-skeleton) is an arbitrary topological
space, and each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
`(n-1)`-skeleton) by attaching `n`-disks. -/
structure RelativeCWComplex where
  /-- The skeletons. Note: `sk i` is usually called the `(i-1)`-skeleton in the math literature. -/
  sk : ℕ → TopCat.{u}
  /-- Each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
  `(n-1)`-skeleton) by attaching `n`-disks. -/
  attach_cells : (n : ℕ) → RelativeCWComplex.AttachCells (sk n) (sk (n + 1)) (n - 1)

/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., `(-1)`-skeleton) is empty. -/
structure CWComplex extends RelativeCWComplex.{u} where
  /-- `sk 0` (i.e., the `(-1)`-skeleton) is empty. -/
  sk_zero_empty : sk 0 = TopCat.of (ULift Empty)

namespace RelativeCWComplex

noncomputable section

/-- The inclusion map from `sk n` (i.e., the `(n-1)`-skeleton) to `sk (n+1)` (i.e., the
`n`-skeleton) of a relative CW-complex -/
def inclusion (X : RelativeCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  RelativeCWComplex.AttachCells.inclusion (X.sk n) (X.sk (n + 1)) (n - 1) (X.attach_cells n)

/-- The topology on a relative CW-complex -/
def toTopCat (X : RelativeCWComplex.{u}) : TopCat.{u} :=
  Limits.colimit <| Functor.ofSequence <| inclusion X

instance : Coe RelativeCWComplex TopCat where coe X := toTopCat X

end

end RelativeCWComplex
