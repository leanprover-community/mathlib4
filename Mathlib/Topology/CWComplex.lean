/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# CW-complexes

This file defines (relative) CW-complexes.

## Main definitions

* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
`sk i` (called the `(i-1)`-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the `(-1)`-skeleton) is an
arbitrary topological space, and each `sk (n+1)` (i.e., the `n`-skeleton) is obtained from `sk n`
(i.e., the `(n-1)`-skeleton) by attaching `n`-disks.

* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., `(-1)`-skeleton) is empty.

## References

The definition of CW-complexes follows David Wärn's suggestion at
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080
-/

open CategoryTheory TopCat

universe u

namespace RelativeCWComplex

/-- The inclusion map from the `n`-sphere to the `(n+1)`-disk -/
def sphereInclusion (n : ℤ) : 𝕊 n ⟶ 𝔻 (n + 1) where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst, ← hrs]
    tauto⟩

variable {S D : TopCat.{u}} (f : S ⟶ D)

/-- Given the inclusion map `f : S ⟶ D` for one generalized cell, we construct the inclusion map
from the disjoint union of `S` (boundary of generalized cells) to the disjoint union of `D`
(generalized cells), where both of the disjoint unions are indexed by `cells`. -/
def generalizedSigmaSphereInclusion (cells : Type) :
    TopCat.of (Σ (_ : cells), S) ⟶ TopCat.of (Σ (_ : cells), D) where
  toFun := Sigma.map id fun _ x ↦ f.toFun x
  continuous_toFun := Continuous.sigma_map fun _ ↦ f.continuous_toFun

/-- Given an attaching map for each `S` (boundary of a generalized cell), we construct
the attaching map for the disjoint union of all the `S`. -/
def generalizedSigmaAttachMap (S X : TopCat.{u}) (cells : Type) (attach_maps : cells → C(S, X)) :
    TopCat.of (Σ (_ : cells), S) ⟶ X where
  toFun := fun ⟨i, x⟩ ↦ attach_maps i x
  continuous_toFun := continuous_sigma fun i ↦ (attach_maps i).continuous_toFun

/-- A type witnessing that `X'` is obtained from `X` by attaching generalized cells `f : S ⟶ D`. -/
structure AttachGeneralizedCells (X X' : TopCat.{u}) where
  /-- The index type over the generalized `(n+1)`-cells -/
  cells : Type
  /-- For each generalized `(n+1)`-cell, we have an attaching map from its boundary to `X`. -/
  attach_maps : cells → C(S, X)
  /-- `X'` is the pushout obtained from `X` along `sigmaAttachMap`. -/
  iso_pushout : X' ≅ Limits.pushout (generalizedSigmaSphereInclusion f cells)
    (generalizedSigmaAttachMap S X cells attach_maps)

/-- The inclusion map from the disjoint union of `n`-spheres to the disjoint union of `(n+1)`-disks,
where both of the disjoint unions are indexed by `cells` -/
noncomputable def sigmaSphereInclusion (n : ℤ) :=
  generalizedSigmaSphereInclusion (sphereInclusion n)

/-- Given an attaching map for each `n`-sphere, we construct the attaching map for the disjoint
union of the `n`-spheres. -/
def sigmaAttachMap (n : ℤ) := generalizedSigmaAttachMap (sphere n)

/-- A type witnessing that `X'` is obtained from `X` by attaching `(n+1)`-disks -/
def AttachCells (n : ℤ) := AttachGeneralizedCells (sphereInclusion n)

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
  attach_cells (n : ℕ) : RelativeCWComplex.AttachCells (n - 1) (sk n) (sk (n + 1))

/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., `(-1)`-skeleton) is empty. -/
structure CWComplex extends RelativeCWComplex.{u} where
  /-- `sk 0` (i.e., the `(-1)`-skeleton) is empty. -/
  isEmpty_sk_zero : IsEmpty (sk 0)

namespace RelativeCWComplex

noncomputable section Topology

/-- The inclusion map from `X` to `X'`, given that `X'` is obtained from `X` by attaching
`(n+1)`-disks -/
def AttachCells.inclusion (X X' : TopCat.{u}) (n : ℤ) (att : AttachCells n X X') : X ⟶ X' :=
  @Limits.pushout.inr TopCat _ _ _ X (sigmaSphereInclusion n att.cells)
    (sigmaAttachMap n X att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

/-- The inclusion map from `sk n` (i.e., the `(n-1)`-skeleton) to `sk (n+1)` (i.e., the
`n`-skeleton) of a relative CW-complex -/
def inclusion (X : RelativeCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  RelativeCWComplex.AttachCells.inclusion (X.sk n) (X.sk (n + 1)) (n - 1) (X.attach_cells n)

/-- The topology on a relative CW-complex -/
def toTopCat (X : RelativeCWComplex.{u}) : TopCat.{u} :=
  Limits.colimit <| Functor.ofSequence <| inclusion X

instance : Coe RelativeCWComplex TopCat where coe X := toTopCat X

end Topology

end RelativeCWComplex
