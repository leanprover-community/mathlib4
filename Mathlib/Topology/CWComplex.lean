/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# CW-complexes

This file defines (relative) CW-complexes.

## Main definitions

* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
  `sk i` (called the $(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an
  arbitrary topological space, and each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from
  `sk n` (i.e., the $(n-1)$-skeleton) by attaching `n`-disks.

* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty.

## References

* [R. Fritsch and R. Piccinini, *Cellular Structures in Topology*][fritsch-piccinini1990]
* The definition of CW-complexes follows David Wärn's suggestion on
  [Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Do.20we.20have.20CW.20complexes.3F/near/231769080).
-/

open CategoryTheory TopCat

universe u

namespace RelativeCWComplex

/-- The inclusion map from the `n`-sphere to the `(n + 1)`-disk. (For `n = -1`, this
involves the empty space `𝕊 (-1)`. This is the reason why `sphere` takes `n : ℤ` as
an input rather than `n : ℕ`.) -/
def sphereInclusion (n : ℤ) : 𝕊 n ⟶ 𝔻 (n + 1) where
  toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
  continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
    rw [isOpen_induced_iff, ← hst, ← hrs]
    tauto⟩

/-- A type witnessing that `X'` is obtained from `X` by attaching generalized cells `f : S ⟶ D` -/
structure AttachGeneralizedCells {S D : TopCat.{u}} (f : S ⟶ D) (X X' : TopCat.{u}) where
  /-- The index type over the generalized cells -/
  cells : Type u
  /-- An attaching map for each generalized cell -/
  attachMaps : cells → (S ⟶ X)
  /-- `X'` is the pushout of `∐ S ⟶ X` and `∐ S ⟶ ∐ D`. -/
  iso_pushout : X' ≅ Limits.pushout (Limits.Sigma.desc attachMaps) (Limits.Sigma.map fun _ ↦ f)

/-- A type witnessing that `X'` is obtained from `X` by attaching `(n + 1)`-disks -/
def AttachCells (n : ℤ) := AttachGeneralizedCells (sphereInclusion n)

end RelativeCWComplex

/-- A relative CW-complex consists of an expanding sequence of subspaces `sk i` (called the
$(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an arbitrary topological
space, and each `sk (n + 1)` (i.e., the `n`-skeleton) is obtained from `sk n` (i.e., the
$(n-1)$-skeleton) by attaching `n`-disks. -/
structure RelativeCWComplex where
  /-- The skeletons. Note: `sk i` is usually called the $(i-1)$-skeleton in the math literature. -/
  sk : ℕ → TopCat.{u}
  /-- Each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from `sk n`
  (i.e., the $(n-1)$-skeleton) by attaching `n`-disks. -/
  attachCells (n : ℕ) : RelativeCWComplex.AttachCells ((n : ℤ) - 1) (sk n) (sk (n + 1))

/-- A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty. -/
structure CWComplex extends RelativeCWComplex.{u} where
  /-- `sk 0` (i.e., the $(-1)$-skeleton) is empty. -/
  isEmpty_sk_zero : IsEmpty (sk 0)

namespace RelativeCWComplex

noncomputable section Topology

/-- The inclusion map from `X` to `X'`, when `X'` is obtained from `X`
by attaching generalized cells `f : S ⟶ D`. -/
def AttachGeneralizedCells.inclusion {S D : TopCat.{u}} {f : S ⟶ D} {X X' : TopCat.{u}}
    (att : AttachGeneralizedCells f X X') : X ⟶ X' :=
  Limits.pushout.inl _ _ ≫ att.iso_pushout.inv

/-- The inclusion map from `sk n` (i.e., the $(n-1)$-skeleton) to `sk (n + 1)` (i.e., the
$n$-skeleton) of a relative CW-complex -/
def skInclusion (X : RelativeCWComplex.{u}) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  (X.attachCells n).inclusion

/-- The topology on a relative CW-complex -/
def toTopCat (X : RelativeCWComplex.{u}) : TopCat.{u} :=
  Limits.colimit (Functor.ofSequence X.skInclusion)

instance : Coe RelativeCWComplex TopCat where coe X := toTopCat X

end Topology

end RelativeCWComplex
