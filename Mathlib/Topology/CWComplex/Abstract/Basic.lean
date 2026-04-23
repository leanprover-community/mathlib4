/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young, Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# CW-complexes

This file defines (relative) CW-complexes using a categorical approach.

## Main definitions

* `RelativeCWComplex`: A relative CW-complex is the colimit of an expanding sequence of subspaces
  `sk i` (called the $(i-1)$-skeleton) for `i ≥ 0`, where `sk 0` (i.e., the $(-1)$-skeleton) is an
  arbitrary topological space, and each `sk (n + 1)` (i.e., the $n$-skeleton) is obtained from
  `sk n` (i.e., the $(n-1)$-skeleton) by attaching `n`-disks.

* `CWComplex`: A CW-complex is a relative CW-complex whose `sk 0` (i.e., $(-1)$-skeleton) is empty.

## Implementation Notes

This file provides a categorical approach to CW complexes,
defining them via colimits and transfinite compositions.
For a classical approach that defines CW complexes via explicit cells and attaching maps,
see `Mathlib/Topology/CWComplex/Classical/Basic.lean`.
The two approaches are equivalent but serve different purposes:
* This approach is more suitable for categorical arguments and generalizations
* The classical approach is more convenient for concrete geometric arguments

## References

* [R. Fritsch and R. Piccinini, *Cellular Structures in Topology*][fritsch-piccinini1990]

## TODO

* Prove the equivalence between this categorical approach and the classical approach in
  `Mathlib/Topology/CWComplex/Classical/Basic.lean`.
  Currently there is no way to move between the two definitions.
-/

@[expose] public section

open TopCat


universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace TopCat

namespace RelativeCWComplex

/-- For each `n : ℕ`, this is the family of morphisms which sends the unique
element of `Unit` to `diskBoundaryInclusion n : ∂𝔻 n ⟶ 𝔻 n`. -/
@[nolint unusedArguments]
abbrev basicCell (n : ℕ) (_ : Unit) : ∂𝔻 n ⟶ 𝔻 n := diskBoundaryInclusion n

end RelativeCWComplex

open RelativeCWComplex in
/-- A relative CW-complex is a morphism `f : X ⟶ Y` equipped with data expressing
that `Y` identifies to the colimit of a functor `F : ℕ ⥤ TopCat` with that
`F.obj 0 ≅ X` and for any `n : ℕ`, `F.obj (n + 1)` is obtained from `F.obj n`
by attaching `n`-disks. -/
abbrev RelativeCWComplex {X Y : TopCat.{u}} (f : X ⟶ Y) := RelativeCellComplex.{u} basicCell f

/-- A CW-complex is a topological space such that `⊥_ _ ⟶ X` is a relative CW-complex. -/
abbrev CWComplex (X : TopCat.{u}) := RelativeCWComplex (initial.to X)

end TopCat
