/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Conj
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

variable (X)

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid. -/
def FundamentalGroup (x : X) :=
  End (FundamentalGroupoid.mk x)

instance (x : X) : Group (FundamentalGroup X x) := inferInstanceAs (Group (End _))

instance (x : X) : Inhabited (FundamentalGroup X x) := inferInstanceAs (Inhabited (End _))

variable {X}

namespace FundamentalGroup

/-- Get an isomorphism between the fundamental groups at two points given a path -/
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

variable (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

/-- An element of the fundamental group as an arrow in the fundamental groupoid. -/
abbrev toArrow {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p

/-- An element of the fundamental group as a quotient of homotopic paths. -/
abbrev toPath {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p

/-- An element of the fundamental group, constructed from an arrow in the fundamental groupoid. -/
abbrev fromArrow {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x :=
  p

/-- An element of the fundamental group, constructed from a quotient of homotopic paths. -/
abbrev fromPath {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p

/-- The homomorphism between fundamental groups induced by a continuous map. -/
@[simps!] def map (f : C(X, Y)) (x : X) : FundamentalGroup X x →* FundamentalGroup Y (f x) :=
  (FundamentalGroupoid.map f).mapEnd _

variable (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- The homomorphism from π₁(X, x) to π₁(Y, y) induced by a continuous map `f` with `f x = y`. -/
def mapOfEq : FundamentalGroup X x →* FundamentalGroup Y y :=
  (eqToIso <| congr_arg FundamentalGroupoid.mk h).conj.toMonoidHom.comp (map f x)

theorem mapOfEq_apply (p : Path x x) :
    mapOfEq f h (fromPath <| .mk p) = fromPath (.mk <| (p.map f.continuous).cast h.symm h.symm) :=
  FundamentalGroupoid.conj_eqToHom ..

end FundamentalGroup
