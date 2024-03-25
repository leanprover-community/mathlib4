/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

#align_import algebraic_topology.fundamental_groupoid.fundamental_group from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid. -/
def FundamentalGroup (X : Type u) [TopologicalSpace X] (x : X) :=
  @Aut (FundamentalGroupoid X) _ ⟨x⟩
#align fundamental_group FundamentalGroup

instance (X : Type u) [TopologicalSpace X] (x : X) : Group (FundamentalGroup X x) := by
  dsimp only [FundamentalGroup]
  infer_instance

instance (X : Type u) [TopologicalSpace X] (x : X) : Inhabited (FundamentalGroup X x) := by
  dsimp only [FundamentalGroup]
  infer_instance

namespace FundamentalGroup

attribute [local instance] Path.Homotopic.setoid

-- Porting note: removed this attribute
--attribute [local reducible] FundamentalGroupoid

/-- Get an isomorphism between the fundamental groups at two points given a path -/
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  Aut.autMulEquivOfIso (asIso ⟦p⟧)
#align fundamental_group.fundamental_group_mul_equiv_of_path FundamentalGroup.fundamentalGroupMulEquivOfPath

variable (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)
#align fundamental_group.fundamental_group_mul_equiv_of_path_connected FundamentalGroup.fundamentalGroupMulEquivOfPathConnected

/-- An element of the fundamental group as an arrow in the fundamental groupoid. -/
abbrev toArrow {X : TopCat} {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p.hom
#align fundamental_group.to_arrow FundamentalGroup.toArrow

/-- An element of the fundamental group as a quotient of homotopic paths. -/
abbrev toPath {X : TopCat} {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p
#align fundamental_group.to_path FundamentalGroup.toPath

/-- An element of the fundamental group, constructed from an arrow in the fundamental groupoid. -/
abbrev fromArrow {X : TopCat} {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x where
  hom := p
  inv := CategoryTheory.Groupoid.inv p
#align fundamental_group.from_arrow FundamentalGroup.fromArrow

/-- An element of the fundamental group, constructed from a quotient of homotopic paths. -/
abbrev fromPath {X : TopCat} {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p
#align fundamental_group.from_path FundamentalGroup.fromPath

end FundamentalGroup
