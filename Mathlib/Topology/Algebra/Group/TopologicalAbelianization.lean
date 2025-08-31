/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.GroupTheory.Abelianization
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Group.Basic

/-!
# The topological abelianization of a group.

This file defines the topological abelianization of a topological group.

## Main definitions

* `TopologicalAbelianization`: defines the topological abelianization of a group `G` as the quotient
  of `G` by the topological closure of its commutator subgroup..

## Main results
- `instNormalCommutatorClosure` : the topological closure of the commutator of a topological group
  `G` is a normal subgroup.

## Tags
group, topological abelianization

-/

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instNormalCommutatorClosure : (commutator G).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator G)

/-- The topological abelianization of `absoluteGaloisGroup`, that is, the quotient of
  `absoluteGaloisGroup` by the topological closure of its commutator subgroup. -/
abbrev TopologicalAbelianization := G ⧸ Subgroup.topologicalClosure (commutator G)

local notation "G_ab" => TopologicalAbelianization

namespace TopologicalAbelianization

instance commGroup : CommGroup (G_ab G) where
  mul_comm := fun x y =>
    Quotient.inductionOn₂' x y fun a b =>
      Quotient.sound' <|
        QuotientGroup.leftRel_apply.mpr <| by
          have h : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
          rw [h]
          exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
  __ : Group (G_ab G) := inferInstance

end TopologicalAbelianization
