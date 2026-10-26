/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Linearly ordered subgroups

## Main definitions

* `Subgroup.topOrderMonoidIso` : the order preserving isomorphism from the top subgroup
  to the group.

-/

public section

/-- The order preserving isomorphism from the top subgroup to the group. -/
@[expose]
noncomputable def Subgroup.topOrderMonoidIso (G : Type*) [Group G] [Preorder G] :
    (⊤ : Subgroup G) ≃*o G where
  __ := (Subgroup.topEquiv (G := G))
  map_le_map_iff' := by simp
