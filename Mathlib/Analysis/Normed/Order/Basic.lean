/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Analysis.NormedSpace.Basic

#align_import analysis.normed.order.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/


open Filter Set

open Topology

variable {α : Type*}

/-- A `NormedOrderedAddGroup` is an additive group that is both a `NormedAddCommGroup` and an
`OrderedAddCommGroup`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
class NormedOrderedAddGroup (α : Type*) extends OrderedAddCommGroup α, NormedAddCommGroup α
#align normed_ordered_add_group NormedOrderedAddGroup

/-- A `NormedOrderedGroup` is a group that is both a `NormedCommGroup` and an
`OrderedCommGroup`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive]
class NormedOrderedGroup (α : Type*) extends OrderedCommGroup α, NormedCommGroup α
#align normed_ordered_group NormedOrderedGroup

attribute [to_additive existing] NormedOrderedGroup.toNormedCommGroup

/-- A `NormedLinearOrderedAddGroup` is an additive group that is both a `NormedAddCommGroup`
and a `LinearOrderedAddCommGroup`. This class is necessary to avoid diamonds caused by both
classes carrying their own group structure. -/
class NormedLinearOrderedAddGroup (α : Type*) extends LinearOrderedAddCommGroup α,
  NormedOrderedAddGroup α
#align normed_linear_ordered_add_group NormedLinearOrderedAddGroup

/-- A `NormedLinearOrderedGroup` is a group that is both a `NormedCommGroup` and a
`LinearOrderedCommGroup`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive]
class NormedLinearOrderedGroup (α : Type*) extends LinearOrderedCommGroup α, NormedOrderedGroup α
#align normed_linear_ordered_group NormedLinearOrderedGroup

attribute [to_additive existing] NormedLinearOrderedGroup.toNormedOrderedGroup

/-- A `NormedLinearOrderedField` is a field that is both a `NormedField` and a
    `LinearOrderedField`. This class is necessary to avoid diamonds. -/
class NormedLinearOrderedField (α : Type*) extends LinearOrderedField α, NormedField α
#align normed_linear_ordered_field NormedLinearOrderedField

attribute [instance 100] NormedOrderedGroup.toNormedCommGroup
#align normed_ordered_group.to_normed_comm_group NormedOrderedGroup.toNormedCommGroup
#align normed_ordered_add_group.to_normed_add_comm_group NormedOrderedAddGroup.toNormedAddCommGroup

attribute [instance 100] NormedLinearOrderedGroup.toNormedOrderedGroup
#align normed_linear_ordered_group.to_normed_ordered_group NormedLinearOrderedGroup.toNormedOrderedGroup
#align normed_linear_ordered_add_group.to_normed_ordered_add_group NormedLinearOrderedAddGroup.toNormedOrderedAddGroup

attribute [instance 100] NormedLinearOrderedField.toNormedField
#align normed_linear_ordered_field.to_normed_field NormedLinearOrderedField.toNormedField

instance Rat.normedLinearOrderedField : NormedLinearOrderedField ℚ where
  toLinearOrderedField := inferInstance
  __ : NormedField _ := inferInstance

  -- ⟨dist_eq_norm, norm_mul⟩

noncomputable instance Real.normedLinearOrderedField : NormedLinearOrderedField ℝ where
  toLinearOrderedField := inferInstance
  __ : NormedField _ := inferInstance

@[to_additive]
instance OrderDual.normedOrderedGroup [NormedOrderedGroup α] : NormedOrderedGroup αᵒᵈ :=
  { @NormedOrderedGroup.toNormedCommGroup α _, OrderDual.orderedCommGroup with }

@[to_additive]
instance OrderDual.normedLinearOrderedGroup [NormedLinearOrderedGroup α] :
    NormedLinearOrderedGroup αᵒᵈ :=
  { OrderDual.normedOrderedGroup, OrderDual.instLinearOrder _ with }

instance Additive.normedOrderedAddGroup [NormedOrderedGroup α] :
    NormedOrderedAddGroup (Additive α) :=
  { Additive.normedAddCommGroup, Additive.orderedAddCommGroup with }

instance Multiplicative.normedOrderedGroup [NormedOrderedAddGroup α] :
    NormedOrderedGroup (Multiplicative α) :=
  { Multiplicative.normedCommGroup, Multiplicative.orderedCommGroup with }

instance Additive.normedLinearOrderedAddGroup [NormedLinearOrderedGroup α] :
    NormedLinearOrderedAddGroup (Additive α) :=
  { Additive.normedAddCommGroup, Additive.linearOrderedAddCommGroup with }

instance Multiplicative.normedlinearOrderedGroup [NormedLinearOrderedAddGroup α] :
    NormedLinearOrderedGroup (Multiplicative α) :=
  { Multiplicative.normedCommGroup, Multiplicative.linearOrderedCommGroup with }
