/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Subgroups of normed (semi)groups

In this file, we prove that subgroups of a normed (semi)group are also normed (semi)groups.

## Tags

normed group
-/


open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

/-! ### Subgroups of normed groups -/

variable {E : Type*}

namespace Subgroup

section SeminormedGroup

variable [SeminormedGroup E] {s : Subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed group is also a seminormed group, with the restriction
of the norm. -/]
instance seminormedGroup : WithSeminormedGroup s :=
  SeminormedGroup.induced _ _ s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) /-- If `x` is an element of a subgroup `s` of a seminormed group `E`,
its norm in `s` is equal to its norm in `E`. -/]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `Subgroup.coe_norm` for use by `norm_cast`. -/
@[to_additive (attr := norm_cast) /-- If `x` is an element of a subgroup `s` of a seminormed group
`E`, its norm in `s` is equal to its norm in `E`.

This is a reversed version of the `simp` lemma `AddSubgroup.coe_norm` for use by `norm_cast`. -/]
theorem norm_coe {s : Subgroup E} (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

end SeminormedGroup

@[to_additive]
instance normedGroup [NormedGroup E] {s : Subgroup E} : WithNormedGroup s :=
  NormedGroup.induced _ _ s.subtype Subtype.coe_injective

end Subgroup

/-! ### Subgroup classes of normed groups -/


namespace SubgroupClass

section SeminormedGroup

variable [SeminormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E] (s : S)

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed additive group is also a seminormed additive group,
with the restriction of the norm. -/]
instance (priority := 75) seminormedGroup : WithSeminormedGroup s :=
  SeminormedGroup.induced _ _ (SubgroupClass.subtype s)

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) /-- If `x` is an element of an additive subgroup `s` of a seminormed
additive group `E`, its norm in `s` is equal to its norm in `E`. -/]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

end SeminormedGroup

@[to_additive]
instance (priority := 75) normedGroup [NormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E]
    (s : S) : WithNormedGroup s :=
  NormedGroup.induced _ _ (SubgroupClass.subtype s) Subtype.coe_injective

end SubgroupClass
