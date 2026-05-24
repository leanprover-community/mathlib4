/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Subgroups of normed (semi)groups

In this file, we prove that subgroups of a normed (semi)group are also normed (semi)groups.

## Tags

normed group
-/

public section


open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

/-! ### Subgroups of normed groups -/

variable {E : Type*}

namespace Subgroup

section SeminormedGroup

variable [NormPseudoMetric E] [Group E] [IsNormedGroup E] {s : Subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed group is also a seminormed group, with the restriction
of the norm. -/]
instance : IsNormedGroup s :=
  IsNormedGroup.induced _ _ s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive /-- If `x` is an element of a subgroup `s` of a seminormed group `E`,
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

/-- missing doc -/
@[to_additive /-- missing doc -/]
instance [NormMetric E] [Group E] [IsNormedGroup E] {s : Subgroup E} : NormMetric s :=
  fast_instance% NormMetric.induced _ _ s.subtype Subtype.coe_injective

end Subgroup

/-! ### Subgroup classes of normed groups -/


namespace SubgroupClass

section SeminormedGroup

variable [NormPseudoMetric E] [Group E] [IsNormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E] (s : S)

/-- missing doc -/
@[to_additive /-- missing doc -/]
instance (priority := 75) : NormPseudoMetric s :=
  fast_instance% NormPseudoMetric.induced _ _ (SubgroupClass.subtype s)

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed additive group is also a seminormed additive group,
with the restriction of the norm. -/]
instance (priority := 75) instIsNormedGroup : IsNormedGroup s :=
  IsNormedGroup.induced _ _ (SubgroupClass.subtype s)

set_option linter.unusedSectionVars false in
/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive /-- If `x` is an element of an additive subgroup `s` of a seminormed
additive group `E`, its norm in `s` is equal to its norm in `E`. -/]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

end SeminormedGroup

/-- missing doc -/
@[to_additive /-- missing doc -/]
instance (priority := 75) [NormMetric E] [Group E] [IsNormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E]
    (s : S) : NormMetric s :=
  fast_instance% NormMetric.induced _ _ (SubgroupClass.subtype s) Subtype.coe_injective

end SubgroupClass
