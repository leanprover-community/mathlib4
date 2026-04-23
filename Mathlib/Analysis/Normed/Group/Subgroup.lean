/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.FastInstance
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Subgroups of normed (semi)groups

In this file, we prove that subgroups of a normed (semi)group are also normed (semi)groups.

## Tags

normed group
-/

@[expose] public section


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
instance seminormedGroup : SeminormedGroup s :=
  fast_instance% SeminormedGroup.induced _ _ s.subtype

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
instance seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedCommGroup s :=
  fast_instance% SeminormedCommGroup.induced _ _ s.subtype

@[to_additive]
instance normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s :=
  fast_instance% NormedGroup.induced _ _ s.subtype Subtype.coe_injective

@[to_additive]
instance normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s :=
  fast_instance% NormedCommGroup.induced _ _ s.subtype Subtype.coe_injective

end Subgroup

/-! ### Subgroup classes of normed groups -/


namespace SubgroupClass

section SeminormedGroup

variable [SeminormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E] (s : S)

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed additive group is also a seminormed additive group,
with the restriction of the norm. -/]
instance (priority := 75) seminormedGroup : SeminormedGroup s :=
  fast_instance% SeminormedGroup.induced _ _ (SubgroupClass.subtype s)

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) /-- If `x` is an element of an additive subgroup `s` of a seminormed
additive group `E`, its norm in `s` is equal to its norm in `E`. -/]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

end SeminormedGroup

@[to_additive]
instance (priority := 75) seminormedCommGroup [SeminormedCommGroup E] {S : Type*} [SetLike S E]
    [SubgroupClass S E] (s : S) : SeminormedCommGroup s :=
  fast_instance% SeminormedCommGroup.induced _ _ (SubgroupClass.subtype s)

@[to_additive]
instance (priority := 75) normedGroup [NormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E]
    (s : S) : NormedGroup s :=
  fast_instance% NormedGroup.induced _ _ (SubgroupClass.subtype s) Subtype.coe_injective

@[to_additive]
instance (priority := 75) normedCommGroup [NormedCommGroup E] {S : Type*} [SetLike S E]
    [SubgroupClass S E] (s : S) : NormedCommGroup s :=
  fast_instance% NormedCommGroup.induced _ _ (SubgroupClass.subtype s) Subtype.coe_injective

end SubgroupClass
