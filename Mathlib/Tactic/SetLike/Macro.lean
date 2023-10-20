/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Tactic.SetLike.Init

/-!
# SetLike

We define the `set_like` tactic as an `aesop` wrapper.
-/

/-- The `set_like` attribute used to tag statements concerning `SetLike` objects for the `set_like`
tactic.  This registers `aesop` rules in the `SetLike` rule set as `safe apply` rules. Passing a
positive integer to the `set_like` attribute (as in `@[aesop safe 10 apply (rule_sets [SetLike])]`) can be used to adjust the
`aesop` penalty.

This attribute should be placed on lemmas like `add_mem` or `zero_mem` which apply to subobject
classes. It can also be used for lemmas pertaining to individual subobjects, like
`ConvexCone.smul_mem`. Note: for lemmas pertaining to subobject closures (e.g., `Subgroup.closure`),
it is import to mark the `Subgroup.mem_closure_of_mem` lemma with a higher penalty so that these
lemmas are not applied first.

For example, in order to show `x - y ∈ Subgroup.closure s` it is generally the right approach to
first apply `sub_mem` to gets goals of `x ∈ Subgroup.closure s` and `y ∈ Subgroup.closure s`, and
then apply `Subgroup.mem_closure_of_mem` to each to get goals of `x ∈ s` and `y ∈ s`. If this lemma
were instead applied first, then the goal would be `x - y ∈ s`, which is likely not solvable in many
cases in practice. -/
syntax "set_like" (num)? : attr

macro_rules
| `(attr|set_like) => `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `SetLike):ident]))
| `(attr|set_like $n:num) =>
    `(attr|aesop safe apply $n:num (rule_sets [$(Lean.mkIdent `SetLike):ident]))

/-- The tactic `set_like` solves goals of the form `expr ∈ S`, where `expr` is some mathematical
expression and `S` is a subobject in some `SetLike` class, by applying lemmas tagged with the
`set_like` user attribute. -/
macro "set_like" : tactic =>
  `(tactic| aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `SetLike):ident]))

/-- The tactic `set_like` solves goals of the form `expr ∈ S`, where `expr` is some mathematical
expressona and `S` is a subobject in some `SetLike` class, by applying lemmas tagged with the
`set_like` user attribute. -/
macro "set_like?" : tactic =>
  `(tactic| aesop? (options := { terminal := true })
    (rule_sets [$(Lean.mkIdent `SetLike):ident]))
