/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Newell Jensen
-/
module

public import Mathlib.Init
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Constructor

/-!
# The `fconstructor` and `econstructor` tactics

The `fconstructor` and `econstructor` tactics are variants of the `constructor` tactic in Lean core,
except that
- `fconstructor` does not reorder goals
- `econstructor` adds only non-dependent premises as new goals.
-/

public meta section

open Lean Elab Tactic

/--
`fconstructor`, on a goal which is an inductive type, solves it by applying the first matching
constructor, creating new goals for all arguments to the constructor in the same order.
This is like `constructor` except the goals are not reordered.
-/
elab "fconstructor" : tactic => withMainContext do
  let mvarIds' ← (← getMainGoal).constructor {newGoals := .all}
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'

/--
`econstructor`, on a goal which is an inductive type, solves it by applying the first matching
constructor, creating new goals for non-dependent arguments to the constructor in the same order.
This is like `constructor` except only non-dependent arguments are shown as new goals.
-/
elab "econstructor" : tactic => withMainContext do
  let mvarIds' ← (← getMainGoal).constructor {newGoals := .nonDependentOnly}
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'
