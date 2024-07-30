/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Newell Jensen
-/
import Lean.Elab.SyntheticMVars
import Lean.Meta.Tactic.Constructor

/-!
# The `fconstructor` and `econstructor` tactics

The `fconstructor` and `econstructor` tactics are variants of the `constructor` tactic in Lean core,
except that
- `fconstructor` does not reorder goals
- `econstructor` adds only non-dependent premises as new goals.
-/

open Lean Elab Tactic

/--
`fconstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except that it does not reorder goals.
-/
elab "fconstructor" : tactic => withMainContext do
  let mvarIds' ← (← getMainGoal).constructor {newGoals := .all}
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'

/--
`econstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except only non-dependent premises are added as new goals.
-/
elab "econstructor" : tactic => withMainContext do
  let mvarIds' ← (← getMainGoal).constructor {newGoals := .nonDependentOnly}
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'
