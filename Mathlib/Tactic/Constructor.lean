/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Lean.Elab.Command
import Lean.Meta.Tactic.Constructor

open Lean Meta Elab Tactic

/--
`fconstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except that it does not reorder goals.
-/
elab "fconstructor " : tactic => withMainContext do
  let mvarIds' ←
    Meta.constructor (cfg := {newGoals := .all}) (← getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'
