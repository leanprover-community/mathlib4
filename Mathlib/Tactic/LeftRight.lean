/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Lean

namespace Mathlib.Tactic.LeftRight
open Lean Meta Elab
open Tactic
def leftRightMeta (pickLeft: Bool) (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let name := if pickLeft then `left else `right
    mvarId.checkNotAssigned name
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        unless ival.ctors.length == 2 do
          throwTacticEx `constructor mvarId s!"{name} target applies for inductive types with exactly two constructors"
        let ctor := ival.ctors.get! (if pickLeft then 0 else 1)
        mvarId.apply (Lean.mkConst ctor us)

end LeftRight

open LeftRight

elab "left" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic (leftRightMeta true)

elab "right" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic (leftRightMeta false)
