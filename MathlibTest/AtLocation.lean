/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
import Mathlib.Util.AtLocation

/-! # Tests for `Location` traversal in `Mathlib.Util.AtLocation` -/

open Lean Elab Tactic Meta Mathlib.Tactic Parser.Tactic

-- the probe tactics deliberately change no goal state
set_option linter.unusedTactic false

/-- Run `withNondepPropLocation` and record which locations were visited. -/
elab "visit_nondep_prop" loc:(location)? : tactic => do
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let visited ← IO.mkRef (#[] : Array Name)
  withNondepPropLocation loc
    (fun fvarId => do visited.modify (·.push (← fvarId.getUserName)))
    (visited.modify (·.push `goal))
    (fun _ => throwError "no location visited")
  logInfo m!"visited: {(← visited.get)}"

/-- Fail at every location visited by `withNondepPropLocation`. -/
elab "visit_none" : tactic => do
  withNondepPropLocation .wildcard
    (fun _ => throwError "hyp refused")
    (throwError "target refused")
    (fun _ => throwError "no location visited")

-- wildcard visits the target first, and selected hypotheses in newest-first ordering. -/
/-- info: visited: [goal, _h, _f] -/
#guard_msgs in
example (_b : Bool) (_f : _b = true) (_g : Bool → Bool) (_h : _b = _b) : True := by
  visit_nondep_prop at *
  trivial

-- the wildcard skips `h1` Prop` hypothesis with a forward dependency -/
/-- info: visited: [goal, _h2] -/
#guard_msgs in
example (n m : Nat) (h1 : n = m) (v : Fin n) (P : Fin m → Prop) (_h2 : P (h1 ▸ v)) : True := by
  visit_nondep_prop at *
  trivial

-- explicitly listed hypotheses are not filtered
/-- info: visited: [_v] -/
#guard_msgs in
example (_v : Bool) : True := by
  visit_nondep_prop at _v
  trivial

-- explicit lists run the hypotheses first and the goal last
/-- info: visited: [_h, goal] -/
#guard_msgs in
example (b : Bool) (_h : b = b) : True := by
  visit_nondep_prop at _h ⊢
  trivial

-- failures of the real `atLocal`/`atTarget` are ignored under `*`, and when no location succeeds
-- `failed` is called
/-- error: no location visited -/
#guard_msgs in
example (h : True) : True := by
  visit_none

/-- Collect the types at each location visited by `mapNondepPropLocation`. -/
elab "collect_nondep_prop" loc:(location)? : tactic => do
  let loc := expandOptLocation (mkOptionalNode loc)
  let tys ← mapNondepPropLocation loc (fun fvarId => fvarId.getType) getMainTarget
  logInfo m!"collected: {tys}"

/-- info: collected: [True, _b = true] -/
#guard_msgs in
example (_b : Bool) (_f : _b = true) : True := by
  collect_nondep_prop at *
  trivial

/-- info: collected: [Bool, _b = true, True] -/
#guard_msgs in
example (_b : Bool) (_f : _b = true) : True := by
  collect_nondep_prop at _b _f ⊢
  trivial
