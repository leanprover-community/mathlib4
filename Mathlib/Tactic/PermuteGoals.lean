/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arthur Paulino, Mario Carneiro
-/

import Lean
import Mathlib.Data.List.Defs

namespace Mathlib.Tactic

open Lean Elab Elab.Tactic

/--
`rotate_goals` moves the first goal to the back. `rotate_goals n` does this `n` times.

`rotate_goals -` moves the last goal to the front. `rotate_goals -n` does this `n` times.

See also `Tactic.pick_goal`, which moves the `n`-th goal to the front.
-/
syntax (name := rotate_goals) "rotate_goals " "-"? (num)? : tactic
elab_rules : tactic
  | `(tactic|rotate_goals)     => setGoals $ (← getGoals).rotateLeft 1
  | `(tactic|rotate_goals -)   => setGoals $ (← getGoals).rotateRight 1
  | `(tactic|rotate_goals $n)  => setGoals $ (← getGoals).rotateLeft n.toNat
  | `(tactic|rotate_goals -$n) => setGoals $ (← getGoals).rotateRight n.toNat
  | _ => throwUnsupportedSyntax

/-- Computes the round-tripping `n`-th goal. -/
private def roundTripNth (n : ℕ) (reverse : Bool) : TacticM (ℕ × List MVarId) := do
  let goals ← getGoals
  let nGoals ← goals.length
  let nth := if ¬reverse then n
    else if n ≤ nGoals then nGoals - n + 1 else n
  (nth, goals)

/--
`pick_goal n` will move the `n`-th goal to the front.

`pick_goal -n` will move the `n`-th goal (counting from the bottom) to the front.

See also `Tactic.rotate_goals`, which moves goals from the front to the back and vice-versa.
-/
elab "pick_goal " reverse:"-"? n:num : tactic => do
  let n := n.toNat
  let reverse := !reverse.isNone
    let (n' + 1, goals) ← roundTripNth n reverse | throwError "goals are 1-indexed"
        let (gls, g :: grs) := goals.splitAt n' | throwError "not enough goals"
        setGoals $ g :: (gls ++ grs)

/-- `swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals. -/
macro "swap" : tactic => `(pick_goal 2)

/--
`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals, replacing the chosen goal.
-/
syntax (name := on_goal) "on_goal " "-"? num " => " tacticSeq : tactic
@[tactic on_goal] def evalOnGoal : Tactic := fun stx => do
match stx with
  | `(tactic|on_goal $n => $seq:tacticSeq)  => onGoal n.toNat seq false
  | `(tactic|on_goal -$n => $seq:tacticSeq) => onGoal n.toNat seq true
  | _ => throwUnsupportedSyntax
where
  onGoal (n : ℕ) (seq : Syntax) (reverse : Bool) : TacticM Unit := do
    let (nth, goals) ← roundTripNth n reverse
    match nth with
      | 0 => throwError "goals are 1-indexed"
      | n' + 1 =>
        match goals.splitAt n' with
          | (_, []) => throwError "not enough goals"
          | (gls, g :: grs) =>
            setGoals [g]
            evalTactic seq
            setGoals $ gls ++ (← getUnsolvedGoals) ++ grs
