/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arthur Paulino
-/

import Lean
import Mathlib.Data.List.Defs

namespace Mathlib.Tactic

open Lean Elab Elab.Tactic

/--
`rotate` moves the first goal to the back. `rotate n` will do this `n` times.

See also `Tactic.swap`, which moves the `n`th goal to the front.
-/
syntax (name := rotate) "rotate" ppSpace "-"? (num)? : tactic
@[tactic rotate] def evalRotate : Tactic := fun stx => do
match stx with
  | `(tactic|rotate)     => setGoals $ (← getGoals).rotateLeft 1
  | `(tactic|rotate -)   => setGoals $ (← getGoals).rotateRight 1
  | `(tactic|rotate $n)  => setGoals $ (← getGoals).rotateLeft n.toNat
  | `(tactic|rotate -$n) => setGoals $ (← getGoals).rotateRight n.toNat
  | _ => throwUnsupportedSyntax

/--
`swap n` will move the `n`-th goal to the front.

`swap` defaults to `swap 2`, which interchanges the first and second goals.
See also `Tactic.rotate`, which moves the first `n` goals to the back.
-/
syntax (name := swap) "swap" ppSpace ppSpace "-"? (num)? : tactic
@[tactic swap] def evalSwap : Tactic := fun stx => do
match stx with
  | `(tactic|swap)     => swap 2 false
  | `(tactic|swap -)   => swap 1 true
  | `(tactic|swap $n)  => swap n.toNat false
  | `(tactic|swap -$n) => swap n.toNat true
  | _ => throwUnsupportedSyntax
where
  swap (n : Nat) (reverse : Bool) : TacticM Unit := do
    let goals ← getGoals
    let nGoals ← goals.length
    let nth := if ¬reverse then n
      else if n ≤ nGoals then nGoals - n + 1 else nGoals + 1
    match nth with
      | 0 => throwError "goals are 1-indexed"
      | n' + 1 =>
        match goals.splitAt n' with
          | (_, []) => throwError "not enough goals"
          | (gls, g :: grs) => setGoals $ g :: gls ++ grs
