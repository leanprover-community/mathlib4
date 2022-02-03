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
syntax (name := rotate) "rotate" (ppSpace num)? : tactic
@[tactic rotate] def evalRotate : Tactic := fun stx => do
match stx with
  | `(tactic|rotate)    => setGoals $ (← getGoals).rotate 1
  | `(tactic|rotate $n) => setGoals $ (← getGoals).rotate n.toNat
  | _ => throwUnsupportedSyntax

/-- Brings the `n`-th goal to the front -/
def swapGoal (n : Nat) : TacticM Unit := do
  match (← getGoals).splitAt (n - 1) with
    | (_, []) => throwError "not enough goals"
    | (gls, g :: grs) => setGoals $ g :: gls ++ grs

/--
`swap n` will move the `n`-th goal to the front.

`swap` defaults to `swap 2`, which interchanges the first and second goals.
See also `Tactic.rotate`, which moves the first `n` goals to the back.
-/
syntax (name := swap) "swap" (ppSpace num)? : tactic
@[tactic swap] def evalSwap : Tactic := fun stx => do
match stx with
  | `(tactic|swap)    => swapGoal 2
  | `(tactic|swap $n) => swapGoal n.toNat
  | _ => throwUnsupportedSyntax

/-- `last` brings the last goal to the front. -/
elab "last" : tactic => do
  let length ← (← getGoals).length
  if length > 1 then
    swapGoal length
