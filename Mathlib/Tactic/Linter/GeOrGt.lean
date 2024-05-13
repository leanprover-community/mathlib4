/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## The `ge_or_gt` linter

A linter for checking whether a declaration contains `≥` or `>`.

TODO currently only in the conclusion? xxx compare with mathlib3!
-/

open Lean Elab Command

namespace Mathlib.Linter.ge_or_gt

def is_ge_or_gt : Syntax → Bool
  | `($_ ≥ $_) => true
  | `($_ > $_) => true
  | _ => false

/- places where this is allowed:
- comments and doc comments, obviously
- custom notation, like `ℚ≥0` (including local notation, e.g.
  `local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}` in Order/Nonneg/Module.lean)        fine

- under binders, like `∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε` (with `∀` or `∃`)
- just check in theorem statements for now - this is important for rewrites!
in proofs, we ignore this!
-/
def contains_illegal_ge_gt : Syntax → Bool
  | `($_:ident) => false
  | `(Exists $_x:ident > $_y:term) => false -- allow
  | `(Forall $_x:ident > $_y:term) => false -- allow
  -- | `($_:missing) => false
  | _ => true

/-- The `ge_or_gt` linter emits a warning if a declaration contains `≥` or `>`
  in illegal places. -/
register_option linter.geOrGt : Bool := {
  defValue := true
  descr := "enable the `ge_or_gt` linter"
}

-- xxx: should this be moved to a different, common  place?
/-- Gets the value of the `linter.geOrGt` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.geOrGt o

/-- docstring here -/
def getOrGtLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match stx.findStack? (fun _ ↦ true) is_ge_or_gt with
    | some ((head, _n)::_chain) =>
      -- XXX: exclude remaining case
        Linter.logLint linter.geOrGt head m!"'≥ or > used in an illegal position\
        please restate to use ≤ or < instead"
    | _ => return

initialize addLinter getOrGtLinter

end Mathlib.Linter.ge_or_gt
