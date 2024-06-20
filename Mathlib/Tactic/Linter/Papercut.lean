/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.List.Basic

/-!
# The papercut linter

The papercut linter tries to ease new users into Lean.
It flags certain design decisions that may be surprising or confusing.

For instance,
* `3 - 5 = 0` (`Nat`-subtraction is truncated subtraction),
* `3 / 5 = 0` (`Nat`-division is rounded division),
* `(3 : ℤ) / 5 = 0` (`Int`-division is rounded division),
* `x / 0 = 0` for most types (division by `0` equals `0`).
-/

open Lean Elab Command

namespace Mathlib.Linter.Papercut

/-- `getPapercuts e` takes as input an expression `e` and returns an `Option MessageData`,
representing a helpful message in case the expression `e` involves certain
implementation details that may be confusing.

For instance, it flags `Nat.sub`, `Nat.div`, `Int.div` and division by `0`.
-/
def getPapercuts (e : Expr) : Meta.MetaM (Option MessageData) := do
  let expNat := mkConst ``Nat
  let expInt := mkConst ``Int
  let expZero := mkConst ``Nat.zero
  match e.getAppFnArgs with
    | (``HSub.hSub, #[n1, n2, n3, _, a, b]) =>
      if ← [n1, n2, n3].allM (Meta.isDefEq · expNat) then
        return some m!"Subtraction in ℕ is actually truncated subtraction: e.g. `1 - 2 = 0`!\n\
                       This yields the 'expected' result only when you also prove the inequality\n\
                       '{← Meta.ppExpr b} ≤ {← Meta.ppExpr a}'"
      else return none
    | (``HDiv.hDiv, #[n1, n2, n3, a, b, zero]) =>
      let zer ← Meta.mkAppOptM ``OfNat.ofNat #[← instantiateMVars n3, expZero, none]
      if ← Meta.isDefEq zer zero then
        return some m!"Division by `0` is usually defined to be zero: e.g. `3 / 0 = 0`!\n\
                       This is usually defined to be `0`, to avoid having to constantly prove \
                       that denominators are non-zero."
      else if ← [n1, n2, n3].allM (Meta.isDefEq · expNat) then
        return some m!"Division in ℕ is actually the floor of the division: e.g. `1 / 2 = 0`!\n\
                       This yields the 'expected' result only when you also prove that \
                       '{← Meta.ppExpr b}' divides '{← Meta.ppExpr a}'"
      else if ← [n1, n2, n3].allM (Meta.isDefEq · expInt) then
        return some m!"\
                    Division in ℤ is actually the floor of the division: e.g. `(1 : ℤ) / 2 = 0`!\n\
                    This yields the 'expected' result only when you also prove that \
                    '{← Meta.ppExpr b}' divides '{← Meta.ppExpr a}'"
      else return none
    | _ => return none

/-- The "papercut" linter emits a warning on certain quirks of the basic
definitions. -/
register_option linter.papercut : Bool := {
  defValue := false
  descr := "enable the papercut linter"
}

@[inherit_doc Mathlib.Linter.Papercut.linter.papercut]
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.papercut o

/-- Avoids context-free `InfoTree` node in `InfoTree.visitM`. -/
def isEmpty : InfoTree → Bool
  | .node _ is => is.isEmpty
  | _ => false

@[inherit_doc Mathlib.Linter.Papercut.linter.papercut]
def papercutLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterHash (← getOptions) do
    return
  if (← get).messages.unreported.isEmpty then
    return
  let initInfoTrees ← getResetInfoTrees
  for t in initInfoTrees.toArray do liftTermElabM do
    unless isEmpty t do  -- there is nothing to see if `t` is empty
    let x ← t.visitM (α := List (Syntax × MessageData))
      (postNode := fun ctx info _ msgs => do
        let msgs := msgs.reduceOption.join
        if let .ofTermInfo ti := info then
          Meta.withMCtx ctx.mctx <| Meta.withLCtx ti.lctx {} do
            if let some msg ← getPapercuts ti.expr then
              let next := (ti.stx, msg)
              if !(msgs.map fun d => d.1.getPos?).contains next.1.getPos? then
                return next :: msgs
              else return msgs
            else return msgs
        else return msgs
       )
    for (stx, msg) in x.getD [] do
      Linter.logLint linter.papercut stx m!"{msg}"

initialize addLinter papercutLinter
