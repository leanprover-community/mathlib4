/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Lemma
import Lean.Elab.Command
import Lean.Linter.Util

/-!
The `unusedSetOptionIn` linter warns against "most external" unused `set_option ... in`s.
-/

open Lean Elab Command

/-- converts
* `theorem x ...` to  `some (example ... , x)`,
* `lemma x ...`   to  `some (example ... , x)`,
* `example ...`   to ``some (example ... , `example)``,
*  everything else goes to `none`.
-/
def toExample {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `($dm:declModifiers theorem $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers lemma $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers example $ds:optDeclSig $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds $dv:declVal), mkIdent `example)
  | _ => return none

/-- The `unusedSetOptionIn` linter warns against "most external" unused `set_option ... in`s. -/
register_option linter.unusedSetOptionIn : Bool := {
  defValue := true
  descr := "enable the unusedSetOptionIn linter"
}

/-- Gets the value of the `linter.unusedSetOptionIn` option. -/
def getSetOptionIn (o : Options) : Bool := Linter.getLinterValue linter.unusedSetOptionIn o

/-- reports a warning if the "first layer" `set_option ... in` is unused. -/
def findSetOptionIn (cmd : CommandElab) : CommandElab := fun stx => do
  let mut report? := (false, default)
  let s ← get
  match stx with
    | .node _ ``Lean.Parser.Command.in #[
        .node _ ``Lean.Parser.Command.set_option #[_, opt, _, _],
        _,  -- atom `in`
        inner] => do
      if let some (exm, id) := (← toExample inner) then
        cmd exm
        let msgs := (← get).messages.toList
        report? := (msgs.isEmpty, id)
        set s
      if report?.1 then
        Linter.logLint linter.unusedSetOptionIn stx m!"unused 'set_option {opt}' in '{report?.2}'"
    | _ => return

@[inherit_doc linter.unusedSetOptionIn]
def unusedSetOptionIn : Linter where run cmd := do
  if getSetOptionIn (← getOptions) then
    findSetOptionIn elabCommand cmd

initialize addLinter unusedSetOptionIn
