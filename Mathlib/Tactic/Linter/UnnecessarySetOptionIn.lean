/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Lemma

/-!
# The `unnecessarySetOptionIn`

The linter reports a warning if a `set_option ... in` command is unnecessary
(i.e., the code elaborates fine without it).
We only report the outermost `set_option ... in` (i.e., nested, superfluous `set_option ... in`s
are not linted against).

The linter ignores `option`s containing `linter` as a component of their names.
The linter also skips checking unnecessary `set_option ... in` preceding `notation`.
-/

open Lean Parser Elab Command

/-- converts
* `theorem x ...`    to `some (example  ... , x)`,
* `lemma x ...`      to `some (example  ... , x)`,
* `example ...`      to `some (example  ... , 'example')`,
* `def x ...`        to `some (example  ... , 'x')`,
* `instance x? ...`  to `some (instance ... , 'x or _unnamed_instance_')`,
*  everything else   to `none`.
-/
def toExample {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `($dm:declModifiers theorem  $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers lemma    $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers example  $ds:optDeclSig $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds $dv:declVal), mkIdent `example)
  | `($dm:declModifiers def      $did:declId $ds:optDeclSig $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds $dv:declVal), did.raw[0])
  | `($dm:declModifiers instance $(_prio)? $(did)? $ds:declSig $dv:declVal) => do
    let did := did.getD (mkIdent `_unnamed_instance_)
    return some (← `($dm:declModifiers instance $ds:declSig $dv:declVal), did.raw[0])
  | _ => return none

/-- Report a warning if a `set_option ... in` command is unnecessary
(i.e., the code elaborates fine without it).
We only report the outermost `set_option ... in` (i.e., nested, superfluous `set_option ... in`s
are not linted against).

This is useful since unnecessary `set_option ... in`s are often silent left-overs of adaptations
that are no longer needed.
Cleaning them up, helps maintaining healthy, up-to-date code.

The linter runs just on the outermost `set_option ... in` mostly for simplicity.
Consider whether emitting a warning if one of the nested `set_option ... in`s can be omitted,
by removing them one at a time.
-/
register_option linter.unnecessarySetOptionIn : Bool := {
  defValue := true
  descr := "enable the unnecessarySetOptionIn linter"
}

/-- The `unnecessarySetOptionIn` linter only tries to remove `maxHeartbeat` options if the
`linter.unnecessarySetOptionIn.heartbeats` option is set to `true`. -/
register_option linter.unnecessarySetOptionIn.heartbeats : Bool := {
  defValue := false
  descr := "if `true`, then the unnecessarySetOptionIn linter also tries to remove `maxHeartbeat`
    options"
}

/-- reports a warning if the "first layer" `set_option ... in` is unnecessary. -/
def findSetOptionIn (cmd : CommandElab) : CommandElab := fun stx => do
  let mut (report?, declId) := (false, default)
  let s ← get
  match stx with
    | `(command| set_option $opt $_ in $inner) => do
      if !Linter.getLinterValue linter.unnecessarySetOptionIn.heartbeats (← getOptions) &&
        opt.getId == `maxHeartbeats then
          return
      if !opt.getId.components.contains `linter then
        if let some (exm, id) := (← toExample inner) then
          cmd exm
          let msgs := (← get).messages.toList
          (report?, declId) := (msgs.isEmpty, id)
          set s
        if report? then
          Linter.logLint linter.unnecessarySetOptionIn stx
            m!"unnecessary 'set_option {opt}' in '{declId}'"
    | _ => return

@[inherit_doc linter.unnecessarySetOptionIn]
def unnecessarySetOptionIn : Linter where run cmd := do
  let mod ← getMainModule
  if mod.getRoot == `MathlibTest && mod != `MathlibTest.UnnecessarySetOptionIn then
    return
  if Linter.getLinterValue linter.unnecessarySetOptionIn (← getOptions) then
    findSetOptionIn elabCommand cmd

initialize addLinter unnecessarySetOptionIn
