/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Linter.Util
import Lean.Elab.Command

/-!
A configurable linter that flags `Syntax` uses that are unnecessary.
-/

open Lean Parser Elab Command

/-- `unnecessarySyntax` linter takes as input a `CommandElabM` function `f` assigning to
a command `cmd` syntax an array of triples `(newCmd, positionStx, message)` consisting of
* the syntax `newCmd` of a command;
* the syntax `positionStx` effectively encoding a position for message reporting;
* a `MessageData` `message`.

For each command `cmd`, the linter then computes the array `f cmd`, and, for each entry
`(newCmd, positionStx, message)` of `f cmd` it
* elaborates `newCmd` inside a fresh namespace;
* if `newCmd` reports an error, it continues;
* if `newCmd` reports no error, then it flags `message` warning at `positionStx`.
-/
register_option linter.unnecessarySyntax : Bool := {
  defValue := true
  descr := "enable the unnecessarySyntax linter"
}

@[inherit_doc linter.unnecessarySyntax]
def getUnnecessarySyntax (o : Options) : Bool := Linter.getLinterValue linter.unnecessarySyntax o

@[inherit_doc linter.unnecessarySyntax]
def unnecessarySyntax (f : Syntax → CommandElabM (Array (Syntax × Syntax × MessageData))) :
    Linter where run cmd := do
  unless getUnnecessarySyntax (← getOptions) do
    return
  let news ← f cmd
  let mut msgs := #[]
  let s ← get
  let newNamespace ← liftTermElabM mkFreshId
  for (newCmd, posStx, msg) in news do
    withScope (fun scp => { scp with currNamespace := scp.currNamespace ++ newNamespace }) do
      elabCommand newCmd
    if !(← get).messages.hasErrors then
      msgs := msgs.push (msg, posStx)
    set s
  for (m, partialStx) in msgs do
    Linter.logLint linter.unnecessarySyntax partialStx m

/-- On input the syntax for the modifiers of a declaration, `removePartialModifier` returns
the pair consisting of the syntax for the modifiers *without* `partial`, as well as the syntax
for the `partial` node.
It `partial` is not part of the input syntax, then it returns `default`. -/
def removePartialModifier (stx : TSyntax ``declModifiers) : (TSyntax ``declModifiers × Syntax) :=
  match stx.raw with
    | .node si ``declModifiers args =>
      (⟨.node si ``declModifiers (args.modify 5 (fun _ => mkNullNode))⟩, args.getD 5 default)
    | _ => default

/-- `removePartial cmd` takes as input the `Syntax` `cmd` and
* if `cmd` is the syntax for a `partial def [...]`, then it returns `#[def [...], partial]`
* otherwise, it returns `#[]`.

The output `partial` node is used to report warnings.
-/
def removePartial {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Array (TSyntax `command × Syntax))
  | `($dm:declModifiers def $did:declId $ds:optDeclSig $dv:declVal) => do
    let (noPartial, partialStx) := removePartialModifier dm
    if dm == noPartial then return #[]
    return #[(← `($noPartial:declModifiers def $did $ds $dv:declVal), partialStx)]
  | _ => return #[]

/-- `reportPartial stx` takes as input the `Syntax` `stx`.
If `stx` does not represent a `partial def [...]`, then it returns `#[]`.
Otherwise it returns a triple consisting of `#[def [...], partial, "unnecessary use of `partial`"]`.
-/
abbrev reportPartial (stx : Syntax) : CommandElabM (Array (Syntax × Syntax × MessageData)) :=
  return (← removePartial stx).map fun (c, p) => (c, p, m!"unnecessary use of `partial`")

initialize addLinter (unnecessarySyntax reportPartial)
