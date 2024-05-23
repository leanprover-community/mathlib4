/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Mathlib.Tactic.Lemma

/-!
# A linter to replace `refine'` with `refine`
-/

namespace Mathlib.Linter

/--
The linter helps with the conversion `refine'` to `refine`, by printing the positions of
missing `?`.
-/
register_option linter.refine'ToRefine : Bool := {
  defValue := true
  descr := "flag `refine'` that can be converted to `refine`s"
}

namespace refine'ToRefine

open Lean Elab

/-- checks whether a `MessageData` refers to an error of a missing `?` is `refine`. -/
def isSyntPlaceHolder : MessageData → Bool
  | .withNamingContext _ (.withContext _ (.tagged `Elab.synthPlaceholder _)) => true
  | _ => false

/-- extracts `refine'` from the given `Syntax`, returning also the `SourceInfo` and the arguments
of the `refine'` node. -/
partial
def getRefine' : Syntax → Array (Syntax × SourceInfo × Array Syntax)
  | stx@(.node si ``Lean.Parser.Tactic.refine' args) =>
    let rest := (args.map getRefine').flatten
    rest.push (stx, si, args)
  | .node _ _ args => (args.map getRefine').flatten
  | _ => default

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

/-- replaces each `refine'` by `refine` in succession in `cmd` and, each time, catches the errors
of missing `?`, collecting their positions.  Eventually, it returns the pair of array of positions
of the `refine'` and of the missing `?`. -/
def getQuestions (cmd : Syntax) : Command.CommandElabM (Array Position × Array Position) := do
  let s ← get
  let fm ← getFileMap
  let refine's := getRefine' cmd
  let newCmds := refine's.map fun (r, si, args) => Id.run do
      let ncm ← cmd.replaceM fun s => if s == r then
        let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine "
        return some (.node si ``Lean.Parser.Tactic.refine args)
        else return none
      return (r, ncm)
  let mut poss := #[]
  let mut refs := #[]
  for (r, ncmd) in newCmds do
    if let some (exm, _) ← toExample ncmd then
      Elab.Command.elabCommand exm
      let msgs := (← get).messages.msgs
      let ph := msgs.filter (fun m => isSyntPlaceHolder m.data)
      if ph.toArray.isEmpty then logInfoAt cmd "oh" else
        refs := refs.push <| fm.toPosition (r.getPos?.getD default)
        poss := poss ++ (ph.map (·.pos)).toArray
    set s
  return (refs, poss)

/-- Gets the value of the `linter.refine'ToRefine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine'ToRefine o

/-- Reports the positions of missing `?`. -/
def refine'ToRefineLinter : Linter where run stx := do
  if getLinterHash (← getOptions) then
    let (refs, pos) ← getQuestions stx
    if pos != #[] then dbg_trace s!"refine': {refs}\n?: {pos}"

initialize addLinter refine'ToRefineLinter
