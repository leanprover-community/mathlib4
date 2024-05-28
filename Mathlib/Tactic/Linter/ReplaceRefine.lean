/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.List.Basic
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

/-- extracts the `Array` of subsyntax of the input `Syntax` that satisfies the given predicate
`Syntax → Bool`.
-/
partial
def _root_.Lean.Syntax.findAll : Syntax → (Syntax → Bool) → Array Syntax
  | stx@(.node _ _ args), f =>
    let rest := (args.map (·.findAll f)).flatten
    if f stx then rest.push stx else rest
  | s, f => if f s then #[s] else #[]

/-- extracts "holes" `_` from the input syntax.
Converting `refine'` to `refine`, these are the candidate nodes for the replacement `_` to `?_`.
-/
def getHoles (stx : Syntax) : Array Syntax :=
  stx.findAll (·.isOfKind ``Lean.Parser.Term.hole)


/-
|-node Lean.Parser.Term.syntheticHole, none
|   |-atom original: ⟨⟩⟨⟩-- '?'
|   |-node Lean.Parser.Term.hole, none
|   |   |-atom original: ⟨⟩⟨ ⟩-- '_'

|-node Lean.Parser.Term.hole, none
|   |-atom original: ⟨⟩⟨⟩-- '_'
-/

/-- converts an "anonymous hole" `_` to a "synthetic hole" `?_` -/
def holeToSyntHole : Syntax → Syntax
  | hole@(.node si ``Lean.Parser.Term.hole _) =>
    .node si ``Lean.Parser.Term.syntheticHole #[mkAtomFrom hole "?", hole]
  | s => s

/-- extracts `refine'` from the input syntax. -/
def getRefine's (stx : Syntax) : Array Syntax :=
  stx.findAll (·.isOfKind ``Lean.Parser.Tactic.refine')
--
--/-- `candidateRefines stx` assumes that `stx` is a syntax node representing `refine' term`.
--It returns the array `#[refine term₁, ..., refine termₙ]`, where each `termᵢ` is obtained from
--`term` by replacing a subset of the `_` with `?_`. -/
--def candidateRefines (stx : Syntax) : Array Syntax := Id.run do
--  let mut cands := #[]
--  let holes := getHoles stx
--  for sub in holes.toList.sublistsFast do
--    let subWith? := sub.mapM fun s => s.replaceM (fun t => )
--    let ncmd ← stx.replaceM (fun s => if sub.contains s then )
--    _


--/-- extracts `refine'` from the given `Syntax`, returning also the `SourceInfo`, the arguments
--of the `refine'` node and whether `refine'` contains `..`. -/
--partial
--def refine'ToRefines : Syntax → Array Syntax
--  | stx@(.node si ``Lean.Parser.Tactic.refine' args) =>
--    dbg_trace "refine' found"
--    let rest := (args.map getRefine').flatten
--    rest.push (stx, si, args, stx.find? (·.isOfKind ``Lean.Parser.Term.optEllipsis))
--  | .node _ _ args => (args.map getRefine').flatten
--  | _ => default



elab "ho " cmd:command : command => do
  let holes := getHoles cmd
  let sholes := holes.map (holeToSyntHole ·)
  logInfo m!"{holes}, {holes.map (·.getPos?)}, {sholes}, {sholes.map (·.getPos?)}"
  Command.elabCommand cmd

/-- checks whether a `MessageData` refers to an error of a missing `?` is `refine`. -/
def isSyntPlaceHolder : MessageData → Bool
  | .withNamingContext _ (.withContext _ (.tagged `Elab.synthPlaceholder _)) => true
  | _ => false

/-- extracts `refine'` from the given `Syntax`, returning also the `SourceInfo`, the arguments
of the `refine'` node and whether `refine'` contains `..`. -/
partial
def getRefine' : Syntax → Array (Syntax × SourceInfo × Array Syntax × Option Syntax)
  | stx@(.node si ``Lean.Parser.Tactic.refine' args) =>
    dbg_trace "refine' found"
    let rest := (args.map getRefine').flatten
    rest.push (stx, si, args, stx.find? (·.isOfKind ``Lean.Parser.Term.optEllipsis))
  | .node _ _ args => (args.map getRefine').flatten
  | _ => default

/-- converts
* `theorem x ...`  to `example ...`,
* `lemma x ...`    to `example ...`,
* `instance x ...` to `example ...`,
*  everything else goes to itself.

This avoids producing two declarations with the same name in the environment.
-/
def toExample {m : Type → Type} [Monad m] [MonadQuotation m] : Syntax → m Syntax
  | `($dm:declModifiers theorem $_did:declId $ds* : $t $dv:declVal) =>
    `($dm:declModifiers example $ds* : $t $dv:declVal)
  | `($dm:declModifiers lemma $_did:declId $ds* : $t $dv:declVal) =>
    `($dm:declModifiers example $ds* : $t $dv:declVal)
  | `($dm:declModifiers instance $_did:declId $ds* : $t $dv:declVal) =>
    `($dm:declModifiers example $ds* : $t $dv:declVal)
  | s => return s

/-- replaces each `refine'` by `refine` in succession in `cmd` and, each time, catches the errors
of missing `?`, collecting their positions.  Eventually, it returns an array of pairs
`(1/0, position)`, where
* `1` means that the `position` is the beginning of `refine'` and
* `0` means that the `position` is a missing `?`.
-/
def getQuestions (cmd : Syntax) : Command.CommandElabM (Array (Nat × Position)) := do
  let s ← get
  let fm ← getFileMap
  let refine's := getRefine' cmd
  let newCmds := refine's.map fun (r, si, args, dots?) => Id.run do
      if let some dots := dots? then dbg_trace "{dots} present"
      let ncm ← cmd.replaceM fun s => if s == r then
        let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine "
        return some (.node si ``Lean.Parser.Tactic.refine args)
        else return none
      return (r, ncm)
  let mut poss := #[]
  for (r, ncmd) in newCmds do
    let exm ← toExample ncmd
    Elab.Command.elabCommand exm
    let msgs := (← get).messages.msgs
    --dbg_trace msgs.toArray.map (·.endPos)
    let ph := msgs.filter (fun m => isSyntPlaceHolder m.data)
    if ! ph.toArray.isEmpty then
      -- a repetition in `Position`s is an indication that `refine` cannot replace `refine'`
      let positions := (ph.map (·.pos)).toList
      if positions == positions.eraseDup then
        --dbg_trace ph.size == msgs.size
        --dbg_trace ph.toArray.map (·.endPos)
        poss := poss ++
          (ph.map (0, ·.pos)).toArray.push (1, fm.toPosition (r.getPos?.getD default))
  set s
  return poss

/-- replaces each `refine'` by `refine` in succession in `cmd` and, each time, catches the errors
of missing `?`, collecting their positions.  Eventually, it returns an array of pairs
`(1/0, position)`, where
* `1` means that the `position` is the beginning of `refine'` and
* `0` means that the `position` is a missing `?`.
-/
def getQuestions' (cmd : Syntax) : Command.CommandElabM (Array (Nat × Position)) := do
  let s ← get
  let fm ← getFileMap
  let refine's := getRefine' cmd
  let newCmds := refine's.map fun (r, si, args, dots?) => Id.run do
      if let some dots := dots? then dbg_trace "{dots} present"
      let ncm ← cmd.replaceM fun s => if s == r then
        let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine "
        return some (.node si ``Lean.Parser.Tactic.refine args)
        else return none
      return (r, ncm)
  let mut poss := #[]
  for (r, ncmd) in newCmds do
    let exm ← toExample ncmd
    Elab.Command.elabCommand exm
    let msgs := (← get).messages.msgs
    --dbg_trace msgs.toArray.map (·.endPos)
    let ph := msgs.filter (fun m => isSyntPlaceHolder m.data)
    if ! ph.toArray.isEmpty then
      -- a repetition in `Position`s is an indication that `refine` cannot replace `refine'`
      let positions := (ph.map (·.pos)).toList
      if positions == positions.eraseDup then
        --dbg_trace ph.size == msgs.size
        --dbg_trace ph.toArray.map (·.endPos)
        poss := poss ++
          (ph.map (0, ·.pos)).toArray.push (1, fm.toPosition (r.getPos?.getD default))
  set s
  return poss

/-- Gets the value of the `linter.refine'ToRefine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine'ToRefine o

/-- Reports the positions of missing `?`. -/
def refine'ToRefineLinter : Linter where run stx := do
  if getLinterHash (← getOptions) then
    let pos ← getQuestions stx
    if pos != #[] then dbg_trace s!"{pos}"

initialize addLinter refine'ToRefineLinter
