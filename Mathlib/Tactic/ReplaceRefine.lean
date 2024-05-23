/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.adomaniLeanUtils.inspect_syntax
import Mathlib.Tactic.Lemma
import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Lean.HashSet

/-!
# A linter to replace `refine'` with `refine`
-/

namespace Mathlib.Linter

/--
The linter emits a warning on any command beginning with `#` that itself emits no message.
For example, `#guard true` and `#check_tactic True ~> True by skip` trigger a message.
There is a list of silent `#`-command that are allowed.
-/
register_option linter.refine'ToRefine : Bool := {
  defValue := true
  descr := "flag `refine'` that can be converted to `refine`s"
}

namespace refine'ToRefine

open Lean Elab

open Lean
def holeToSyntHole : Syntax → Syntax
  | s@`(_) => mkNode ``Lean.Parser.Term.syntheticHole #[mkAtom "?", s]
  | s => s

def toSynthIf {m : Type → Type} [Monad m] [MonadFileMap m] (f : Syntax → Bool) (stx : Syntax) :
    m Syntax := do
  let fm ← getFileMap
  let new ← stx.replaceM (fun s =>
    if f s then
      dbg_trace fm.toPosition (s.getPos?.getD default)
      return some (holeToSyntHole s) else return none)
  return new

def allToSynth {m : Type → Type} [Monad m] [MonadFileMap m] (stx : Syntax) : m Syntax := do
  let fm ← getFileMap
  let new ← stx.replaceM (fun s =>
--    let pos := s.getPos?
--    let d := if pos.isSome then dbg_trace "{s.getPos?}: {s}"; "" else ""
--    dbg_trace d
--    dbg_trace "{s.getPos?}: {s.getKind}"
    if s.isOfKind ``Lean.Parser.Term.hole then
      dbg_trace fm.toPosition (s.getPos?.getD default)
      return some (holeToSyntHole s) else return none)
  return new

def mdCtor : MessageData → String
  | .ofFormat ..          => "ofFormat"
  | .ofPPFormat ..        => "ofPPFormat"
  | .ofGoal ..            => "ofGoal"
  | .withContext _ md       => "withContext " ++ mdCtor md
  | .withNamingContext _ md => "withNamingContext-" ++ mdCtor md
  | .nest ..              => "nest"
  | .group ..             => "group"
  | .compose ..           => "compose"
  | .tagged nm md            => "tagged" ++ toString nm ++ "//" ++ mdCtor md
  | .trace ..             => "trace"

def someToSynth {m : Type → Type} [Monad m] [MonadFileMap m]
    (pos : Array Position) (stx : Syntax) : m Syntax := do
  let fm ← getFileMap
  let new ← stx.replaceM (fun s =>
--    let pos := s.getPos?
--    let d := if pos.isSome then dbg_trace "{s.getPos?}: {s}"; "" else ""
--    dbg_trace d
--    dbg_trace "{s.getPos?}: {s.getKind}"
    if pos.contains (fm.toPosition (s.getPos?.getD default)) && s.isOfKind ``Lean.Parser.Term.hole then
      return some (holeToSyntHole s) else return none)
  return new

def isSyntPlaceHolder : MessageData → Bool
  | .withNamingContext _ (.withContext _ (.tagged `Elab.synthPlaceholder _)) => true
  | _ => false

#check Array.pop

partial
def getRefine' : Syntax → Array (Syntax × SourceInfo × Array Syntax)
  | stx@(.node si ``Lean.Parser.Tactic.refine' args) =>
    let rest := (args.map getRefine').flatten
    rest.push (stx, si, args)
  | .node _ _ args => (args.map getRefine').flatten
  | _ => default

def refine'ToRefine (stx : Syntax) : Syntax := Id.run do
  stx.replaceM fun s => match s with
    | .node si ``Lean.Parser.Tactic.refine' args =>
      let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine "
      some (.node si ``Lean.Parser.Tactic.refine args)
    | _ => none

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

def getQuestions (cmd : Syntax) : Command.CommandElabM (Array Position) := do
  let s ← get
  let refine's := getRefine' cmd
  let newCmds := refine's.map fun (r, si, args) => Id.run do
      cmd.replaceM fun s => if s == r then
        let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine "
        return some (.node si ``Lean.Parser.Tactic.refine args)
        else return none
  let mut poss := #[]
  for ncmd in newCmds do
    if let some (exm, _) ← toExample ncmd then
      Elab.Command.elabCommand exm
      let msgs := (← get).messages.msgs
      let ph := msgs.filter (fun m => isSyntPlaceHolder m.data)
      if ph.toArray.isEmpty then logInfoAt cmd "oh"
      poss := poss ++ (ph.map (·.pos)).toArray
    set s
  return poss

partial
def toRefine (cmd : Syntax) : Elab.Command.CommandElabM (Array Position × Syntax) := do
--  let s ← get
  Elab.Command.elabCommand cmd
  let msgs := (← get).messages.msgs
--  let poss := msgs.map (·.pos)
  let ph := msgs.filter fun m => isSyntPlaceHolder m.data
  let poss := (ph.map (·.pos)).toArray
--  set s
--  if poss.size != 0 then
--    logInfo m!"{poss}"
  let new ← someToSynth poss cmd
--    logInfo m!"{poss}\n{new}"
  let (oPos, nCmd) ← toRefine new
  return (poss ++ oPos, nCmd)
--  else
--    return (poss, cmd)


elab "rerere " cmd:command : command => do
  let refine's := getRefine' cmd
  let mut poss' := #[]
  for (r, si, args) in refine's do
    let ncmd ← cmd.raw.replaceM fun s => if s == r then
      let args := args.modify 0 fun _ => mkAtomFrom args[0]! "refine"
      return some (.node si ``Lean.Parser.Tactic.refine args)
      else return none
    let s ← get
    Elab.Command.elabCommand ncmd
    let msgs := (← get).messages.msgs
  --  let poss := msgs.map (·.pos)
    let ph := msgs.filter (fun m => isSyntPlaceHolder m.data)
    poss' := poss' ++ (ph.map (·.pos)).toArray
    set s
  dbg_trace poss'
  Elab.Command.elabCommand cmd
/-
  logInfo m!"{(getRefine' cmd).map Prod.fst}"
  let cmd := refine'ToRefine cmd
  logInfo <| cmd
  let s ← get
  Elab.Command.elabCommand cmd
  let msgs := (← get).messages.msgs
--  let poss := msgs.map (·.pos)
  let ph := msgs.filter fun m => isSyntPlaceHolder m.data
  let poss := ph.map (·.pos)
  logInfo m!"{poss.toArray}"
  set s
  let new ← someToSynth poss.toArray cmd
  logInfo m!"{poss.toArray}\n{new}"
  Elab.Command.elabCommand new --cmd
-/

elab "rerere' " cmd:command : command => do
  logInfo m!"{(← getQuestions cmd)}"
  --let (pos, cmd) ← toRefine cmd
  --logInfo m!"{pos}"
  Elab.Command.elabCommand cmd
/-
rerere'
example : 0 < 1 := by
  refine' lt_of_lt_of_eq (b := 1) _ _
  · refine' lt_of_lt_of_eq (b := 1) _ _
    · exact Nat.zero_lt_one
    · rfl
  · rfl
-/


/-- Gets the value of the `linter.refine'ToRefine` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.refine'ToRefine o

/-- Checks that no command beginning with `#` is present in 'Mathlib',
except for the ones in `allowed_commands`.

If `warningAsError` is `true`, then the linter logs an info (rather than a warning).
This means that CI will eventually fail on `#`-commands, but not stop it from continuing.

However, in order to avoid local clutter, when `warningAsError` is `false`, the linter
logs a warning only for the `#`-commands that do not already emit a message. -/
def refine'ToRefineLinter : Linter where run stx := do
  if getLinterHash (← getOptions) then
    let pos ← getQuestions stx
    if pos != #[] then dbg_trace s!"{pos}" --else dbg_trace s!"{pos}"
/-
    let withRefine := refine'ToRefine stx
    if stx != withRefine then
      let s ← get
      let (pos, _withRefine) ← toRefine withRefine
      logInfo _withRefine
      set s
      dbg_trace pos
      if pos != #[] then
          logInfoAt stx m!"{pos}"
-/

initialize addLinter refine'ToRefineLinter
#exit
inspect
example : 0 < 1 := by
  refine' lt_of_lt_of_eq (b := 1) _ _
  · exact Nat.zero_lt_one
  · rfl

/-
|   |   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |   |-node Lean.Parser.Term.byTactic, none
|   |   |   |-atom original: ⟨⟩⟨\n  ⟩-- 'by'
|   |   |   |-node Lean.Parser.Tactic.tacticSeq, none
|   |   |   |   |-node Lean.Parser.Tactic.tacticSeq1Indented, none
|   |   |   |   |   |-node null, none
|   |   |   |   |   |   |-node Lean.Parser.Tactic.refine', none
|   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- 'refine''
|   |   |   |   |   |   |   |-node Lean.Parser.Term.app, none
|   |   |   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (lt_of_lt_of_eq,lt_of_lt_of_eq)
|   |   |   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.namedArgument, none
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '('
|   |   |   |   |   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (b,b)
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |   |   |   |   |   |   |   |   |   |-node num, none
|   |   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '1'
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ')'
|   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.hole, none
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '_'
|   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.hole, none
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨\n  ⟩-- '_'
-/

#check Lean.MessageLog.msgs

run_cmd dbg_trace ← Lean.Elab.Command.getMainModule
inspect
example : 0 < 1 := by
  refine' lt_of_lt_of_eq (b := 1) _ ?_
  · exact Nat.zero_lt_one
  · rfl

rerere
example : 0 < 1 := by
  refine' lt_of_lt_of_eq (b := 1) _ _
  · refine' lt_of_lt_of_eq (b := 1) _ _
    · exact Nat.zero_lt_one
    · rfl
  · rfl

rerere'
example : 0 < 1 := by
  refine lt_of_lt_of_eq (b := 1) _ _
  · refine lt_of_lt_of_eq (b := 1) _ _
    · exact Nat.zero_lt_one
    · rfl
  · rfl


--run_cmd Elab.Command.liftCoreM do Meta.MetaM.run do
--  let s ← `(_)
--  logInfo (holeToSyntHole s)
--  let s ← `(tactic| $(mkIdent `refine) $(mkIdent `lt_of_lt_of_eq) (b := 1) ?_ ?_)
--  logInfo (allToSynth s)

/-
|   |   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |   |-node Lean.Parser.Term.byTactic, none
|   |   |   |-atom original: ⟨⟩⟨\n  ⟩-- 'by'
|   |   |   |-node Lean.Parser.Tactic.tacticSeq, none
|   |   |   |   |-node Lean.Parser.Tactic.tacticSeq1Indented, none
|   |   |   |   |   |-node null, none
|   |   |   |   |   |   |-node Lean.Parser.Tactic.refine, none
|   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- 'refine'
|   |   |   |   |   |   |   |-node Lean.Parser.Term.app, none
|   |   |   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (lt_of_lt_of_eq,lt_of_lt_of_eq)
|   |   |   |   |   |   |   |   |-node null, none
|   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.namedArgument, none
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '('
|   |   |   |   |   |   |   |   |   |   |-ident original: ⟨⟩⟨ ⟩-- (b,b)
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':='
|   |   |   |   |   |   |   |   |   |   |-node num, none
|   |   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '1'
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- ')'
|   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.syntheticHole, none
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '?'
|   |   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.hole, none
|   |   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨ ⟩-- '_'
|   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.syntheticHole, none
|   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- '?'
|   |   |   |   |   |   |   |   |   |   |-node Lean.Parser.Term.hole, none
|   |   |   |   |   |   |   |   |   |   |   |-atom original: ⟨⟩⟨\n  ⟩-- '_'

-/
