/-
Copyright (c) 2023 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Scott Morrison, Kimball Leisinger, Leo de Moura
-/
import Lean
import Std.Tactic.TryThis
import Aesop
/-!
# AidedBy tactic combinator: asynchronous tactic execution

This implements a tactic combinator `aided_by` that automatically runs a tactic in the background.
The syntax is essentially `"aided_by" tacticSeq "do" (tacticSeq)?`,
with the first tactic sequence to be run in the background (e.g. `aesop?`)
while the second tactic sequence is intractively entered.
We also provide the sytax `"by!" tacticSeq` as a shorthand for `"aided_by" aesop? "do" tacticSeq`.

When elaborating each tactic in the (second) tactic sequence:

* We launch a tactic in a separate thread,
which on completion caches the resulting proof state if successful.
* We wait briefly (50 ms by default) and then
look for a proof state in the cache that matches the current goal and local context.
* If we find a matching proof state,
we use it to complete the proof with a `TryThis` action.
* Otherwise the user continues proving interactively.
* Observe that as the user works interactively,
the tactic sequence is re-evaluated,
and hence we check if the background task completed the proof at some stage.
-/


open Lean Meta Elab Term Tactic Core Parser Tactic
open Std.Tactic


/--
Helper for running to `IO` from `EIO`.
-/
def EIO.runToIO (eio: EIO Exception α) : IO α  := do
  match ←  eio.toIO' with
  | Except.ok x =>
      pure x
  | Except.error e =>
      let msg ← e.toMessageData.toString
      IO.throwServerError msg

namespace Mathlib.Tactic.AidedBy

/--
Extracting an array of tactics from a `tacticSeq`.
(code due to Leo de Moura)
-/
def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

/--
Appending a `tacticSeq` to an array of tactics to form a `tacticSeq`.
-/
def appendTactics (ts : Array (TSyntax `tactic))
    (s : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := ts ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := ts ++ t
      `(tacticSeq| $[$ts']*)
  | _ => `(tacticSeq| $[$ts]*)

/--
Detects if a tactic sequence is a `sorry` tactic in that it can prove `False`.
-/
def isSorry (tacticCode: TSyntax `tactic) : TermElabM Bool := do
  let goal ← mkFreshExprMVar (mkConst ``False)
  try
    let (goals, _) ← Elab.runTactic  goal.mvarId! tacticCode
    return goals.isEmpty
  catch _ =>
    return false

register_option aided_by.delay : Nat :=
  { defValue := 50
    group := "aided_by"
    descr := "Time to wait after launching a task." }


deriving instance BEq, Hashable, Repr for LocalDecl

/--
Key for the cache of proof states.
-/
structure GoalKey where
  goal : Expr
  lctx : List <| Option LocalDecl
deriving BEq, Hashable, Repr

/--
Proof state.
-/
structure ProofState where
  core   : Core.State
  meta   : Meta.State
  term?  : Option Term.State
  script : TSyntax ``tacticSeq
  messages : List Message

/--
Get the current goal and local context and form a key.
-/
def GoalKey.get : TacticM GoalKey := do
  let lctx ← getLCtx
  let goal ← getMainTarget
  pure { goal := goal, lctx := lctx.decls.toList }

section Caches

/--
Cache of proof states for successful searches.
-/
initialize tacticCache : IO.Ref (HashMap GoalKey ProofState)
        ← IO.mkRef ∅

/--
Keys for which a search has been launched.
-/
initialize spawnedKeys :
  IO.Ref (HashSet <| GoalKey)
        ← IO.mkRef  ∅

/--
Check if a search has been launched for a key.
-/
def isSpawned (key : GoalKey) : IO Bool := do
  let m ← spawnedKeys.get
  return m.contains key

/--
Mark a key as having a search launched.
-/
def markSpawned (key : GoalKey)  : IO Unit := do
  spawnedKeys.modify fun m => m.insert key

/--
Mark a key as having a search completed and save the result.
-/
def putTactic (key : GoalKey) (s : ProofState) : MetaM Unit := do
  tacticCache.modify fun m => m.insert key s

/--
Get the (optional) proof state for a key.
-/
def getState (key : GoalKey) : TacticM (Option ProofState) := do
  let m ← tacticCache.get
  return m.find? key

end Caches

/--
Parses (if possible) a string as a `tacticSeq`.

Note: This is a slight modification of `Parser.runParserCategory`
due to Scott Morrison/Kim Liesinger. -/
def parseAsTacticSeq (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax ``tacticSeq) :=
  let p := andthenFn whitespace Tactic.tacticSeq.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok ⟨s.stxStack.back⟩
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

/--
Extract a tactic from a message
if there is a message beginning with "Try this:".
Otherwise return a default tactic.
-/
def getMsgTacticD (default : TSyntax ``tacticSeq)  :
    CoreM <| (TSyntax ``tacticSeq) × (List Message) := do
  let msgLog ← Core.getMessageLog
  let msgs := msgLog.toList
  let mut tac : TSyntax ``tacticSeq := default
  for msg in msgs do
    let msg := msg.data
    let msg ← msg.toString
    match msg.dropPrefix? "Try this:" with
    | none =>
      pure ()
    | some msg => do
      let parsedMessage :=
        parseAsTacticSeq (←getEnv) msg.toString.trimLeft
      match parsedMessage with
      | Except.ok tac' =>
        resetMessageLog
        tac:=  tac'
      | _ =>
        logInfo m!"failed to parse tactic ({msg.toString})"
        pure ()
  return (tac, msgs)

/--
Run a tactic in `Meta` and cache the resulting proof state
if the tactic is successful and finishing.
-/
def runAndCacheM (tacticCode : TSyntax ``tacticSeq)
  (goal: MVarId) (target : Expr)  : MetaM Unit :=
  goal.withContext do
    let lctx ← getLCtx
    let key : GoalKey := { goal := target, lctx := lctx.decls.toList }
    if ←isSpawned key then
      return ()
    markSpawned key
    let core₀ ← getThe Core.State
    let meta₀ ← getThe Meta.State
    try
      let (goals, ts) ← runTactic  goal tacticCode
      unless goals.isEmpty do
        throwError m!"Tactic not finishing, remaining goals:\n{goals}"
      let (code, msgs) ← getMsgTacticD tacticCode
      let s : ProofState := {
        core   := (← getThe Core.State)
        meta   := (← getThe Meta.State)
        term?   := some ts
        script := code
        messages := msgs
        }
      putTactic key s
    catch _ =>
    set core₀
    set meta₀

/--
Run a tactic in `IO` and cache the resulting proof state
if the tactic is successful and finishing.
-/
def runAndCacheIO (tacticCode : TSyntax ``tacticSeq)
    (goal: MVarId) (target : Expr)
    (mctx : Meta.Context) (ms : Meta.State)
    (cctx : Core.Context) (cs: Core.State) : IO Unit :=
  let eio :=
  (runAndCacheM tacticCode goal target).run' mctx ms |>.run' cctx cs
  let res := eio.runToIO
  res

/--
Fetch a proof (if cached) for the current goal.
-/
def fetchProof  : TacticM ProofState :=
  focus do
  let key ← GoalKey.get
  let goal ← getMainGoal
  match (← getState key) with
  | none =>
    throwTacticEx `fetch goal  m!"No cached result found for the goal : {← ppExpr <| key.goal }."
  | some s => do
    return s


syntax (name := autoTacs) "aided_by" ("from_by")? tacticSeq "do" (tacticSeq)? : tactic

macro "by#" tacs:tacticSeq : term =>
  `(by
  aided_by from_by aesop? do $tacs)

macro "by#"  : term =>
  `(by
  aided_by from_by aesop? do)

/--
Implementation of `aided_by` tactic.
-/
@[tactic autoTacs] def autoStartImpl : Tactic := fun stx =>
withMainContext do
match stx with
| `(tactic| aided_by from_by $auto? do $tacticCode) =>
    autoStartImplAux stx auto? tacticCode true
| `(tactic| aided_by $auto? do $tacticCode) =>
    autoStartImplAux stx auto? tacticCode false
| `(tactic| aided_by from_by $auto? do) => do
    autoStartImplAux' stx auto? true
| `(tactic| aided_by $auto? do) => do
    autoStartImplAux' stx auto? false
| _ => throwUnsupportedSyntax
where
  initialSearch (stx: Syntax)
    (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)(fromBy: Bool) : TacticM Unit :=
    withMainContext do
    if (← getUnsolvedGoals).isEmpty then
        return ()
    let ioSeek : IO Unit := runAndCacheIO
      autoCode  (← getMainGoal) (← getMainTarget)
              (← readThe Meta.Context) (← getThe Meta.State )
              (← readThe Core.Context) (← getThe Core.State)
    let _ ← ioSeek.asTask
    try
      let delay  := aided_by.delay.get (← getOptions)
      dbgSleep delay.toUInt32 fun _ => do
        let pf ← fetchProof
        let script := pf.script
        if fromBy then
          TryThis.addSuggestion stx (← `(by $script))
        else
          TryThis.addSuggestion stx script
    catch _ =>
      pure ()
  autoStartImplAux (stx: Syntax)
  (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)
  (tacticCode : TSyntax ``tacticSeq)(fromBy: Bool) : TacticM Unit :=
  withMainContext do
    initialSearch stx autoCode fromBy
    let allTacs := getTactics tacticCode
    let mut cumTacs :  Array (TSyntax `tactic) := #[]
    for tacticCode in allTacs do
      evalTactic tacticCode
      if ← isSorry tacticCode then
        return ()
      cumTacs := cumTacs.push tacticCode
      if (← getUnsolvedGoals).isEmpty then
        unless tacticCode.raw.reprint.get!.trim.endsWith "sorry" do
          if fromBy then
            TryThis.addSuggestion stx (← `(by $[$cumTacs]*))
          else
            TryThis.addSuggestion stx (← `(tacticSeq|$[$cumTacs]*))
        return ()
      let ioSeek : IO Unit := runAndCacheIO
        autoCode  (← getMainGoal) (← getMainTarget)
                (← readThe Meta.Context) (← getThe Meta.State )
                (← readThe Core.Context) (← getThe Core.State)
      let _ ← ioSeek.asTask
      try
        let delay  := aided_by.delay.get (← getOptions)
        dbgSleep delay.toUInt32 fun _ => do
          let pf ← fetchProof
          let allTacs ←  appendTactics cumTacs pf.script
          if fromBy then
            TryThis.addSuggestion stx (← `(by $allTacs))
          else
            TryThis.addSuggestion stx allTacs
          return ()
      catch _ =>
        pure ()
  autoStartImplAux' (stx: Syntax)
    (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)(fromBy: Bool) : TacticM Unit :=
    withMainContext do
    initialSearch stx autoCode fromBy
    if (← getUnsolvedGoals).isEmpty then
        return ()
