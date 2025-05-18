/-
Copyright (c) 2025 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Andreas Gittis
-/
import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Monkeyhammer

If infinitely many monkeys have infinitely many hammers, they can do some damage.

This module defines a command prefix `#monkeyhammer` that monkeys with the tactics
in the command in an attempt to simplify it.

Components:
- A system to run tactics in "super recovery mode". It tries to
-/

namespace Mathlib.Tactic.Monkeyhammer

open Lean Elab Command Parser

/--
Strips all whitespace.
-/
def stripAllWhitespace (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp Syntax.unsetTrailing

-- Tactic.tacticSeqBracketed -> Tactic.tacticSeq1Indented with focus dot
def normTacticBlockKind (stx : Syntax) : Syntax := Unhygienic.run do
  stx.rewriteBottomUpM fun stx =>
    match stx with
    | `(Tactic.tacticSeqBracketed| { $[$tacs:tactic];* }) =>
      if tacs.isEmpty then
        `(Tactic.tacticSeq1Indented| · skip)
      else
        `(Tactic.tacticSeq1Indented| · $[$tacs:tactic]*)
    | _ => pure stx

def isSkipTactic (stx : Syntax) : Bool := stx matches `(tactic| skip)

def ensureFocus (stx : TSyntax `tactic) : TSyntax `tactic :=
  match stx with
  | `(tactic| focus $_:tacticSeq) => stx
  | _ => Unhygienic.run `(tactic| focus $stx:tactic)

/--
Converts all tactic sequences into `Tactic.tacticSeq1Indented`.
Removes semicolons from `tacticSeq1Indented`s and flattens them.
Normalizes parenthesis expressions, re-inserting semicolons.
Eliminates `skip`s in some contexts.
Expands `<;>`s.
-/
partial def normTacticSequences (stx : Syntax) : Syntax :=
  let stx := normTacticBlockKind stx
  Unhygienic.run <| stx.rewriteBottomUpM normStep
where
  flattenTacs (tacs : Array (TSyntax `tactic)) : Array (TSyntax `tactic) :=
    let tacs : Array (TSyntax `tactic) := tacs.flatMap fun (tac : TSyntax `tactic) =>
    match tac with
    | `(Tactic.tacticSeq1Indented| $[$tacs':tactic]*) => tacs'
    | `(Tactic.paren| ($[$tacs':tactic]*)) => tacs'
    | _ => #[tac]
    tacs.filter fun tac => !isSkipTactic tac
  normStep (stx : Syntax) : Unhygienic Syntax := do
    match stx with
    | `(Tactic.tacticSeq1Indented| $[$tacs:tactic]*) =>
      let tacs := flattenTacs tacs
      if tacs.isEmpty then
        `(Tactic.tacticSeq1Indented| skip)
      else
        `(Tactic.tacticSeq1Indented| $[$tacs:tactic]*)
    | `(Tactic.paren| ($[$tacs:tactic]*)) =>
      let tacs := flattenTacs tacs
      if tacs.isEmpty then
        `(tactic| skip)
      else if tacs.size == 1 then
        pure tacs[0]!
      else
        `(Tactic.paren| ($[$tacs:tactic];*))
    | `(tactic| try skip) => `(tactic| skip)
    | `(tactic| all_goals skip) => `(tactic| skip)
    | `(tactic| focus all_goals $tacs:tacticSeq) => `(tactic| focus $tacs:tacticSeq)
    | `(tactic| all_goals focus $tacs:tacticSeq) => `(tactic| all_goals $tacs:tacticSeq)
    | `(tactic| $tac1:tactic <;> $tac2:tactic) =>
      if isSkipTactic tac1 then pure <| ensureFocus tac2
      else if isSkipTactic tac2 then pure <| ensureFocus tac1
      else
        let tacs1 := flattenTacs #[tac1]
        `(tactic|
          focus
            $[$tacs1:tactic]*
            all_goals $tac2:tactic)
    | `(tactic| · · $tacs:tacticSeq) => `(tactic| · $tacs:tacticSeq)
    | `(tactic| · focus $tacs:tacticSeq) => `(tactic| · $tacs:tacticSeq)
    | `(tactic| · try $tacs:tacticSeq) => normStep (← `(tactic| · $tacs:tacticSeq))
    | `(tactic| focus focus $tacs:tacticSeq) => `(tactic| focus $tacs:tacticSeq)
    | `(tactic| focus · $tacs:tacticSeq) => `(tactic| · $tacs:tacticSeq)
    | `(tactic| · skip) => `(tactic| done)
    | _ => pure stx

/--
Replaces each SourceInfo with a unique synthetic position.
This way each syntax node can be uniquely identified.

Side effect: strips all whitespace.
-/
def coordinatizeSyntax (s : Syntax) : Syntax :=
  let rec visit (s : Syntax) : StateM Nat Syntax := do
    let nextId := do
      let c ← modifyGet fun n => (n, n + 1)
      return SourceInfo.synthetic ⟨c⟩ ⟨c⟩
    match s with
    | .node _ kind args =>
      let info ← nextId
      let args ← args.mapM visit
      return .node info kind args
    | _ =>
      let info ← nextId
      return s.setInfo info
  visit s |>.run' 1

abbrev SyntaxCoord := Nat

/--
Gets the coordinate stored in the synthetic SourceInfo.
Panics if the syntax is `Syntax.missing`.
-/
def syntaxCoord (s : Syntax) : SyntaxCoord :=
  match s.getInfo? with
  | some (.synthetic ⟨n⟩ _) => n
  | _ => unreachable!

def modifyAtCoord (s : Syntax) (c : SyntaxCoord) (f : Syntax → Syntax) : Syntax :=
  Id.run <| s.replaceM fun stx => pure <| if syntaxCoord stx = c then some (f stx) else none

def replaceAtCoord (s : Syntax) (c : SyntaxCoord) (r : Syntax) : Syntax :=
  modifyAtCoord s c (fun _ => r)

partial def syntaxForEachM {m : Type → Type} [Monad m]
    (s : Syntax) (f : Syntax → m Unit) :
    m Unit := do
  f s
  match s with
  | .node _ _ args =>
    for i in [0:args.size] do
      syntaxForEachM args[i]! f
  | _ => pure ()

structure CommandSnapshot where
  context : Command.Context
  state : Command.State

def mkCommandSnapshot : CommandElabM CommandSnapshot := do
  return {
    context := { (← read) with snap? := none, cancelTk? := none },
    state := (← get)
  }

/--
Runs the command using the given command snapshot.
Does not modify the current state.
-/
def CommandSnapshot.run {α : Type} (s : CommandSnapshot) (m : CommandElabM α) :
    CommandElabM (α × CommandSnapshot) := do
  let m' := m |>.run s.context |>.run s.state
  let throwUserError {β} (s : String) : CommandElabM β := liftM (m := IO) <| throw <| IO.userError s
  match ← m'.toIO' with
  | Except.error (Exception.error _ msg) => throwUserError (← msg.toString)
  | Except.error (Exception.internal id _) =>
    let name ← id.getName
    throwUserError <| "internal exception #" ++ toString id.idx ++ ", " ++ toString name
  | Except.ok (r, state) => return (r, { s with state })

/--
Tag to use for `monkey_try` successes. Trick: since it is equal to its own declaration name,
it can be referred to using ` ``monkeyTrySuccessTag`.
-/
def monkeyTrySuccessTag : Name := decl_name%
/-- See `monkeyTrySuccessTag`. This one is for failure. -/
def monkeyTryFailureTag : Name := decl_name%

/-- Gives the number of init goals and final goals after removing the shared suffix. -/
def tacticArity (initGoals finalGoals : List MVarId) : Nat × Nat :=
  let rec go (xs ys : List MVarId) : Nat × Nat :=
    match xs, ys with
    | [], ys => (0, ys.length)
    | xs, [] => (xs.length, 0)
    | x :: xs', y :: ys' =>
      if x == y then
        go xs' ys'
      else
        (xs'.length + 1, ys'.length + 1)
  go initGoals.reverse finalGoals.reverse

def mkMonkeyTryTag (n : Name) (coord : Nat) (initGoals finalGoals : List MVarId) : Name :=
  let (inita, finala) := tacticArity initGoals finalGoals
  .num (.num (.num (.num (.num n coord) initGoals.length) finalGoals.length) inita) finala

def isMonkeyTryTag? (tag : Name) : Option (Name × Nat × Nat × Nat × Nat × Nat) :=
  if let .num (.num (.num (.num (.num n c) init) final) inita) finala := tag then
    some (n, c, init, final, inita, finala)
  else
    none

/--
Like `try t`, but records whether or not the tactic succeeded in the message log.
This can be used to detect whether or not the tactic even ran.

This is part of a system for automatically removing unused or always-failing tactics.
-/
elab "monkey_try " t:tactic : tactic => do
  Tactic.withoutRecover do
    let i := syntaxCoord (← getRef)
    let initGoals ← Tactic.getUnsolvedGoals
    try
      -- If there are no goals, fail immediately. We don't want to rely on the tactic to fail.
      guard !initGoals.isEmpty
      Tactic.evalTactic t
      let finalGoals ← Tactic.getUnsolvedGoals
      let tag := mkMonkeyTryTag ``monkeyTrySuccessTag i initGoals finalGoals
      logInfo <| MessageData.tagged tag "monkey_try success"
    catch _ =>
      -- N.B. Tactic try/catch does backtracking.
      let tag := mkMonkeyTryTag ``monkeyTryFailureTag i initGoals initGoals
      logInfo <| MessageData.tagged tag "monkey_try failure"

inductive MonkeyTryResult
  /-- Tactic was never run. (Does not appear in the `getMonkeyTryResults` table, but it should
  be understood to be the default value.) -/
  | skipped
  /-- The tactic always succeeds (maybe it never executes). -/
  | success
  /-- The tactic always fails. -/
  | failure
  /-- The tactic might succeed in one case and fail in another. -/
  | mixed
  deriving Inhabited, Repr

def MonkeyTryResult.merge : MonkeyTryResult → MonkeyTryResult → MonkeyTryResult
  | .skipped, r2 => r2
  | r1, .skipped => r1
  | .success, .success => .success
  | .failure, .failure => .failure
  | _, _ => .mixed

/-- A `MonkeyTryResult` along with the maximum number of goals that appear before and after,
across all executions of the particular tactic. -/
def MonkeyTryResult' := MonkeyTryResult × Nat × Nat × Nat × Nat
deriving Repr

def MonkeyTryResult'.neutral : MonkeyTryResult' := (.skipped, 0, 0, 0, 0)

def MonkeyTryResult'.merge : MonkeyTryResult' → MonkeyTryResult' → MonkeyTryResult'
  | (r1, arities1), (r2, arities2) => (r1.merge r2, max arities1 arities2)

partial def findTag : MessageData → Option Name
  | .withContext _ msg       => findTag msg
  | .withNamingContext _ msg => findTag msg
  | .nest _ msg              => findTag msg
  | .group msg               => findTag msg
  | .compose msg₁ msg₂       => findTag msg₁ <|> findTag msg₂
  | .tagged n _              => some n
  | .trace _ msg msgs        => findTag msg <|> msgs.firstM findTag
  | _                        => none

def getMonkeyTryResults : CommandElabM (Std.HashMap SyntaxCoord MonkeyTryResult') := do
  let msgLog := (← get).messages
  let mut results : Std.HashMap SyntaxCoord MonkeyTryResult' := {}
  for msg in msgLog.unreported do
    if let some tag := findTag msg.data then
      if let some (n,  c, arities) := isMonkeyTryTag? tag then
        if n == ``monkeyTrySuccessTag then
          results := results.alter c (fun r? => (r?.getD .neutral).merge (.success, arities))
        else if n == ``monkeyTryFailureTag then
          results := results.alter c (fun r? => (r?.getD .neutral).merge (.failure, arities))
  return results

def tacticOfTacticSeq (tacs : TSyntax ``Parser.Tactic.tacticSeq) : Unhygienic (TSyntax `tactic) :=
  match tacs with
  | `(tacticSeq| $tac:tactic) => pure tac
  | _ => `(tactic| ($tacs:tacticSeq))

/--
Assuming `s` successfully elaborates, uses the collected `monkey_try` results to remove
the inserted `monkey_try`s.
- `skipped`/`failure` means we can replace `monkey_try tac` with `skip`
- `success` means we can replace `monkey_try tac` with `tac`
- `mixed` means we can replace `monkey_try tac` with `try tac`.

As a bonus, uses the accumulated tactic evaluation information
to eliminate `all_goals`/`focus`/`·`.

Recall that the syntax coordinates are placed on the `monkey_try` tactic itself.
-/
def removeMonkeyTries (results : Std.HashMap SyntaxCoord MonkeyTryResult') (s : Syntax) : Syntax :=
  Unhygienic.run <| s.rewriteBottomUpM fun stx =>
    match stx with
    | `(tactic| monkey_try $tac:tactic) =>
      match results[syntaxCoord stx]?.getD .neutral with
      | (.skipped, _, _, _, _) | (.failure, _, _, _, _) => `(tactic| skip)
      | (.success, initGoals, _finalGoals, initArity, finalArity) =>
        match tac with
        | `(tactic| all_goals $tacs:tacticSeq) =>
          if initGoals == 0 then
            `(tactic| skip)
          else if initGoals == 1 then
            tacticOfTacticSeq tacs
          else
            pure tac
        | `(tactic| focus $tacs:tacticSeq) =>
          if initGoals == 1 then
            tacticOfTacticSeq tacs
          else if initArity == 1 && finalArity == 0 then
            `(tactic| · $tacs:tacticSeq)
          else
            pure tac
        | `(tactic| · $tacs:tacticSeq) =>
          if initGoals == 1 then
            tacticOfTacticSeq tacs
          else
            pure tac
        | _ =>
          pure tac
      | (.mixed, _, _, _, _) => `(tactic| try $tac:tactic)
    | _ => pure stx

/--
Inserts `monkey_try` before every tactic (everything that appears in the `tactic` syntax category).
Exception: replaces `try` with `monkey_try`.

Note: one *must* run `coordinatizeSyntax` on the result before elaborating.
-/
def insertMonkeyTries (env : Environment) (s : Syntax) : Syntax :=
  let cat := (Parser.getCategory (Parser.parserExtension.getState env).categories `tactic).get!
  let tacticKinds := cat.kinds
  Unhygienic.run <| s.rewriteBottomUpM fun stx =>
    if let .node _ kind _ := stx then
      if kind == ``Tactic.tacticSeq1Indented then
        pure stx
      else if tacticKinds.contains kind then
        let stx : TSyntax `tactic := ⟨stx⟩
        match stx with
        | `(tactic| skip) => pure stx
        | `(tactic| try $tac:tactic) => `(tactic| monkey_try $tac:tactic)
        | _ => `(tactic| monkey_try $stx:tactic)
      else
        pure stx
    else
      pure stx

def runCommandWithoutModifyingState {α} (m : CommandElabM α)
    (preserveMessagesOnError := false) :
    CommandElabM (Option α) := do
  let (v?, snap) ← (← mkCommandSnapshot).run do
    withReader (fun ctx => { ctx with suppressElabErrors := false }) do
      -- Clear the messages, disable infotrees
      modify fun st => { st with
          messages := {},
          infoState := { enabled := false } }
      -- Ensure that elaboration is not asynchronous, so we can catch errors in the message log
      modifyScope fun scope => { scope with opts := Elab.async.set scope.opts false }
      try
        let v ← m
        if (← get).messages.hasErrors then throwError "has errors"
        return some v
      catch _ =>
        return none
  if preserveMessagesOnError && v?.isNone then
    modify fun st => { st with
      messages := st.messages ++ snap.state.messages
    }
  return v?

/--
Elaborates the command without modifying the environment or state,
normalizing tactic syntaxes, and letting the monkeys knock out tactics that aren't run.
Returns `none` if there are any elaboration errors.
-/
def elabWithMonkeyTryWithoutModifyingState (cmd : Command) (maxHeartbeats? : Option Nat := none) :
    CommandElabM (Option Command) := do
  let cmd := normTacticSequences cmd
  let cmd := insertMonkeyTries (← getEnv) cmd
  let cmd := coordinatizeSyntax cmd
  -- logInfo m!"with monkey tries\n{cmd}"
  let results? ← runCommandWithoutModifyingState do
    if let some m := maxHeartbeats? then
      modifyScope fun scope => { scope with opts := maxHeartbeats.set scope.opts (m / 1000) }
    elabCommand cmd
    getMonkeyTryResults
  let some results := results? | return none
  -- logInfo m!"num results is {results.size}"
  -- for (c, result) in results do
  --   logInfo m!"result at {c}: {repr result}"
  let cmd' := removeMonkeyTries results cmd
  let cmd' := normTacticSequences cmd'
  return some ⟨cmd'⟩

/-- The coordinate for the replacement, the probability weight, and the syntax replacement. -/
abbrev MonkeyActions := Array (SyntaxCoord × Nat × Unhygienic Syntax)

abbrev MonkeyCollectM := StateRefT MonkeyActions CommandElabM

def addMonkeyActionFor (stx : Syntax) (weight : Nat) (act : Unhygienic Syntax) :
    MonkeyCollectM Unit := do
  modify fun st => st.push (syntaxCoord stx, weight, act)

def collectMonkeyActionsFor (stx : Syntax) : MonkeyCollectM Unit := do
  let env ← getEnv
  let cat := (Parser.getCategory (Parser.parserExtension.getState env).categories `tactic).get!
  let tacticKinds := cat.kinds
  if let .node _ kind _ := stx then
    if tacticKinds.contains kind then

      -- Knock out a tactic
      addMonkeyActionFor stx 1 do `(tactic| skip)

      -- Replace with finishing tactics
      addMonkeyActionFor stx 1 do `(tactic| tauto)
      addMonkeyActionFor stx 1 do `(tactic| linarith)
      addMonkeyActionFor stx 1 do `(tactic| ring)
      addMonkeyActionFor stx 1 do `(tactic| omega)
      addMonkeyActionFor stx 1 do `(tactic| trivial)
      addMonkeyActionFor stx 1 do `(tactic| contradiction)

      -- Replace with other tactics
      addMonkeyActionFor stx 1 do `(tactic| ring_nf)
      addMonkeyActionFor stx 1 do `(tactic| norm_num only)
      addMonkeyActionFor stx 1 do `(tactic| norm_cast)

      if let `(tactic| rw $c:optConfig [$[$rules:rwRule],*] $[$l?:location]?) := stx then
        -- If it's `rw`, try knocking out lemmas, both by deletion and by splitting
        for i in [0:rules.size] do
          addMonkeyActionFor stx 1 do
            let rules' := rules.eraseIdx! i
            `(tactic| rw $c:optConfig [$[$rules':rwRule],*] $[$l?:location]?)
          addMonkeyActionFor stx 1 do
            let rules1 := rules.extract 0 i
            let rules2 := rules.extract (i+1) rules.size
            `(tactic|
              (rw $c:optConfig [$[$rules1:rwRule],*] $[$l?:location]? ;
               rw $c:optConfig [$[$rules2:rwRule],*] $[$l?:location]?))

      if let `(tactic| simp $c:optConfig $[$disch?:discharger]? $[only%$only?]?
                [$[$args],*] $[$l?:location]?) := stx then
        -- If it's `simp`, try knocking out simp lemmas.
        for i in [:args.size] do
          addMonkeyActionFor stx 1 do
            let args' := args.eraseIdx! i
            `(tactic| simp $c:optConfig $[$disch?:discharger]? $[only%$only?]?
                [$[$args'],*] $[$l?:location]?)

      if let `(tactic| linarith $[!%$bang?]? $c:optConfig $[only%$only?]?
                $[[$[$terms?],*]]?) := stx then
        -- If it's `linarith`, try knocking out additional hypotheses
        let terms := terms?.getD #[]
        for i in [:terms.size] do
          addMonkeyActionFor stx 1 do
            let terms' := terms.eraseIdx! i
            `(tactic| linarith $[!%$bang?]? $c:optConfig $[only%$only?]? [$[$terms'],*])
        -- Try removing `!`
        if bang?.isSome then
          addMonkeyActionFor stx 1 do
            `(tactic| linarith $c:optConfig $[only%$only?]? [$[$terms],*])

      if let `(tactic| nlinarith $[!%$bang?]? $c:optConfig $[only%$only?]?
                $[[$[$terms?],*]]?) := stx then
        -- If it's `nlinarith`, try knocking out additional hypotheses
        let terms := terms?.getD #[]
        for i in [:terms.size] do
          addMonkeyActionFor stx 1 do
            let terms' := terms.eraseIdx! i
            `(tactic| linarith $[!%$bang?]? $c:optConfig $[only%$only?]?
                [$[$terms'],*])
        -- Try removing `!`
        if bang?.isSome then
          addMonkeyActionFor stx 1 do
            `(tactic| nlinarith $c:optConfig $[only%$only?]? [$[$terms],*])
        -- Try using `linarith`
        addMonkeyActionFor stx 1 do
          `(tactic| linarith $[!%$bang?]? $c:optConfig $[only%$only?]? [$[$terms],*])

def collectMonkeyActions (stx : Syntax) : MonkeyCollectM Unit := do
  syntaxForEachM stx collectMonkeyActionsFor

def getMonkeyActions (stx : Syntax) : CommandElabM MonkeyActions := do
  let (_, acc) ← collectMonkeyActions stx |>.run #[]
  return acc

structure MonkeyState where
  stepsLeft : Nat
  heartbeatCap : Nat

abbrev MonkeyM := StateRefT MonkeyState CommandElabM

def selectRandomWeighted {α} (arr : Array α) (wt : α → Nat) : IO Nat := do
  let totalWeight := arr.foldl (init := 0) fun acc x => acc + wt x
  let r ← IO.rand 0 (totalWeight - 1)
  let mut acc := 0
  for h : i in [0:arr.size] do
    if r <= acc then
      return i
    acc := acc + wt arr[i]
  return 0

def monkeyWith (cmd : Command) : MonkeyM Command := do
  let mut cmd : Command := cmd
  while (← get).stepsLeft > 0 do
    cmd := ⟨coordinatizeSyntax <| normTacticSequences cmd⟩
    let actions ← getMonkeyActions cmd
    if actions.isEmpty then
      return cmd
    let mut attempted : Std.HashSet Nat := {}
    while (← get).stepsLeft > 0 do
      if attempted.size == actions.size then
        return cmd
      modify fun st => { st with stepsLeft := st.stepsLeft - 1 }
      let i ← selectRandomWeighted actions fun (_, w, _) => w
      if attempted.contains i then
        continue
      attempted := attempted.insert i
      let (c, _, s') := actions[i]!
      let cmd' : Command := ⟨replaceAtCoord cmd c (Unhygienic.run s')⟩
      let mh := (← get).heartbeatCap
      if let some cmd' ← elabWithMonkeyTryWithoutModifyingState cmd' (maxHeartbeats? := mh) then
        cmd := cmd'
        break
  return cmd

/--
Estimates the complexity of a Syntax.
-/
def estimatedSyntaxComplexity (env : Environment) (s : Syntax) : Nat :=
  let cat := (Parser.getCategory (Parser.parserExtension.getState env).categories `tactic).get!
  let tacticKinds := cat.kinds
  let rec visit (acc : Nat) (s : Syntax) : Nat :=
    match s with
    | .node _ kind args =>
      if tacticKinds.contains kind then
        match s with
        | `(tactic| rw $_:optConfig [$[$rules:rwRule],*] $[$_:location]?) =>
          acc + rules.size
        | _ => args.foldl (init := acc + 1) visit
      else
        args.foldl (init := acc) visit
    | _ => acc
  visit 0 s

structure MonkeyHammerConfig where
  -- totalHeartbeats : Nat := 20000000000
  heartbeatCap : Nat := 200000000
  poolSize : Nat := 5
  numRuns : Nat := 20
  stepsPerRun : Nat := 10

--declare_command_config_elab elabMonkeyHammerConfig MonkeyHammerConfig

def monkeyHammer (cmd : Command) (config : MonkeyHammerConfig) :
    CommandElabM (Array Command) := do
  let env ← getEnv
  let cmd : Command := ⟨coordinatizeSyntax <| normTacticSequences cmd⟩
  let cmdCplx := estimatedSyntaxComplexity env cmd
  let mut pool : Array (Nat × Command) :=
    Array.replicate (max 1 config.poolSize) (cmdCplx, cmd)
  for _ in [0:config.numRuns] do
    pool := pool.qsort (fun a b => a.1 < b.1)
    let i ← IO.rand 0 (pool.size - 1)
    assert! i < pool.size
    let (_, cmd') := pool[i]!
    let rst : MonkeyState := {
      stepsLeft := config.stepsPerRun
      heartbeatCap := config.heartbeatCap
    }
    let cmd'' ← monkeyWith cmd' |>.run' rst
    if cmd' != cmd'' then
      let cpl := estimatedSyntaxComplexity env cmd''
      if cpl ≤ pool[pool.size - 1]!.1 * 6/5 then
        pool := pool.set! (pool.size - 1) (cpl, cmd'')
  pool := pool.qsort (fun a b => a.1 < b.1)
  let bestCplx := pool[0]!.1
  let mut results := #[]
  for (cplx', cmd') in pool do
    if cplx' ≤ cmdCplx && cplx' ≤ bestCplx * 6/5 && cmd' != cmd then
      unless results.contains cmd' do
        results := results.push cmd'
  return results

/--
`#monkeyhammer cmd` monkeys with the tactics in `cmd` to try to simplify it.
-/
elab tk:"#monkeyhammer " cmd:command : command => do
  let ref ← getRef
  withRef tk do
    if cmd.raw.hasMissing then
      throwError "monkeyhammer does not apply if there is a parse error"
    -- Ensure the command elaborates, and get the number of heartbeats for a baseline.
    let heartbeats? ←
      runCommandWithoutModifyingState (preserveMessagesOnError := true) do
        Prod.snd <$> withHeartbeats do elabCommand cmd
    let some heartbeats := heartbeats?
      | throwError m!"errors in command"
    -- Allow 10 times the measured heartbeats.
    let heartbeatCap := min (10 * heartbeats + 1) (← Command.liftCoreM getMaxHeartbeats)
    let cmds ← monkeyHammer cmd { heartbeatCap }
    if cmds.isEmpty then
      throwError "Could not improve the command."
    else
      liftTermElabM do
        for cmd in cmds do
          Meta.Tactic.TryThis.addSuggestion tk (origSpan? := ref)
            { suggestion := cmd }

end Mathlib.Tactic.Monkeyhammer

-- #monkeyhammer
-- theorem baz (p : Prop) : p → p := by
--   focus tauto <;> tauto <;> tauto
--   -- try simp at x
--   -- try omega
-- --  monkey_try { intro }
--   -- exact id


-- #monkeyhammer
-- example (p : Prop) : p → p := by
-- --  monkey_try { intro }
--   -- fail "hi"
--   exact id


-- #monkeyhammer
-- theorem my_great_theorem (p : Prop) : p → p := by
--   let x := 37; -- comment
--   let a := 21
--   skip <;> simp <;> skip

-- example (n m : Nat) : n * m + 1 = 1 + m * n := by ring_nf
