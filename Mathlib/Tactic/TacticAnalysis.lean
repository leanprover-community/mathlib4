/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import Lean.Util.Heartbeats
import Lean.Server.InfoUtils
import Mathlib.Lean.ContextInfo
import Mathlib.Lean.Elab.Tactic.Meta

/-! # Tactic analysis framework

In this file we define a framework for analyzing sequences of tactics.
This can be used for linting (for instance: report when two `rw` calls can be merged into one),
but it can also be run in a more batch-like mode to report larger potential refactors
(for instance: report when a sequence of three or more tactics can be replaced with `grind`,
without taking more heartbeats than the original proof did).

## Using the framework

The framework runs, but does nothing by default (`set_option linter.tacticAnalysis false`
to turn it off completely). Enable the analysis round `roundName` by enabling its corresponding
option: `set_option linter.tacticAnalysis.roundName true`.

To add a round of analysis called `roundName`, declare an option `linter.tacticAnalysis.roundName`,
make a definition of type `Mathlib.TacticAnalysis.Config` and give the `Config` declaration the
`@[tacticAnalysis linter.tacticAnalysis.roundName]` attribute. Don't forget to enable the option.

## Warning

The `ComplexConfig` interface doesn't feel quite intuitive and flexible yet and should be changed
in the future. Please do not rely on this interface being stable.
-/

open Lean Elab Term Command Linter

/-- The tactic analysis framework hooks into the linter to run analysis rounds on sequences
of tactics.
This can be used for linting, or in a more batch-like mode to report potential refactors.
-/
register_option linter.tacticAnalysis : Bool := {
  defValue := true
  descr := "enable the tactic analysis framework"
}

namespace Mathlib.TacticAnalysis

/-- Stores the configuration for a tactic analysis pass.

This provides the low-level interface into the tactic analysis framework.
-/
structure Config where
  /-- The function that runs this pass. Takes an array of infotree nodes corresponding
  to a sequence of tactics from the source file. Should do all reporting itself,
  for example by `Lean.Linter.logLint`.
  -/
  run : Array (ContextInfo × TacticInfo) → CommandElabM Unit

/-- The internal representation of a tactic analysis pass,
extending `Config` with some declaration meta-information.
-/
structure Pass extends Config where
  /-- The option corresponding to this pass, used to enable it.

  Example: `linter.tacticAnalysis.grindReplacement`.
  -/
  opt : Option (Lean.Option Bool)

/-- Each tactic analysis round is represented by the declaration name for the `Config`. -/
structure Entry where
  /-- The declaration, of type `Config`, that defines this pass. -/
  declName : Name
  /-- The option, of type `Lean.Option Bool`, that controls whether the pass is enabled. -/
  optionName : Name

/-- Read a configuration from a declaration of the right type. -/
def Entry.import (e : Entry) : ImportM Pass := do
  let { env, opts, .. } ← read
  let cfg ← IO.ofExcept <|
    unsafe env.evalConstCheck Config opts ``Config e.declName
  -- This next line can return `none` in the file where the option is declared:
  let opt := (unsafe env.evalConst (Lean.Option Bool) opts e.optionName).toOption
  return { cfg with opt }

instance : Ord Entry where
  compare a b := (@lexOrd _ _ ⟨Lean.Name.cmp⟩ ⟨Lean.Name.cmp⟩).compare (a.1, a.2) (b.1, b.2)

/-- Environment extensions for `tacticAnalysis` declarations -/
initialize tacticAnalysisExt : PersistentEnvExtension Entry (Entry × Pass)
    -- Like `SimplePersistentEnvExtension`, store the locally declared entries separately from all
    -- of the passes. Otherwise we end up re-exporting the entries and spending a lot of time
    -- deduplicating them downstream.
    (List Entry × Array Pass) ←
  registerPersistentEnvExtension {
    mkInitial := pure ([], #[])
    addImportedFn s := do
      let localEntries := []
      let allPasses ← s.flatten.mapM fun e => e.import
      return (localEntries, allPasses)
    addEntryFn := fun (localEntries, allPasses) (entry, pass) =>
      (entry :: localEntries, allPasses.push pass)
    exportEntriesFn := fun (localEntries, _) => localEntries.reverse.toArray
  }

/-- Attribute adding a tactic analysis pass from a `Config` structure. -/
initialize registerBuiltinAttribute {
  name := `tacticAnalysis
  descr := "adds a tacticAnalysis pass"
  applicationTime := .afterCompilation
  add declName stx kind := match stx with
    | `(attr| tacticAnalysis) => do
      throwError m!"tacticAnalysis: missing option name."
    | `(attr| tacticAnalysis $optionName) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'tacticAnalysis', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'tacticAnalysis', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let entry := {
        declName
        optionName := Syntax.getId optionName
      }
      let ext ← entry.import
      setEnv <| tacticAnalysisExt.addEntry env (entry, ext)
    | _ => throwUnsupportedSyntax
}

/-- Parse an infotree to find all the sequences of tactics contained within `stx`.

We consider a sequence here to be a maximal interval of tactics joined by `;` or newlines.
This function returns an array of sequences. For example, a proof of the form:
```
by
  tac1
  · tac2; tac3
  · tac4; tac5
```
would result in three sequences:
* `#[tac1, (· tac2; tac3), (· tac4; tac5)]`
* `#[tac2, tac3]`
* `#[tac4, tac5]`

Similarly, a declaration with multiple `by` blocks results in each of the blocks getting its
own sequence.
-/
def findTacticSeqs (stx : Syntax) (tree : InfoTree) :
    CommandElabM (Array (Array (ContextInfo × TacticInfo))) := do
  let some enclosingRange := stx.getRange? |
    throw (Exception.error stx m!"operating on syntax without range")
  -- Turn the CommandElabM into a surrounding context for traversing the tree.
  let ctx ← read
  let state ← get
  let ctxInfo := { env := state.env, fileMap := ctx.fileMap, ngen := state.ngen }
  let out ← tree.visitM (m := CommandElabM) (ctx? := some ctxInfo)
    (fun _ i _ => do
      if let some range := i.stx.getRange? then
        pure <| enclosingRange.start <= range.start && range.stop <= enclosingRange.stop
      else pure false)
    (fun ctx i _c cs => do
      let relevantChildren := (cs.filterMap id).toArray
      let childTactics := relevantChildren.filterMap Prod.fst
      let childSequences := (relevantChildren.map Prod.snd).flatten
      let stx := i.stx
      if let some (.original _ _ _ _) := stx.getHeadInfo? then
        -- Punctuation: skip this.
        if stx.getKind ∈ [`«;», `Lean.cdotTk, `«]», nullKind, `«by»] then
          return (none, childSequences)
        -- Tactic modifiers: return the children unmodified.
        if stx.getKind ∈ [``Lean.Parser.Tactic.withAnnotateState] then
          return (childTactics[0]?, childSequences)
        -- Tactic sequencing operators: collect all the child tactics into a new sequence.
        if stx.getKind ∈ [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
            ``Lean.Parser.Term.byTactic] then
          return (none, if childTactics.isEmpty then
              childSequences
            else
              childSequences.push childTactics)

        -- Remaining options: plain pieces of syntax.
        -- We discard `childTactics` here, because those are either already picked up by a
        -- sequencing operator, or come from macros.
        if let .ofTacticInfo i := i then
          return ((ctx, i), childSequences)
        return (none, childSequences)
      else
        return (none, childSequences))
  return (out.map Prod.snd).getD #[]

/-- Run the tactic analysis passes from `configs` on the tactic sequences in `stx`,
using `trees` to get the infotrees. -/
def runPasses (configs : Array Pass) (stx : Syntax)
    (trees : PersistentArray InfoTree) : CommandElabM Unit := do
  let opts ← getLinterOptions
  let enabledConfigs := configs.filter fun config =>
    -- This can be `none` in the file where the option is declared.
    if let some opt := config.opt then getLinterValue opt opts else false
  if enabledConfigs.isEmpty then
    return
  for i in trees do
    for seq in (← findTacticSeqs stx i) do
      for config in enabledConfigs do
        config.run seq

/-- A tactic analysis framework.
It is aimed at allowing developers to specify refactoring patterns,
which will be tested against a whole project,
to report proposed changes.

It hooks into the linting system to move through the infotree,
collecting tactic syntax and state to call the passes on.
-/
def tacticAnalysis : Linter where run := withSetOptionIn fun stx => do
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let configs := (tacticAnalysisExt.getState env).2
  let trees := (← getInfoState).substituteLazy.get.trees
  runPasses configs stx trees

initialize addLinter tacticAnalysis

section ComplexConfig

/-!
### Work in progress: `Config` building blocks

In this section we define `ComplexConfig` which is supposed to make it easier to build standard
analysis rounds.

**Work in progress** note: This interface does not feel intuitive yet and might be redesigned.
Please do not rely on it being stable!
-/

/--
The condition is returned from the `.trigger` function to indicate which sublists of a
tactic sequence to test.

The `context` field can be used to accumulate data between different invocations of `.trigger`.
-/
inductive TriggerCondition (ctx : Type _)
  /-- `skip` means that the current tactic and the ones before it will be discarded. -/
  | skip
  /-- `continue` means to accumulate the current tactic, but not yet run the test on it. -/
  | continue (context : ctx)
  /-- `accept` means to run the test on the sequence of `.continue`s up to this `.accept`. -/
  | accept (context : ctx)
deriving BEq

/-- Specifies which analysis steps to take.

The overall design will have three user-supplied components:

  * **trigger** on a piece of syntax (which could contain multiple tactic calls);
  * **test** if a suggested change is indeed an improvement;
  * **tell** the user where changes can be made.
-/
structure ComplexConfig where
  /-- Type returned by the `.test` function. -/
  out : Type
  /-- Type returned by the `.trigger` function. -/
  ctx : Type

  /-- Determines which (sequences of) tactics to analyze.

  `context` is `some ctx` whenever the previous trigger returned `continue ctx`,
  `none` at the start of a tactic sequence or after a `skip`/`accept`.

  If the last returned value is `continue` at the end of the sequence, the framework inserts an
  extra `done` to run the `trigger` on.
  -/
  trigger (context : Option ctx) (currentTactic : Syntax) : TriggerCondition ctx
  /-- Code to run in the context of the tactic, for example an alternative tactic. -/
  test (context : ctx) (goal : MVarId) : MetaM out
  /-- Decides what to report to the user. -/
  tell (stx : Syntax) (originalSubgoals : List MVarId) (originalHeartbeats : Nat)
    (new : out) (newHeartbeats : Nat) : CommandElabM (Option MessageData)

/-- Test the `config` against a sequence of tactics, using the context info and tactic info
from the start of the sequence. -/
def testTacticSeq (config : ComplexConfig) (tacticSeq : Array (TSyntax `tactic))
    (ctxI : ContextInfo) (i : TacticInfo) (ctx : config.ctx) :
    CommandElabM Unit := do
  /- Syntax quotations use the current ref's position info even for nodes which do not usually
  carry position info. We set the ref here to ensure we log messages on the correct range. -/
  withRef (mkNullNode tacticSeq) do
    let stx ← `(tactic| $tacticSeq;*)
    -- TODO: support more than 1 goal. Probably by requiring all tests to succeed in a row
    if let [goal] := i.goalsBefore then
      let (oldGoals, oldHeartbeats) ← withHeartbeats <|
        try
          ctxI.runTacticCode i goal stx
        catch e =>
          logWarning m!"original tactic '{stx}' failed: {e.toMessageData}"
          return [goal]
      let (new, newHeartbeats) ← withHeartbeats <| ctxI.runTactic i goal <| config.test ctx
      if let some msg ← config.tell stx oldGoals oldHeartbeats new newHeartbeats  then
        logWarning msg

/-- Run the `config` against a sequence of tactics, using the `trigger` to determine which
subsequences should be `test`ed. -/
def runPass (config : ComplexConfig) (seq : Array (ContextInfo × TacticInfo)) :
    CommandElabM Unit := do
  let mut acc := none
  let mut firstInfo := none
  let mut tacticSeq := #[]
  for (ctxI, i) in seq do
    if firstInfo.isNone then
      firstInfo := some (ctxI, i)
    let stx : TSyntax `tactic := ⟨i.stx⟩
    tacticSeq := tacticSeq.push stx
    match config.trigger acc stx with
    | .continue ctx =>
      acc := ctx
    | .skip =>
      acc := none
      tacticSeq := #[]
      firstInfo := none
    | .accept ctx =>
      if let some (ctxI, i) := firstInfo then
        testTacticSeq config tacticSeq ctxI i ctx
      else
        logWarningAt stx m!"internal error in tactic analysis: accepted an empty sequence."
      acc := none
  -- Insert a `done` at the end so we can handle a final `.continue` at the end.
  match config.trigger acc (← `(tactic| done)) with
  | .accept ctx =>
    if let some (ctxI, i) := firstInfo then
      testTacticSeq config tacticSeq ctxI i ctx
  | _ => pure ()

/-- Constructor for a `Config` which breaks the pass up into multiple pieces. -/
def Config.ofComplex (config : ComplexConfig) : Config where
  run := runPass config

end ComplexConfig

end Mathlib.TacticAnalysis
