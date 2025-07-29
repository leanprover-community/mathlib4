import Lean.Elab.Term
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Meta
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
import Batteries.CodeAction -- to enable the hole code action
import Lean.Meta.Tactic.Grind.Main
import Lean.Util.Heartbeats
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.MinImports

open Lean Elab Term Command Linter

register_option linter.tactic_analysis : Bool := {
  defValue := true
  descr := "enable transformations for tactics"
}

namespace Lean.Elab.ContextInfo

variable {α}

/-- Embeds a `CoreM` action in `CommandElabM` by supplying the information stored in `info`.

Copy of `ContextInfo.runCoreM` that looks up relevant information in the `CommandElabM` context.
-/
def runCoreM' (info : ContextInfo) (x : CoreM α) : CommandElabM α := do
  -- We assume that this function is used only outside elaboration, mostly in the language server,
  -- and so we can and should provide access to information regardless whether it is exported.
  let env := info.env.setExporting false
  let ctx ← read
  /-
    We must execute `x` using the `ngen` stored in `info`. Otherwise, we may create `MVarId`s and `FVarId`s that
    have been used in `lctx` and `info.mctx`.
    Similarly, we need to pass in a `namePrefix` because otherwise we can't create auxiliary definitions.
  -/
  let (x, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen, auxDeclNGen := { namePrefix := info.parentDecl?.getD .anonymous } }
  -- Migrate logs back to the main context.
  modify fun state => { state with
    messages := state.messages ++ newState.messages,
    traceState.traces := state.traceState.traces ++ newState.traceState.traces }
  return x

def runMetaM' (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  (·.1) <$> info.runCoreM' (Lean.Meta.MetaM.run (ctx := { lctx := lctx }) (s := { mctx := info.mctx }) <|
    -- Update the local instances, otherwise typeclass search would fail to see anything in the local context.
    Meta.withLocalInstances (lctx.decls.toList.filterMap id) <| x)

/-- Run a tactic computation in the context of an infotree node. -/
def runTactic (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (x : MVarId → MetaM α) : CommandElabM α := do
  if i.goalsBefore.all fun g => g != goal then panic!"ContextInfo.runTactic: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaM' lctx <| do
    -- Make a fresh metavariable because the original goal is already assigned.
    let type ← goal.getType
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
    x goal.mvarId!

end Lean.Elab.ContextInfo

namespace TacticAnalysis

inductive TriggerCondition (ctx : Type _)
  | skip
  | continue (context : ctx)
  | accept (context : ctx)
deriving BEq

/-- Specifies which analysis steps to take. -/
structure Config (out ctx) where
  /-- Which (sequences of) tactics to analyze. -/
  trigger (context : Option ctx) (currentTactic : Syntax) : TriggerCondition ctx
  /-- Code to run in the context of the tactic, for example an alternative tactic. -/
  test (context : ctx) (goal : MVarId) : MetaM out
  /-- Decides what to report to the user. -/
  tell (stx : Syntax) (original : List MVarId × Nat) (new : out × Nat) : Option MessageData

def findTacticSeqs (stx : Syntax) (tree : InfoTree) : CommandElabM (Array (Array (ContextInfo × TacticInfo))) := do
  let some enclosingRange := stx.getRange? | throw (Exception.error stx m!"operating on syntax without range")
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
        if stx.getKind ∈ [`«;», `Lean.cdotTk, `«]», nullKind] then
          return (none, childSequences)
        -- Tactic modifiers: return the children unmodified.
        if stx.getKind ∈ [``Lean.Parser.Tactic.withAnnotateState] then
          return (childTactics[0]?, childSequences)
        -- Tactic sequencing operators: collect all the child tactics into a new sequence.
        if stx.getKind ∈ [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Term.byTactic] then
          return (none, if childTactics.isEmpty then childSequences else childSequences.push childTactics)
        if let .ofTacticInfo i := i then
          /-
          if !childTactics.isEmpty then
            logInfoAt stx m!"at {i.stx.getKind}: discarding child tactics {childTactics.map fun i => i.2.stx.getKind}"
          -/
          return ((ctx, i), childSequences)
        /-
        if !childTactics.isEmpty then
          logInfoAt stx m!"at {i.stx.getKind}: discarding child tactics {childTactics.map fun i => i.2.stx.getKind}"
        -/
        return (none, childSequences)
      else
        return (none, childSequences))
  return (out.map Prod.snd).getD #[]

def filterTactics {out ctx} (config : Config out ctx) (seq : Array (ContextInfo × TacticInfo)) : CommandElabM Unit := do
  let mut acc := none
  let mut firstInfo := none
  for (ctxI, i) in seq do
    if firstInfo.isNone then
      firstInfo := some (ctxI, i)
    let stx := i.stx
    match config.trigger acc stx with
    | .continue ctx =>
      acc := ctx
    | .skip =>
      acc := none
      firstInfo := none
    | .accept ctx =>
      if let some (ctxI, i) := firstInfo then
        if let [goal] := i.goalsBefore then -- TODO: support more than 1 goal. Probably by requiring all tests to succeed in a row
          let old ← withHeartbeats <| ctxI.runTactic i goal fun goal => do
            try
              Lean.Elab.runTactic goal stx
            catch e =>
              logWarningAt stx m!"original tactic '{stx}' failed: {e.toMessageData}"
              return ([goal], {})
          let new ← withHeartbeats <| ctxI.runTactic i goal <| config.test ctx
          if let some msg := config.tell stx (old.1.1, old.2) new then
            Linter.logLint linter.tactic_analysis stx msg
      else
        logWarningAt stx m!"internal error in tactic analysis: accepted an empty sequence."

def filterTacticsList {out ctx} (config : Config out ctx) (stx : Syntax)
    (trees : PersistentArray InfoTree) : CommandElabM Unit :=
  for i in trees do
    let seqs ← findTacticSeqs stx i
    -- logInfoAt stx m!"Sequences: {seqs.map (· |>.map (· |>.2.stx.getKind))}"
    for seq in seqs do
      filterTactics config seq

/-- Run a tactic, returning any new messages rather than adding them to the message log.

Copied from `Mathlib.Tactic.Hint.withMessageLog`.
-/
def withMessageLog (t : MetaM Unit) : MetaM MessageLog := do
  let initMsgs ← modifyGetThe Core.State fun st => (st.messages, { st with messages := {} })
  t
  modifyGetThe Core.State fun st => (st.messages, { st with messages := initMsgs })

def grindReplacement : Config (List MVarId × MessageData) Syntax where
  trigger _ stx := if
      stx.getKind ∈
        [`Mathlib.Tactic.linarith, `Lean.Parser.Tactic.omega, `Mathlib.Tactic.RingNF.ring]
    then .accept stx else .skip
  test stx goal := withOptions (fun opts => opts.set `grind.warning false) do
    let tac ← `(tactic| grind)
    try
      let (goals, _) ← Lean.Elab.runTactic goal tac
      return (goals, m!"")
    catch e => -- Grind throws an error if it fails.
      let name ← mkAuxDeclName `extracted
      let ((sig, _, modules), _) ← (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run
      let imports := modules.toList.map (s!"import {·}")
      return ([goal], m!"{"\n".intercalate imports}\n\ntheorem {sig} := by\n  fail_if_success grind\n  {stx}")
  tell stx old new :=
    if new.1.1 != [] then
      m!"'grind' failed where '{stx}' succeeded. Counterexample:\n{new.1.2}"
    /-
    else
      if old.2 * 2 < new.2 then
        return m!"'grind' is slower than '{stx}': {new.2 / 1000} versus {old.2 / 1000} heartbeats"
    -/
    else none

/-- A tactic analysis framework.
It is aimed at allowing developers to specify refactoring patterns,
which will be tested against a whole project,
to report proposed changes.

The overall design will have three user-supplied components:

  * **trigger** on a piece of syntax (which could contain multiple tactic calls);
  * **test** if a suggested change is indeed an improvement;
  * **tell** the user where changes can be made.

It hooks into the linting system to move through the infotree,
collecting tactic syntax and state to pass to the three Ts.
-/
def tactic_analysis : Linter where run := withSetOptionIn fun stx => do
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  /-
  let some convs := Parser.ParserCategory.kinds <$> cats.find? `conv
    | return
  -/
  let trees ← getInfoTrees
  filterTacticsList grindReplacement stx trees

initialize addLinter tactic_analysis

end TacticAnalysis
