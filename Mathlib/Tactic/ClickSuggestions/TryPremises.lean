/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.FindPremises
meta import Mathlib.Tactic.ClickSuggestions.FindPremises

/-!
# generating lemma suggestions, given the the shortlist of candidate lemmas
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean ProofWidgets Jsx

/-- An array of candidate lemmas, corresponding to a single section. -/
inductive Candidates where
  /-- A `rw` suggestion section. -/
  | rw (i : RwInfo) (arr : Array RwLemma)
  /-- A `grw` suggestion section. -/
  | grw (i : GrwInfo) (arr : Array GrwLemma)
  /-- An `apply` suggestion section. -/
  | app (arr : Array ApplyLemma)
  /-- An `apply at` suggestion section. -/
  | appAt (arr : Array ApplyAtLemma)

local instance {α β cmp} [Append β] : Append (Std.TreeMap α β cmp) :=
  ⟨.mergeWith fun _ ↦ (· ++ ·)⟩

open Meta.RefinedDiscrTree in
/-- Combine the results of looking up in various discrimination trees into an Array
of sections of candidates, where each section corresponds to one kind of match with the
discrimination tree. -/
@[specialize]
def getCandidatesAux (rwInfo : RwInfo) (gpos : Array GrwPos) (reportProgress : String → BaseIO Unit)
    (rw : Expr → MetaM (MatchResult RwLemma)) (grw : Expr → MetaM (MatchResult GrwLemma))
    (app : Expr → MetaM (MatchResult ApplyLemma)) (appAt : Expr → MetaM (MatchResult ApplyAtLemma))
    : ClickSuggestionsM (Array Candidates) := do
  let mut cands : Std.TreeMap Nat (Array Candidates) := {}
  /- The order in which we show the suggestions for the same pattern for different tactics
  depends on the following insertion order.
  We choose the order `grw` => `rw` => `apply(at)`. -/
  if !gpos.isEmpty then
    reportProgress "grw"
    let grwInfo := { rwInfo with gpos }
    cands := cands ++ (← grw rwInfo.subExpr).elts.map fun _ ↦ (·.map (.grw grwInfo))
  reportProgress "rw"
  let mut rwInfo := rwInfo
  repeat
    /- TODO: we are passing the same `rwKind` to each of these nested applications, but it is
    certainly possible that the correct `rwKind` is not the same for all of these.
    Though this edge case is probably very rare. -/
    cands := cands ++ (← rw rwInfo.subExpr).elts.map fun _ ↦ (·.map (.rw rwInfo))
    let .app f _ := rwInfo.subExpr | break
    rwInfo := { rwInfo with subExpr := f, pos := rwInfo.pos.pushAppFn }
  if (← read).pos == .root then
    if (← read).hyp?.isSome then
      reportProgress "apply at"
      cands := cands ++ (← appAt rwInfo.rootExpr).elts.map fun _ ↦ (·.map .appAt)
    else
      reportProgress "apply"
      cands := cands ++ (← app rwInfo.rootExpr).elts.map fun _ ↦ (·.map .app)
  return cands.foldr (init := #[]) fun _ val acc ↦ acc ++ val

/-- Get the candidate theorems from imported files. -/
@[specialize]
def getImportCandidates (rwInfo : RwInfo) (gpos : Array GrwPos)
    (reportProgress : String → BaseIO Unit) :
    ClickSuggestionsM (Array Candidates) :=
  getCandidatesAux rwInfo gpos reportProgress
    (getImportMatches rwRef) (getImportMatches grwRef)
    (getImportMatches appRef) (getImportMatches appAtRef)

/-- Get the candidate theorems from `pres`.
Used for current file declarations and local hypotheses -/
def getCandidates (rwInfo : RwInfo) (gpos : Array GrwPos)
    (pres : PreDiscrTrees) :
    ClickSuggestionsM (Array Candidates) :=
  getCandidatesAux rwInfo gpos (fun _ ↦ pure ())
    (getMatches pres.rw.toRefinedDiscrTree) (getMatches pres.grw.toRefinedDiscrTree)
    (getMatches pres.app.toRefinedDiscrTree) (getMatches pres.appAt.toRefinedDiscrTree)

/-- Run `f` on the results of all tasks in the array of tasks, in an arbitrary order.

TODO?: use Lean's `Mutex` to avoid the polling loop? -/
@[specialize]
private partial def foldTasksM {α β} (tasks : Array (Task β)) (init : α) (f : α → β → MetaM α) :
    MetaM α := do
  if tasks.isEmpty then return init
  Core.checkInterrupted
  if ← (tasks.anyM IO.hasFinished : BaseIO _) then
    let (a, tasks) ← tasks.foldlM (init := (init, #[])) fun (a, tasks) task ↦ do
      if ← IO.hasFinished task then
        return (← f a task.get, tasks)
      else
        return (a, tasks.push task)
    foldTasksM tasks a f
  else
    IO.sleep 10
    foldTasksM tasks init f

/-- Spawn tasks for the given candidate premises and
return an HTML that shows the incoming results -/
def runSuggestions (kind : SectionKind) (assignableMVars : Array Expr) :
    Candidates → ClickSuggestionsM Html
  | .rw info arr => go "rw" (·.isDuplicate ·) arr (·.name) (·.try info assignableMVars)
  | .grw info arr => go "grw" (·.isDuplicate ·) arr (·.name) (·.try info assignableMVars)
  | .app arr => go "apply" (·.isDuplicate ·) arr (·.name) (·.try assignableMVars)
  | .appAt arr => go "apply at" (·.isDuplicate ·) arr (·.name) (·.try assignableMVars)
where
  @[specialize]
  go {α β} [Ord α] [Inhabited α] (tactic : String) (isDup : α → α → MetaM Bool)
      (candidates : Array β) (premise : β → Premise)
      (mkSuggestion : β → ClickSuggestionsM (Result α)) : ClickSuggestionsM Html := do
    let (html, token) ← mkRefreshComponent
    let tasks ← candidates.mapM fun lem ↦ spawnTask (premise lem) (mkSuggestion lem)
    discard <| BaseIO.asTask (prio := .dedicated) <| (← saveCtxM <| trackingComputation tactic do
      discard <| foldTasksM tasks ({} : SectionState α) fun s ↦ fun
        | .ok (some res) => do
          let s ← s.insertResult res isDup
          token.updateLazy (renderSection tactic kind s)
          return s
        | .ok none => pure s
        | .error e => do
          let s := { s with errors := s.errors.push e }
          token.updateLazy (renderSection tactic kind s)
          return s
      ).catchExceptions fun ex ↦ do
        if let .internal ex := ex then
          if ex == interruptExceptionId then
            return
        (panic! s!"Error when processing {tactic}: {← ex.toMessageData.toString}")
    return html

open Meta in
/-- Return the expression that we need to rewrite into to solving the goal with `rfl`. -/
def findRflTarget? (root subExpr : Expr) (rwKind : RwKind) : ClickSuggestionsM (Option Expr) := do
  if (← read).hyp?.isSome then return none
  -- If the expression has bound variables, we suggest `simp_rw` instead of `rw`,
  -- which does not attempt to close the goal with `rfl`.
  if rwKind matches .hasBVars then return none
  let pos := (← read).pos
  let subExpr' ← mkFreshExprMVar (← inferType subExpr)
  let root' ← replaceSubexpr (fun _ ↦ pure subExpr') pos root
  try
    (← mkFreshExprMVar root').mvarId!.applyRfl
    return some (← instantiateMVars subExpr')
  catch _ =>
    return none

/-- Compute the library rearch suggestions. This uses `token` to incrementally update the output. -/
public def librarySearchSuggestions (rootExpr subExpr : Expr) (lctx : LocalContext)
    (rwKind : RwKind) (parentDecl? : Option Name)
    (token : RefreshToken) : ClickSuggestionsM Unit := do
  Core.checkInterrupted
  let mut sections := #[]

  let pos := (← read).pos
  let fvarId? := (← read).hyp?
  let gpos ← getGrwPos? rootExpr subExpr pos fvarId?.isSome
  let rflTarget? ← Meta.withLCtx lctx {} <| findRflTarget? rootExpr subExpr rwKind
  let rwInfo := { rootExpr, subExpr, rflTarget?, pos, rwKind }
  let assignableMVars := Array.map Expr.mvar <| ←
    (subExpr.collectMVars {}).result.filterM (not <$> ·.isReadOnlyOrSyntheticOpaque)
  let choice : Choice := {
    rw := true
    grw := !gpos.isEmpty
    app := pos == .root && fvarId?.isNone
    appAt := pos == .root && fvarId?.isSome
  }

  Core.checkInterrupted
  token.update <div> loading local hypotheses ⏳️ </div>
  let pres ← computeLCtxDiscrTrees choice lctx fvarId?
  Core.checkInterrupted
  for cand in ← getCandidates rwInfo gpos pres do
    sections := sections.push (← runSuggestions .hyp assignableMVars cand)

  Core.checkInterrupted
  token.update <div>
    {.element "div" #[] sections}
    <div> loading theorem in the current file ⏳️ </div>
    </div>
  let pres ← computeModuleDiscrTrees choice parentDecl?
  Core.checkInterrupted
  for cand in ← getCandidates rwInfo gpos pres do
    sections := sections.push (← runSuggestions .currFile assignableMVars cand)

  Core.checkInterrupted
  token.update <div>
    {.element "div" #[] sections}
    <div> initializing discrimination trees ⏳️ </div>
    </div>
  computeImportDiscrTrees choice
  Core.checkInterrupted
  let reportProgress (tac : String) :=
    token.update <div>
      {.element "div" #[] sections}
      <div> {.text s!"loading imported `{tac}` theorems ⏳️"} </div>
      </div>
  for cand in ← getImportCandidates rwInfo gpos reportProgress do
    sections := sections.push (← runSuggestions .imported assignableMVars cand)

  token.update <| .element "div" #[] sections
  unless sections.isEmpty do
    markProgress

end Mathlib.Tactic.ClickSuggestions
