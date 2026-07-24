/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils
public meta import Lean.Meta.Hint

/-!
# The `haveI`/`letI` linter

The tactics and term-mode constructs `haveI` and `letI` differ from `have` and `let` only in
that they *inline* the given value into the term being constructed, instead of binding it
with a `have`/`let` binder. (In Lean 3, `haveI`/`letI` were additionally needed to make the
new hypothesis available to instance resolution; in Lean 4, `have` and `let` register local
instances themselves, so inlining is the only remaining difference. Indeed, in current Lean
core the four constructs share a single elaborator: `haveI` is `have +zeta` and `letI` is
`let +zeta`, so the rest of the proof is elaborated in an identical local context and only
the assembly of the final term differs.)

Inside the proof of a proposition this difference is invisible: proofs are irrelevant, so
nothing can depend on whether a value was inlined into the proof term. Hence `haveI`/`letI`
are never needed when constructing a proof of a proposition, and `have`/`let` should be used
instead.

This linter flags every user-written `haveI` or `letI`, tactic or term, that is used to
construct a proof of a proposition, and offers a "try this" suggestion replacing just the
`haveI`/`letI` keyword with `have`/`let` respectively. Concretely, the linter looks for
`haveI`/`letI` syntax in the source of each command, collects the elaboration information
(`TacticInfo` for the tactic, `TermInfo`/`PartialTermInfo` for the term) recorded for that
syntax, and flags the syntax if some recorded goal (for the tactic) or elaborated term (for
the term) was confirmed to be propositional, and none was confirmed otherwise. In particular
a tactic `haveI` that a combinator such as `<;>` ran against both a data goal and a `Prop`
goal is not flagged, since a single source replacement would also affect the data goal.
Uses whose goal or term is data (for instance in the body of a `def`, or in a tactic block
constructing data inside a proof) are not flagged, and neither are uses in *statements*
(where the term being constructed is the proposition itself, not a proof of it, and
replacing `haveI` with `have` would change the statement) or macro-generated uses.

TODO:
* also lint the do-notation `haveI'`/`letI'` variants, when the term being constructed is a
  proof of a proposition.
-/

meta section

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `haveILetI` linter flags uses of the `haveI` or `letI` tactic or term in a proof of a
proposition. Since proofs are irrelevant, the value-inlining behaviour of `haveI`/`letI` can
have no effect there, and `have`/`let` should be used instead. -/
public register_option linter.style.haveILetI : Bool := {
  defValue := false
  descr := "enable the `haveILetI` linter"
}

namespace Style.haveILetI

/-- A user-written `haveI`/`letI` (tactic or term) found in the source syntax of a command. -/
structure Candidate where
  /-- The `haveI`/`letI` syntax node itself. -/
  node : Syntax
  /-- The `haveI`/`letI` keyword token (the first child of `node`). -/
  kw : Syntax
  /-- `true` if `node` is the tactic, `false` if it is the term. -/
  isTactic : Bool
  /-- The keyword, as a string: `"haveI"` or `"letI"`. -/
  kwStr : String
  /-- The replacement keyword, as a string: `"have"` or `"let"`. -/
  replStr : String
  /-- The source range of `node`. -/
  range : Syntax.Range

/-- If `kind` is one of the four `haveI`/`letI` syntax kinds, return
`(is it the tactic?, its keyword, the suggested replacement keyword)`.
Otherwise, return `none`. -/
def replacement? (kind : SyntaxNodeKind) : Option (Bool × String × String) :=
  if kind == ``Lean.Parser.Tactic.tacticHaveI__ then some (true, "haveI", "have")
  else if kind == ``Lean.Parser.Tactic.tacticLetI__ then some (true, "letI", "let")
  else if kind == ``Lean.Parser.Term.haveI then some (false, "haveI", "have")
  else if kind == ``Lean.Parser.Term.letI then some (false, "letI", "let")
  else none

/-- `candidates stx` returns all `haveI`/`letI` tactics and terms in the source syntax `stx`,
in source order. Only syntax whose keyword token the user actually wrote (with `.original`
source info) is returned, since the linter suggests a source replacement for that token. -/
partial def candidates (stx : Syntax) : Array Candidate :=
  go stx #[]
where
  /-- Auxiliary recursion for `candidates`, accumulating into `acc`. -/
  go (stx : Syntax) (acc : Array Candidate) : Array Candidate := Id.run do
    let .node _ kind args := stx | return acc
    let mut acc := acc
    if let some (isTactic, kwStr, replStr) := replacement? kind then
      if let some kw := args[0]? then
        if kw.getHeadInfo matches .original .. then
          if let some range := stx.getRange? then
            acc := acc.push { node := stx, kw, isTactic, kwStr, replStr, range }
    for arg in args do
      acc := go arg acc
    return acc

/-- `propEvidence ty` reports whether the type `ty` is a proposition: `some true`/`some false`
if this could be determined, and `none` if not. Since `Meta.isProp` merely returns `false`
when the sort of `ty` cannot be computed because of unresolved metavariables — which can
occur in `ty` itself, or only in its sort (for instance when `ty` is a local variable of
type `Sort ?u`) — a negative answer in the presence of such metavariables is downgraded to
`none`. Note that a *universe parameter* in the sort still yields `some false`: a
declaration must be correct at every universe. -/
def propEvidence (ty : Expr) : MetaM (Option Bool) := do
  let ty ← instantiateMVars ty
  if ← Meta.isProp ty then
    return some true
  else if ty.hasExprMVar || ty.hasLevelMVar
      || (← instantiateMVars (← inferType ty)).hasMVar then
    return none
  else
    return some false

/-- `tacticGoalIsProp? ctx i` reports whether the main goal before the tactic recorded in the
`TacticInfo` `i` is a proposition, returning `none` if this could not be determined (there is
no main goal, or the check fails). Goals that are already assigned are skipped, as in
`Lean.Elab.Tactic.getMainGoal`. The check first runs in the metavariable context at tactic
time (`i.mctxBefore`); if that is inconclusive, it is retried in the metavariable context of
`ctx` — which, with `foldInfoOuterCtx` below, is the final context of the surrounding
declaration — where metavariables in the goal's type may since have been resolved. -/
def tacticGoalIsProp? (ctx : ContextInfo) (i : TacticInfo) : CommandElabM (Option Bool) := do
  let some goal := i.goalsBefore.find? fun g =>
      !(i.mctxBefore.eAssignment.contains g) && !(i.mctxBefore.dAssignment.contains g)
    | return none
  let some decl := i.mctxBefore.decls.find? goal | return none
  let ev ← try
      ctx.runMetaM decl.lctx do setMCtx i.mctxBefore; propEvidence decl.type
    catch _ => pure none
  if ev.isSome then return ev
  try
    ctx.runMetaM decl.lctx <| propEvidence decl.type
  catch _ => return none

/-- Fold `f` over all `Info` nodes of the `InfoTree` `t`, each together with the
`ContextInfo` of the nearest enclosing `.context` node. Unlike `InfoTree.foldInfo`, this
does *not* apply `Info.updateContext?` at the inner `Info` nodes: that would hand the infos
inside a tactic block the metavariable context as of the end of their surrounding tactic
(`TacticInfo.mctxAfter`), whereas this linter wants the *final* metavariable context of the
surrounding declaration, in which metavariable assignments made by *later* tactic steps
(for instance in later branches of a `<;>`) are also visible. -/
partial def foldInfoOuterCtx {α : Type} (f : ContextInfo → Info → α → α) (init : α)
    (t : InfoTree) : α :=
  go none init t
where
  /-- Auxiliary recursion for `foldInfoOuterCtx`. -/
  go (ctx? : Option ContextInfo) (acc : α) : InfoTree → α
    | .context i t => go (i.mergeIntoOuter? ctx?) acc t
    | .node i ts => ts.foldl (go ctx?) (if let some ctx := ctx? then f ctx i acc else acc)
    | .hole _ => acc

/-- `termIsProof? ctx lctx expr? expectedType?` reports whether the term recorded in a
`TermInfo` (with elaborated value `expr?`) or `PartialTermInfo` (with `expr? := none`) is a
proof of a proposition, returning `none` if this could not be determined. The type of the
elaborated term is consulted first, then the recorded expected type. -/
def termIsProof? (ctx : ContextInfo) (lctx : LocalContext) (expr? expectedType? : Option Expr) :
    CommandElabM (Option Bool) := do
  try
    ctx.runMetaM lctx do
      if let some e := expr? then
        let ev ← try propEvidence (← inferType (← instantiateMVars e)) catch _ => pure none
        if ev.isSome then
          return ev
      match expectedType? with
      | some ty => try propEvidence ty catch _ => pure none
      | none => return none
  catch _ => return none

@[inherit_doc linter.style.haveILetI]
def haveILetILinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.haveILetI (← Linter.getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless (← getInfoState).enabled do
    return
  let cands := candidates stx
  if cands.isEmpty then
    return
  -- Index the candidates by their source range, in order to look up the elaboration
  -- information recorded for them. (Distinct candidates have distinct ranges: they would
  -- otherwise be distinct syntax nodes starting with the same keyword token.)
  let mut keyOf : Std.HashMap Syntax.Range (Nat × Candidate) := {}
  for h : idx in [0:cands.size] do
    keyOf := keyOf.insert cands[idx].range (idx, cands[idx])
  -- For each candidate, collect all `TacticInfo`s (for the tactic) or
  -- `TermInfo`/`PartialTermInfo`s (for the term) recorded for its syntax. The same
  -- user-written `haveI`/`letI` can be recorded several times, for instance when it is run
  -- on several goals by `all_goals` or `<;>`, or when its elaboration was postponed. We
  -- match by source range *and* syntax kind: macro expansion produces syntax spanning the
  -- same range (for instance, the `haveI` tactic expands to `refine_lift haveI …; ?_`,
  -- which contains the `haveI` *term* at the very same range), and the kind check ensures
  -- that each candidate is only paired with elaborations of its own syntax.
  let mut found : Array (Array (ContextInfo × Info)) := .replicate cands.size #[]
  for t in ← getInfoTrees do
    found := foldInfoOuterCtx (init := found) (t := t) fun ctx info acc => Id.run do
      let some (istx, isTacticInfo) := (match info with
        | .ofTacticInfo i => some (i.stx, true)
        | .ofTermInfo i => some (i.stx, false)
        | .ofPartialTermInfo i => some (i.stx, false)
        | _ => none) | return acc
      let some range := istx.getRange? | return acc
      let some (idx, cand) := keyOf[range]? | return acc
      unless cand.isTactic == isTacticInfo && istx.getKind == cand.node.getKind do
        return acc
      return acc.modify idx (·.push (ctx, info))
  -- Flag a candidate precisely when at least one of its recorded elaborations was confirmed
  -- to be propositional and none was confirmed not to be. Elaborations for which this could
  -- not be determined (for instance a `PartialTermInfo` with no recorded expected type)
  -- neither confirm nor block. In particular, a candidate with no recorded elaboration at
  -- all (e.g. `haveI` inside a syntax quotation) is not flagged, and neither is a tactic
  -- `haveI` that a combinator ran against both a `Prop` goal and a data goal, since the
  -- suggested replacement would also affect the data goal.
  for h : idx in [0:cands.size] do
    let cand := cands[idx]
    let mut confirmed := false
    let mut blocked := false
    for (ctx, info) in found[idx]! do
      if blocked then
        break
      let ev ← match info with
        | .ofTacticInfo i => tacticGoalIsProp? ctx i
        | .ofTermInfo i => termIsProof? ctx i.lctx (some i.expr) i.expectedType?
        | .ofPartialTermInfo i => termIsProof? ctx i.lctx none i.expectedType?
        | _ => pure none
      match ev with
      | some true => confirmed := true
      | some false => blocked := true
      | none => pure ()
    if confirmed && !blocked then
      -- The suggestion replaces just the `haveI`/`letI` keyword token, sidestepping any
      -- pretty-printing or reformatting of the rest of the syntax.
      let sugg : Hint.Suggestion := {
        suggestion := .string cand.replStr
        span? := cand.kw
        toCodeActionTitle? := some fun repl => s!"Replace '{cand.kwStr}' with '{repl}'"
      }
      let hint ← liftCoreM <| MessageData.hint m!"Use '{cand.replStr}' instead:" #[sugg]
        (ref? := cand.kw)
      Linter.logLint linter.style.haveILetI cand.kw
        (m!"'{cand.kwStr}' only differs from '{cand.replStr}' in that it inlines its value \
          into the proof term; in the proof of a proposition this makes no difference." ++ hint)

initialize addLinter haveILetILinter

end Style.haveILetI

end Mathlib.Linter
