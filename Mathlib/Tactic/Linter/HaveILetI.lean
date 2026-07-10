/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils

/-!
# The `haveI`/`letI` linter

The tactics `haveI` and `letI` differ from `have` and `let` only in that they *inline*
the given value into the term being constructed, instead of binding it with a
`have`/`let` binder. (In Lean 3, `haveI`/`letI` were additionally needed to make the new
hypothesis available to instance resolution; in Lean 4, `have` and `let` register local
instances themselves, so inlining is the only remaining difference. Indeed, in current
Lean core the four tactics share a single elaborator: `haveI` is `have +zeta` and `letI`
is `let +zeta`, so the rest of the proof is elaborated in an identical local context and
only the assembly of the final term differs.)

Inside the proof of a proposition this difference is invisible: proofs are irrelevant,
so nothing can depend on whether a value was inlined into the proof term. Hence
`haveI`/`letI` are never needed in tactic proofs of propositions, and `have`/`let`
should be used instead.

This linter flags every use of the `haveI` or `letI` *tactic* whose main goal is a
proposition. Uses whose goal is data (for instance in the body of a `def`, or in a
tactic block constructing data inside a proof) are not flagged, and neither are uses
in theorem *statements* or in term-mode definition bodies, where `haveI`/`letI` are
meaningful.

TODO:
* also lint the term-mode `haveI`/`letI` (including their use inside `exact`/`refine`
  terms in tactic proofs, currently the main source of unflagged pointless uses) and
  the do-notation `haveI'`/`letI'` variants, when the term being constructed is a
  proof of a proposition.
-/

meta section

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `haveILetI` linter flags uses of the `haveI` or `letI` tactic in a proof of a
proposition. Since proofs are irrelevant, the value-inlining behaviour of `haveI`/`letI`
can have no effect there, and `have`/`let` should be used instead. -/
public register_option linter.style.haveILetI : Bool := {
  defValue := false
  descr := "enable the `haveILetI` linter"
}

namespace Style.haveILetI

/-- If `stx` is a `haveI` or `letI` tactic call, return the pair
`(its keyword, the suggested replacement keyword)`. Otherwise, return `none`. -/
def replacement? : Syntax → Option (String × String)
  | .node _ ``Lean.Parser.Tactic.tacticHaveI__ _ => some ("haveI", "have")
  | .node _ ``Lean.Parser.Tactic.tacticLetI__ _ => some ("letI", "let")
  | _ => none

/-- `candidates t` returns the tactic-info nodes of the `InfoTree` `t` corresponding to
user-written `haveI`/`letI` tactic calls, together with the `ContextInfo` needed to
inspect their goals and the two keywords returned by `replacement?`. -/
def candidates (t : InfoTree) : Array (ContextInfo × TacticInfo × String × String) :=
  t.foldInfo (init := #[]) fun ctx info args => Id.run do
    let .ofTacticInfo i := info | return args
    -- Only consider syntax that the user actually wrote.
    let .original .. := i.stx.getHeadInfo | return args
    let some (kw, repl) := replacement? i.stx | return args
    return args.push (ctx, i, kw, repl)

/-- `mainGoalIsProp ctx i` reports whether the main goal before the tactic recorded in
the `TacticInfo` `i` is a proposition. Goals that are already assigned are skipped, as
in `Lean.Elab.Tactic.getMainGoal`. If there is no main goal, or if the check fails,
it conservatively returns `false`. -/
def mainGoalIsProp (ctx : ContextInfo) (i : TacticInfo) : CommandElabM Bool := do
  let some goal := i.goalsBefore.find? fun g =>
      !(i.mctxBefore.eAssignment.contains g) && !(i.mctxBefore.dAssignment.contains g)
    | return false
  let some decl := i.mctxBefore.decls.find? goal | return false
  ctx.runMetaM decl.lctx do
    setMCtx i.mctxBefore
    -- On failure (or when the goal's type is a not-yet-assigned metavariable), we
    -- conservatively do not flag.
    try Meta.isProp (← instantiateMVars decl.type)
    catch _ => return false

@[inherit_doc linter.style.haveILetI]
def haveILetILinter : Linter where run := withSetOptionIn fun _stx => do
  unless Linter.getLinterValue linter.style.haveILetI (← Linter.getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless (← getInfoState).enabled do
    return
  -- The same user-written tactic call can be recorded several times in the info trees,
  -- for instance when it is run on several goals by `all_goals` or `<;>`; only report
  -- it once.
  let mut seen : Std.HashSet (Option String.Pos.Raw × Option String.Pos.Raw) := {}
  for t in ← getInfoTrees do
    for (ctx, i, kw, repl) in candidates t do
      let range := (i.stx.getPos?, i.stx.getTailPos?)
      unless seen.contains range do
        if ← mainGoalIsProp ctx i then
          -- A range is inserted into `seen` only when it is reported: a negative
          -- result must not be cached, since under multi-goal combinators the same
          -- syntax can first run against a data goal and later against a `Prop` goal.
          seen := seen.insert range
          Linter.logLint linter.style.haveILetI i.stx
            m!"'{kw}' only differs from '{repl}' in that it inlines its value into the \
            proof term; in the proof of a proposition this makes no difference, \
            so please use '{repl}' instead."

initialize addLinter haveILetILinter

end Style.haveILetI

end Mathlib.Linter
