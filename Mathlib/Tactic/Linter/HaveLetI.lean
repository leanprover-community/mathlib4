/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Lean.Meta.Hint
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# The `haveI`/`letI` linter

The tactics `haveI` and `letI` differ from `have` and `let` only in that they inline
the given value into the term being constructed, instead of binding it with a
`have`/`let` binder. (In Lean 3, `haveI`/`letI` were additionally needed to make the new
hypothesis available to instance resolution; in Lean 4, `have` and `let` register local
instances themselves, so inlining is the only remaining difference.)

Inside the proof of a proposition this difference is invisible: proofs are irrelevant,
so nothing can depend on whether a value was inlined into the proof term. Hence
`haveI`/`letI` are never needed in tactic proofs of propositions, and `have`/`let`
should be used instead.

This linter flags every use of the `haveI` or `letI` tactic whose main goal is a
proposition.

TODO:
* also lint the term-mode `haveI`/`letI`
-/

meta section

open Lean Elab Meta Parser.Term Tactic Linter

namespace Mathlib.Linter.HaveLetI

/-- The `haveILetI` linter flags uses of the `haveI` or `letI` tactic in a proof of a
proposition. Since proofs are irrelevant, the value-inlining behaviour of `haveI`/`letI`
can have no effect there, and `have`/`let` should be used instead. -/
public register_option linter.style.haveILetI : Bool := {
  defValue := true
  descr := "enable the `haveILetI` linter"
}

/-- Run the `haveI` tactic, with a try this suggestion when the goal is a `Prop`. -/
def runHaveI (tk : Syntax) (c : TSyntax ``letConfig) (d : TSyntax ``letDecl) : TacticM Unit := do
  evalTactic (← `(tactic| haveI $c:letConfig $d:letDecl))
  if getLinterValue linter.style.haveILetI (← getLinterOptions) then
    withMainContext do
    if ← isProp (← getMainTarget) then
      let suggs ← Hint.mkSuggestionsMessage #[{toTryThisSuggestion := "have"}] tk none false
      logWarning m!"Try this: {suggs}\n\n\
        The goal is a proposition, so `have` is preferred over `haveI`.\n\
        The difference between `have` and `haveI` is that `haveI` inlines the value.\n\
        But this is not relevant for proofs because of proof irrelevance."

/-- `haveI` behaves like `have`, but inlines the value instead of producing a `have` term. -/
elab tk:"haveI" c:letConfig d:letDecl : tactic => runHaveI tk c d

/-- Run the `letI` tactic, with a try this suggestion when the goal is a `Prop`. -/
def runLetI (tk : Syntax) (c : TSyntax ``letConfig) (d : TSyntax ``letDecl) : TacticM Unit := do
  evalTactic (← `(tactic| letI $c:letConfig $d:letDecl))
  if getLinterValue linter.style.haveILetI (← getLinterOptions) then
    withMainContext do
    if ← isProp (← getMainTarget) then
      let suggs ← Hint.mkSuggestionsMessage #[{toTryThisSuggestion := "let"}] tk none false
      logWarning m!"Try this: {suggs}\n\n\
        The goal is a proposition, so `let` is preferred over `letI`.\n\
        The difference between `let` and `letI` is that `letI` inlines the value.\n\
        But this is not relevant for proofs because of proof irrelevance."

/-- `letI` behaves like `let`, but inlines the value instead of producing a `let` term. -/
elab tk:"letI" c:letConfig d:letDecl : tactic => runLetI tk c d

end Mathlib.Linter.HaveLetI
