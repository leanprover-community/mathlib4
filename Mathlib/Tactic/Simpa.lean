/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
import Lean
import Mathlib.Tactic.Core

namespace Mathlib.Tactic

open Lean Parser.Tactic Elab.Tactic

/--
This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic.

#TODO: implement `with ⋯` behavior
-/
elab "simpa " cfg?:(config)? disch?:(discharger)?
    only?:&" only "? args?:(simpArgs)?
    wth?:(withStx)? using?:(usingStx)? : tactic => do
  let cfg := cfg?.getOptional?
  let disch := disch?.getOptional?
  let only := only?.getOptional?
  let args ← getSimpArgs args?.getOptional?
  let argsSizeIsZero : Bool := args.size = 0
  let nGoals := (← getUnsolvedGoals).length
  if argsSizeIsZero then
    evalTacticM `(tactic|simp $(cfg)? $(disch)? $[only%$only]?)
  else
    evalTacticM `(tactic|simp $(cfg)? $(disch)? $[only%$only]? [$[$args],*])
  if (← getUnsolvedGoals).length < nGoals then
    throwError "try 'simp' instead of 'simpa'"
  let simpAtThisStx := if argsSizeIsZero
    then `(tactic|try simp $(cfg)? $(disch)? $[only%$only]? at this)
    else `(tactic|try simp $(cfg)? $(disch)? $[only%$only]? [$[$args],*] at this)
  match using?.getOptional? with
  | none   =>
    evalTacticM simpAtThisStx
    evalTacticM `(tactic|assumption)
  | some u => match u with
    | `(usingStx|using $e) =>
      evalTacticM `(tactic|have := $e)
      evalTacticM simpAtThisStx
      evalTacticM `(tactic|exact this)
    | _                    => Elab.throwUnsupportedSyntax
