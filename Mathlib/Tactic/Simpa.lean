/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Mario Carneiro
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
    wth?:(withArgs)? using?:(usingArg)? : tactic => do
  let cfg := cfg?.getOptional?
  let disch := disch?.getOptional?
  let only := only?.getOptional?
  let args ← args?.getOptional?.mapM getSimpArgs
  let nGoals := (← getUnsolvedGoals).length
  evalTactic $ ← `(tactic|simp $(cfg)? $(disch)? $[only%$only]? $[[$[$args],*]]?)
  if (← getUnsolvedGoals).length < nGoals then
    throwError "try 'simp' instead of 'simpa'"
  match ← using?.getOptional?.mapM getUsingArg with
  | none   =>
    evalTactic $ ← `(tactic|try simp $(cfg)? $(disch)? $[only%$only]? $[[$[$args],*]]? at this)
    evalTactic $ ← `(tactic|assumption)
  | some e =>
    evalTactic $ ← `(tactic|have h := $e)
    evalTactic $ ← `(tactic|try simp $(cfg)? $(disch)? $[only%$only]? $[[$[$args],*]]? at h)
    evalTactic $ ← `(tactic|exact h)
