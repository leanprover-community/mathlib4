/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
import Mathlib.Tactic.Core

namespace Mathlib.Tactic

open  Lean.Parser.Tactic Lean.Elab.Tactic

-- move these?
syntax simpArgs' := ((" only ")? " [" simpArg,+ "] ")?
syntax withStx   := (" with " (colGt ident)+)?
syntax usingStx  := (" using " term)?

/--
This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ...] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ...]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic. -/
elab (name := simpa) "simpa" cfg?:(config)? disch?:(discharger)?
    args?:simpArgs' wth?:withStx using?:usingStx : tactic => do
  let cfg := cfg?.getOptional?
  let args := args?.getOptional?
  let nGoals := (← getUnsolvedGoals).length
  try evalTactic (← `(tactic|simp $(cfg)? $(disch?.getOptional?)? $(args)?))
  catch | _ => throwError "couldn't simplify the goal"
  if (← getUnsolvedGoals).length < nGoals then
    throwError "try 'simp' instead of 'simpa'"
  match wth? with
  | `(withStx| $[with $wth*]?) =>
    match wth with
    | none => pure ()
    | some wth =>
      for w in wth do
        try evalTactic (← `(tactic|intro $w))
        catch | _ => throwError "couldn't introduce {w}"
  | _ => Lean.Elab.throwUnsupportedSyntax
  match using? with
  | `(usingStx|$[using $t:term]?) =>
    try
      match t with
      | none =>
        evalTactic (← `(tactic|try simp $(cfg)? $(args)? at this))
        evalTactic (← `(tactic|assumption))
      | some t =>
        evalTactic (← `(tactic|exact $t))
    catch | _ => throwError "'simpa' couldn't close the goal"
  | _ => Lean.Elab.throwUnsupportedSyntax
