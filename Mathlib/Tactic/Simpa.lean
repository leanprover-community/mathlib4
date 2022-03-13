/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
import Lean
import Mathlib.Tactic.Core

namespace Mathlib.Tactic

open Lean Parser.Tactic Elab.Tactic

syntax simpArgs := " [" simpArg,+ "] "
syntax withStx  := " with " (colGt ident)+
syntax usingStx := " using " term

def mkSimpArgs' (optStx : Option Syntax) : TacticM (Array Syntax) :=
  match optStx with
  | none     => default
  | some stx => match stx with
    | `(simpArgs|[$args,*]) => pure $ args.getElems
    | _                     => Elab.throwUnsupportedSyntax

/--
This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic. -/
elab (name := simpa) "simpa " cfg?:(config)? disch?:(discharger)?
    only?:&" only "? args?:(simpArgs)?
    wth?:(withStx)? using?:(usingStx)? : tactic => do
  let cfg := cfg?.getOptional?
  let disch := disch?.getOptional?
  let only := only?.getOptional?
  let args ← mkSimpArgs' args?.getOptional?
  let nGoals := (← getUnsolvedGoals).length
  if args.size = 0 then
    evalTactic (← `(tactic|simp $(cfg)? $(disch)? $[only%$only]?))
  else
    evalTactic (← `(tactic|simp $(cfg)? $(disch)? $[only%$only]? [$[$args],*]))
  if (← getUnsolvedGoals).length < nGoals then
    throwError "try 'simp' instead of 'simpa'"
  match using?.getOptional? with
  | none   => pure ()
  | some u => match u with
    | `(usingStx|using $e) => evalTactic (← `(tactic|have := $e))
    | _                    => Elab.throwUnsupportedSyntax
  if args.size = 0 then
    evalTactic (← `(tactic|try simp $(cfg)? $(disch)? $[only%$only]? at this))
  else
    evalTactic (← `(tactic|try simp $(cfg)? $(disch)? $[only%$only]? [$[$args],*] at this))
  evalTactic (← `(tactic|assumption))

example (p : Nat → Prop) (h : p (1 + 0)) : p 1 := by simpa [h]

example (p : Nat → Prop) (h : p (1 + 0)) : p 1 := by simpa

example (p : Nat → Prop) (h : p (1 + 0)) : p 1 := by simpa using h

example (p : Nat → Prop) (h : p (1 + 0)) : p 1 := by simpa only [h]

example (p : Nat → Prop) (h : p (1 + 0)) : p 1 := by simpa only using h

example (p : Prop) (w : p): p := by simpa only [xx] --??

def v (a : Nat) : List Nat := [a]

example : v a = [a] := by simpa only [v]
