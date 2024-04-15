/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "generic" linter

The "generic" linter takes as input a function
`unwanted : Syntax → Array Syntax` that returns the syntax nodes of an input syntax that
should be flagged.


TODO:
* Add `blackout? : Syntax → Bool` to prevent further inspection by the linter?
* Add `context? : InfoTree → Bool` for further effects combining `unwanted` and `blackout?` and
  possibly doing some further filtering?

See  #11890 for an example of how this may be extended.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "generic" linter emits a warning on "generic" syntax. -/
register_option linter.generic : Bool := {
  defValue := true
  descr := "enable the generic linter"
}

namespace generic

/-- find `cdot` syntax. -/
partial
def findDot : Syntax → (Array Syntax)
  | stx@(.node _ k args) =>
    let dargs := (args.map findDot).flatten
    if k == ``Lean.Parser.Term.cdot then dargs.push stx else dargs
  |_ => default

/-- is the actual symbol `·`? -/
def isCDot? : Syntax → Bool
  | .node _ _ #[.atom _ v] => v == "·"
  | _ => false

/-- the main unwanted syntax: a `cdot` that is not a `·`. -/
def unwanted.cDot (stx : Syntax) : Array Syntax :=
  (findDot stx).filter (!isCDot? ·)

end generic

end Mathlib.Linter

namespace Mathlib.Linter.generic

/-- Gets the value of the `linter.generic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.generic o

/-- The main implementation of the terminal refine linter. -/
def terminalRefineLinter (contains? : Syntax → Array Syntax) : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let _ ← (contains? stx).mapM fun s =>
      Linter.logLint linter.generic s m!"here"

initialize addLinter (terminalRefineLinter unwanted.cDot)
