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


Future extensions:
* Add `blackout? : Syntax → Bool` to prevent further inspection by the linter?
* Add `context? : InfoTree → Bool` for further effects combining `unwanted` and `blackout?` and
  possibly doing some further filtering?

See  #11890 for an example of how this may be extended.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "generic" linter emits a warning on all syntax matching a given pattern. -/
register_option linter.generic : Bool := {
  defValue := true
  descr := "enable the generic linter"
}

namespace generic

/-- is the actual symbol `·`? -/
def isCDot? : Syntax → Bool
  | .node _ ``cdotTk #[.node _ `patternIgnore #[.node _ _ #[.atom _ v]]] => v == "·"
  | .node _ ``Lean.Parser.Term.cdot #[.atom _ v] => v == "·"
  | _ => false

/--
`findDot stx` extracts from `stx` the syntax nodes of `kind` `Lean.Parser.Term.cdot` or `cdotTk`. -/
partial
def findDot : Syntax → Array Syntax
  | stx@(.node _ k args) =>
    let dargs := (args.map findDot).flatten
    match k with
      | ``Lean.Parser.Term.cdot => dargs.push stx
      | ``cdotTk => dargs.push stx
      | _ =>  dargs
  |_ => default

/-- the main unwanted syntax: a `cdot` that is not a `·`.
The function return an array of syntax atoms corresponding to `cdot`s that are not the
written with the character `·`. -/
def unwanted.cDot (stx : Syntax) : Array Syntax :=
  dbg_trace findDot stx
  (findDot stx).filter (!isCDot? ·)

/-- Whether a syntax element is adding an `instance` attribute without a `local` modifier. -/
def is_attribute_instance_in : Syntax → Array Syntax
  | stx@`(command|attribute [instance] $_decl:ident in $_) => #[stx]
  | stx@`(command|attribute [instance $_priority] $_decl:ident in $_) => #[stx]
  | _ => #[]

end generic

end Mathlib.Linter

namespace Mathlib.Linter.generic

/-- Gets the value of the `linter.generic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.generic o

/-- The main implementation of the generic syntax linter. -/
def genericSyntaxLinter (contains? : Syntax → Array (Syntax × MessageData)) : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let _ ← (contains? stx).mapM fun (s, msg) =>
      Linter.logLint linter.generic s msg

initialize addLinter (genericSyntaxLinter fun stx =>
  (unwanted.cDot stx).map (·, "cdots should use `·`"))

initialize addLinter (genericSyntaxLinter fun stx =>
  (is_attribute_instance_in stx).map (·, "careful: \
    `attribute [instance] ... in` declarations are surprising: \
    they are **not** limited to the subsequent declaration, \
    but define global instances \
    please remove the `in` or make this a `local instance` instead"))
