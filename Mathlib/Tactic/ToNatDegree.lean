/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
#  `toND` a command to convert from `degree` to `natDegree`

If `thm` is a theorem about `degree`s of polynomials, then `toND thm` tries to add to the
environment the analogous result about `natDegree`s of polynomials.
-/

open Lean Elab Command

namespace Mathlib.ToNatDegree

/-- converts `WithBot _` to `Nat` and `⊥` to `0`: a custom-made guessing a reasonable default
when converting a `degree` with values in `WithBot ℕ` to a `natDegree` with values in `ℕ`. -/
def WithBotToNat (stx : Syntax) : Syntax := Id.run do
  stx.replaceM fun s =>
    match s with
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ `WithBot _, _] => some (mkIdent ``Nat)
      | .node _ `«term⊥» #[.atom _ "⊥"] => some (Syntax.mkNumLit "0")
      | _ => none

/-- converts a name involving `degree` to a name involving `natDegree`. -/
def nameToNatDegree : Name → Name
  | .str a b =>
      let repl := if b.splitOn "natDegree" == [b] then b.replace "degree" "natDegree" else b
      .str (nameToNatDegree a) repl
  | _ => default

/-- converts a statement involving `degree` to a name involving `natDegree`. -/
def toNatDegree (stx : Syntax) : Syntax := Id.run do
  stx.replaceM fun s =>
    match s.getId with
      | .anonymous => none
      | v => some (mkIdent (nameToNatDegree v))

/--
If `thm` is a theorem about `degree`s of polynomials, then `toND thm` tries to add to the
environment the analogous result about `natDegree`s of polynomials.
-/
elab "toND " tk:"?"? cmd:command : command => do
  if tk.isSome then logInfo m!"adding {indentD (toNatDegree cmd)}"
  elabCommand cmd
  elabCommand (WithBotToNat <| toNatDegree cmd)
