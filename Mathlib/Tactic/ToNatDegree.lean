/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Data.ENat.Basic

/-!
#  `toTD` a command to convert from `degree` to `trailingDegree`

If `thm` is a theorem about `degree`s of polynomials, then `toTD thm` tries to add to the
environment the analogous result about `trailingDegree`s of polynomials.
-/

open Lean Elab Command

namespace Mathlib.ToNatDegree

/-- converts `WithBot _` to `ℕ∞` and `⊥` to `⊤`.
Useful when converting a `degree` with values in `WithBot ℕ` to a `trailingDegree` with values
in `ℕ∞`. -/
def WithBotToENat (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ `WithBot _, _] =>
        return some (← `(ℕ∞))
      | .node _ `«term⊥» #[.atom _ "⊥"] => return some (← `(⊤))
      | _ => return none

/-- converts a name involving `degree` to a name involving `trailingDegree`. -/
def nameToTrailingDegree : Name → Name
  | .str a b =>
      let b := b.replace "degree" "trailingDegree"
      let b := b.replace "max" "min"
      let b := b.replace "bot" "top"
      .str (nameToTrailingDegree a) b
  | _ => default

/-- converts a statement involving `degree` to a name involving `trailingDegree`. -/
def toTrailingDegree (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToTrailingDegree v))

/--
If `thm` is a theorem about `degree`s of polynomials, then `toTD thm` tries to add to the
environment the analogous result about `trailingDegree`s of polynomials.
-/
elab "toTD " tk:"?"? cmd:command : command => do
  if tk.isSome then logInfo m!"adding {indentD (← toTrailingDegree cmd)}"
  elabCommand cmd
  elabCommand (← WithBotToENat <| ← toTrailingDegree cmd)
