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

/-- converts a name involving `degree` to a name involving `natDegree`. -/
def nameToNatDegree : Name → Name
  | .str a b => .str (nameToNatDegree a) (b.replace "degree" "natDegree")
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
  elabCommand (toNatDegree cmd)
