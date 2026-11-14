/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# Shared utilities for the translate tactic

TODO: is there a better location for them?
-/

public meta section

namespace Mathlib.Tactic.Translate

open Lean Lean.Meta Lean.Elab

/-- Elaborate syntax that refers to an argument of a declaration or hypothesis.
This is either a 1-indexed number, or a name from `argNames`.
- `fvars` is only used to add hover information to `stx`
- `head` is only used for the error message. -/
def elabArgStx (stx : TSyntax [`ident, `num]) (argNames : Array Name) (fvars : Array Expr)
    (head : MessageData) : MetaM Nat := do
  let n ← match stx with
    | `($name:ident) => match argNames.idxOf? name.getId with
      | some n => pure n
      | none => throwErrorAt stx
        "invalid argument `{stx}`, it is not an argument of `{head}`."
    | `($n:num) =>
      if n.getNat = 0 then
        throwErrorAt stx "invalid index `{stx}`, arguments are counted starting from 1."
      if n.getNat > fvars.size then
        throwErrorAt stx "index `{stx}` is out of bounds, there are only `{fvars.size}` arguments"
      pure (n.getNat - 1)
    | _ => throwUnsupportedSyntax
  Elab.Term.addTermInfo' stx fvars[n]! |>.run'
  return n

end Mathlib.Tactic.Translate
