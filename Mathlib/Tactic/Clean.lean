/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Michail Karatarakis, Kyle Miller
-/
import Lean.Elab.SyntheticMVars

/-!
# `clean%` term elaborator

Remove identity functions from a term.
-/

open Lean Meta Elab

namespace Lean.Expr

/-- List of names removed by the `clean` tactic.
All of these names must resolve to functions defeq `id`. -/
-- Note: one could also add `hidden`, but this doesn't arise from type hints.
def cleanConsts : List Name :=
  [``id]

/-- Clean an expression by eliminating identify functions listed in `cleanConsts`.
Also eliminates `fun x => x` applications and tautological `let_fun` bindings. -/
def clean (e : Expr) : Expr :=
  e.replace fun
    | .app (.app (.const n _) _) e' => if n ∈ cleanConsts then some e' else none
    | .app (.lam _ _ (.bvar 0) _) e' => some e'
    | e =>
      match e.letFun? with
      | some (_n, _t, v, .bvar 0) => some v
      | _ => none

end Lean.Expr

namespace Mathlib.Tactic

/--
`clean% t` fully elaborates `t` and then eliminates all identity functions from it.

Identity functions are normally generated with terms like `show t from p`,
which translate to some variant on `@id t p` in order to retain the type.
These are also generated by tactics such as `dsimp` to insert type hints.

Example:
```lean
def x : Id Nat := by dsimp [Id]; exact 1
#print x
-- def x : Id Nat := id 1

def x' : Id Nat := clean% by dsimp [Id]; exact 1
#print x'
-- def x' : Id Nat := 1
```
-/
syntax (name := cleanStx) "clean% " term : term

@[term_elab cleanStx, inherit_doc cleanStx]
def elabClean : Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(clean% $t) => do
    let e ← Term.withSynthesize <| Term.elabTerm t expectedType?
    return (← instantiateMVars e).clean
  | _ => throwUnsupportedSyntax

/-- (Deprecated) `clean t` is a macro for `exact clean% t`. -/
macro "clean " t:term : tactic => `(tactic| exact clean% $t)

end Mathlib.Tactic
