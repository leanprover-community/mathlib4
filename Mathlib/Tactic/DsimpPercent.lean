/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Meta.Simp

/-!
`dsimp% […] t` runs `dsimp […]` on term `t`.

For instance, instead of
```
have foo := ...
dsimp at foo
rw [foo]
```
one can do `rw [dsimp% foo]`.
-/

public meta section

namespace Mathlib.Tactic

open  Lean Elab Term Meta Parser Tactic

/--
`dsimp% […] t` runs `dsimp […]` on term `t`.

For instance, instead of
```
have foo := ...
dsimp at foo
rw [foo]
```
one can write `rw [dsimp% foo]`.
-/
syntax (name := dsimpPercent) "dsimp%" optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? term : term

@[term_elab dsimpPercent, inherit_doc dsimpPercent]
def dsimpPercentElaborator : TermElab := fun stx expectedType => do
  let fresh ← mkFreshExprMVar default
  let go : TacticM Expr := do
    let e ← Term.elabTerm stx[5] expectedType
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
    if (← isProof e) then
      let (dsimpResult, _) ← Meta.dsimp (← inferType e) ctx simprocs
      mkExpectedTypeHint e dsimpResult
    else
      let (dsimpResult, _) ← Meta.dsimp (← Term.elabTerm stx[5] expectedType) ctx simprocs
      return dsimpResult
  go { elaborator := .anonymous } |>.run' { goals := [fresh.mvarId!] }

end Mathlib.Tactic
