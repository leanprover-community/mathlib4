/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Moritz Doll
-/

import Mathlib.Tactic.Core

namespace Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic Elab.Tactic.Conv Parser.Tactic.Conv

/--
`dsimp` simplifies a term in `conv`-mode using only definitional equalities.

Examples:

```lean
example : (1 + 0) = 1 := by
  conv =>
    lhs
    dsimp
```
-/
syntax (name := dsimp) "dsimp " (config)? (discharger)? (&"only ")? ("[" dsimpArg,* "]")? : conv

@[tactic Lean.Parser.Tactic.Conv.dsimp] def evalDSimp : Tactic := fun stx => withMainContext do
  -- Get the simp context:
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  -- Get the left-hand-side and change it using dsimp
  changeLhs (← Lean.Meta.dsimp (← getLhs) ctx)

example : (1 + 0) = 1 := by
  dsimp

example : (1 + 0) = 1 := by
  conv =>
    lhs
    dsimp
