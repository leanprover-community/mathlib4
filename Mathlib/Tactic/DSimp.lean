/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Moritz Doll
-/

import Mathlib.Tactic.Core

/-!
The `dsimp` tactic for `conv`.
-/

namespace Lean.Parser.Tactic.Conv
open Lean.Elab.Tactic Elab.Tactic.Conv Parser.Tactic.Conv

/--
`dsimp` is the definitional simplifier in `conv`-mode. It differs from `simp` in that it only
applies theorems that hold by reflexivity.

Examples:

```lean
example (a : Nat): (0 + 0) = a - a := by
  conv =>
    lhs
    dsimp
    rw [←Nat.sub_self a]
```
-/
syntax (name := dsimp) "dsimp " (config)? (discharger)? (&"only ")? ("[" dsimpArg,* "]")? : conv

@[tactic Lean.Parser.Tactic.Conv.dsimp] def evalDSimp : Tactic := fun stx => withMainContext do
  -- Get the simp context:
  let { ctx, .. } ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  -- Get the left-hand-side and change it using dsimp
  changeLhs (← Lean.Meta.dsimp (← getLhs) ctx)
