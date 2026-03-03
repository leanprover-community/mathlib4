/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Lean.Meta.Simp

/-!
The dsimp% term elaborator runs the `dsimp` tactic on a given term.

For instance, instead of
```
have foo := ...
dsimp at foo
rw [foo]
```
one can do `rw [dsimp% foo]`.
-/

public meta section

open Lean Elab Term Meta

namespace Mathlib.Tactic.dsimpPercent

/--
The `dsimp%` term elaborator runs the `dsimp` tactic on a given term and yields
the resulting term.

For instance, instead of
```
have foo := ...
dsimp at foo
rw [foo]
```
one can write `rw [dsimp% foo]`.
-/
elab (name := dsimpPercentElaborator) "dsimp%" t:term:min : term => do
  mapForallTelescope (fun e => do
    let cfg : Simp.Config := { failIfUnchanged : Bool := true }
    let ctx ← Simp.mkContext cfg #[← getSimpTheorems] (← getSimpCongrTheorems)
    let simprocs ← Simp.getSimprocs
    let e' ← dsimp (← inferType e) ctx #[simprocs]
    if !(← isProp e) then
      let e'' ← dsimp e ctx #[simprocs]
      return ← mkExpectedTypeHint e''.1 e'.1
    else return ← mkExpectedTypeHint e e'.1) (← elabTerm t none)

end Mathlib.Tactic.dsimpPercent

