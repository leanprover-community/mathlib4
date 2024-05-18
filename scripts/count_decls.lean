/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Damiano Testa
-/
import Mathlib

/-!
# `count_decls` -- a tally of declarations in `Mathlib`

This file is used by the `Periodic reports` script to generate a tally of declarations
in `Mathlib`.

Source: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Metamathematics.3A.20Theorems.20by.20Domain.20Areas/near/374090639
-/

open Lean Elab

/-- A structure containing a few declaration types.  `other` consists of
* `axiom`
* `opaque`
* `quot`
* `ctor`
* `rec`.
-/
structure State where
  defs : Nat := 0
  thms : Nat := 0
  inductives : Nat := 0
  other : Nat := 0
  deriving Repr


/-- `MathlibModIdxs env` returns the `ModuleIdx`s corresponding to `Mathlib` files
that are in the provided environment. -/
def MathlibModIdxs (env : Environment) : IO (HashSet Nat) := do
  let mut modIdx : HashSet Nat := .empty
  for imp in ← IO.FS.lines "Mathlib.lean" do
    if let some nm := env.getModuleIdx? (imp.drop 7).toName then
      modIdx := modIdx.insert nm
  return modIdx

/-- A command that prints a tally of definitions, theorems and inductives in `Mathlib`. -/
elab "count_decls" : command => do
  let env ← getEnv
  let maths ← MathlibModIdxs env
  let consts := env.constants
  let update (s : State) (_ : Name) (c : ConstantInfo) : Command.CommandElabM State :=
    if c.isUnsafe then return s else
    let mod := env.getModuleIdxFor? c.name
    if !maths.contains (mod.getD default) then return s else
    match c with
    | .defnInfo ..   => return {s with defs := s.defs + 1}
    | .thmInfo ..    => return {s with thms := s.thms + 1}
    | .inductInfo .. => return {s with inductives := s.inductives + 1}
    | _ => return {s with other := s.other + 1}
  let s : State ← consts.foldM update {}
  logInfo s!"defs {s.defs}\nthms {s.thms}\ninductives {s.inductives}\nother {s.other}"
  --let total := s.defs + s.thms + s.inductives + s.other
  --logInfo s!"{repr s}\ntotal: {total}"

--count_decls
