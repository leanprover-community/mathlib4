/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init
import Lean.Meta.Canonicalizer
import Lean.Meta.Tactic.Simp.Types

/-!
# A monad for tracking and deduplicating atoms

This monad is used by tactics like `ring` and `abel` to keep uninterpreted atoms in a consistent
order, and also to allow unifying atoms up to a specified transparency mode.

Note: this can become very expensive because it is using `isDefEq`.
For performance reasons, consider whether `Lean.Meta.Canonicalizer.canon` can be used instead.
After canonicalizing, a `HashMap Expr Nat` suffices to keep track of previously seen atoms,
and is much faster as it uses `Expr` equality rather than `isDefEq`.
-/

namespace Mathlib.Tactic
open Lean Meta

/-- The context (read-only state) of the `AtomM` monad. -/
structure AtomM.Context where
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

/-- The mutable state of the `AtomM` monad. -/
structure AtomM.State where
  /-- The list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
  atoms : Std.HashMap Expr Nat := {}

/-- The monad that `ring` works in. This is only used for collecting atoms. -/
abbrev AtomM := ReaderT AtomM.Context <| StateRefT AtomM.State CanonM

/-- Run a computation in the `AtomM` monad. -/
def AtomM.run {α : Type} (red : TransparencyMode) (m : AtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  let c : CanonM α := (m { evalAtom }).run' {}
  c.run' red

/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
def AtomM.addAtom (e : Expr) : AtomM Nat := do
  let c ← get
  let e ← canon e
  match c.atoms[e]? with
  | some i => return i
  | none =>
  modifyGet fun c ↦ (c.atoms.size, { c with atoms := c.atoms.insert e c.atoms.size })

end Mathlib.Tactic
