/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Meta.Tactic.Simp.Types

/-!
# A monad for tracking and deduplicating atoms

This monad is used by tactics like `ring` and `abel` to keep uninterpreted atoms in a consistent
order, and also to allow unifying atoms up to a specified transparency mode.
-/

set_option autoImplicit true

namespace Mathlib.Tactic
open Lean Meta

/-- The context (read-only state) of the `AtomM` monad. -/
structure AtomM.Context :=
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

/-- The mutable state of the `AtomM` monad. -/
structure AtomM.State :=
  /-- The list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
  atoms : Array Expr := #[]

/-- The monad that `ring` and `abel` work in. This is only used for collecting atoms. -/
abbrev AtomM := ReaderT AtomM.Context <| StateRefT AtomM.State MetaM

/-- Run a computation in the `AtomM` monad. -/
def AtomM.run (red : TransparencyMode) (m : AtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  (m { red, evalAtom }).run' {}

/--
Simplify an expression using `Atom.Context.evalAtom`,
and check if the simplified expression has already been encountered.
If not, put it into the list of atoms.
In either case, return its index in the list of atoms,
along with the `Simp.Result` describing the simplification.
-/
def AtomM.addAtomWithResult (e : Expr) : AtomM (Nat × Simp.Result) := do
  let ⟨red, evalAtom⟩ ← read
  let ⟨atoms⟩ ← get
  let r ← evalAtom e
  for h : i in [:atoms.size] do
    have : i < atoms.size := h.2
    if ← withTransparency red <| isDefEq r.expr atoms[i] then
      return (i, r)
  set (⟨atoms.push r.expr⟩ : AtomM.State)
  return (atoms.size, r)

/--
Simplify an expression using `Atom.Context.evalAtom`,
and check if the simplified expression has already been encountered.
If not, put it into the list of atoms.
In either case, return its index in the list of atoms.

(Use `AtomM.addAtomWithResult` if you need to keep track of a simplification
performed via `Atom.Context.evalAtom`.)
-/
def AtomM.addAtom (e : Expr) : AtomM Nat := return (← AtomM.addAtomWithResult e).1
