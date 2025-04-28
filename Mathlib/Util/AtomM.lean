/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init
import Lean.Meta.Tactic.Simp.Types
import Qq

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
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

/-- The mutable state of the `AtomM` monad. -/
structure AtomM.State where
  /-- The list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
  atoms : Array Expr := #[]

/-- The monad that `ring` works in. This is only used for collecting atoms. -/
abbrev AtomM := ReaderT AtomM.Context <| StateRefT AtomM.State MetaM

/-- Run a computation in the `AtomM` monad. -/
def AtomM.run {α : Type} (red : TransparencyMode) (m : AtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  (m { red, evalAtom }).run' {}

/-- A safe version of `isDefEq` that doesn't throw errors. We use it to avoid
"unknown free variable '_fvar.102937'" errors when there may be out-of-scope free variables.

TODO: don't catch any other errors
-/
def isDefEqSafe (a b : Expr) : MetaM Bool :=
  try isDefEq a b catch _ => pure false

/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtom` should be considered the normal form.
-/
def AtomM.addAtom (e : Expr) : AtomM (Nat × Expr) := do
  let c ← get
  for h : i in [:c.atoms.size] do
    if ← withTransparency (← read).red <| isDefEqSafe e c.atoms[i] then
      return (i, c.atoms[i])
  modifyGet fun c ↦ ((c.atoms.size, e), { c with atoms := c.atoms.push e })

open Qq in
/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtomQ` should be considered the normal form.

This is a strongly-typed version of `AtomM.addAtom` for code using `Qq`.
-/
def AtomM.addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomM (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, e') ← AtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

end Mathlib.Tactic
