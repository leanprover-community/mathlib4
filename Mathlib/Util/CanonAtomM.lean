/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Init
import Lean.Meta.Tactic.Simp.Types
import Qq

/-!
# A monad for tracking and deduplicating atoms
This monad attempts to provide the same functionality as `AtomM`, but uses the recommended faster =
approach described in `CanonM`.
-/
namespace Mathlib.Tactic

open Lean Meta

/-- The context (read-only state) of the `CanonAtomM` monad. -/
structure CanonAtomM.Context where
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

/-- The mutable state of the `AtomM` monad. -/
structure CanonAtomM.State where
  /-- The index for the new atom -/
  currentIndex : Nat := 0
  /-- A hashmap to keep track of the indices of canonicalized `Expr`s -/
  index : Std.HashMap Expr Nat := {}

/-- The monad used for collecting atoms. -/
abbrev CanonAtomM := ReaderT CanonAtomM.Context <| StateRefT CanonAtomM.State CanonM

/-- Run a computation in the `CanonAtomM` monad. -/
def CanonAtomM.run {α : Type} (red : TransparencyMode) (m : CanonAtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  ((m { red, evalAtom }).run' {}).run' red

/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be the canonicalized version). -/
def CanonAtomM.addAtom (e : Expr) : CanonAtomM (Nat × Expr) := do
  let e' ← canon e
  if let some es := (← get).index.get? e' then
    return (es, e')
  else
    modifyGet fun c ↦ ((c.currentIndex, e'),
      {currentIndex := c.currentIndex + 1, index := (c.index.insert e' c.currentIndex)})

open Qq

/-- A strongly typed version of `CanonAtomM.addAtom` using `Qq`. -/
def CanonAtomM.addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    CanonAtomM (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, e') ← CanonAtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

end Mathlib.Tactic
