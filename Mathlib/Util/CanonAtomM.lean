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

structure CanonAtomM.Context where
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

structure CanonAtomM.State where
  currentIndex : Nat := 0
  index : Std.HashMap Expr Nat := {}

abbrev CanonAtomM := ReaderT CanonAtomM.Context <| StateRefT CanonAtomM.State CanonM

def CanonAtomM.run {α : Type} (red : TransparencyMode) (m : CanonAtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  ((m { red, evalAtom }).run' {}).run' red

def CanonAtomM.addAtom (e : Expr) : CanonAtomM (Nat × Expr) := do
  let e' ← canon e
  if let some es := (← get).index.get? e' then
    return (es, e')
  else
    modifyGet fun c ↦ ((c.currentIndex, e'),
      {currentIndex := c.currentIndex + 1, index := (c.index.insert e' c.currentIndex)})

open Qq

def CanonAtomM.addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    CanonAtomM (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, e') ← CanonAtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

end Mathlib.Tactic
