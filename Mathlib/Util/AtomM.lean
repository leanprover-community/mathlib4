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

/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtom` should be considered the normal form.
-/
def AtomM.addAtom (e : Expr) : AtomM (Nat × Expr) := do
  let c ← get
  for h : i in [:c.atoms.size] do
    if ← withTransparency (← read).red <| isDefEq e c.atoms[i] then
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

section AtomQM

open scoped Qq

/-- The mutable state of the `AtomQM` monad. -/
structure AtomQM.State where
  data : Array <| (u : Level) × (Array <| (α : Q(Type u)) × Array Q($α)) := #[]

/-- The context (read-only state) of the `AtomQM` monad. -/
structure AtomQM.Context where
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom {u : Level} {α : Q(Type u)} (a : Q($α)) : MetaM ((x : Q($α)) × Q($x = $a)) :=
    pure ⟨a, q(rfl)⟩
  deriving Inhabited

/-- The monad that `ring` works in. This is only used for collecting atoms. -/
abbrev AtomQM := ReaderT AtomQM.Context <| StateRefT AtomQM.State MetaM

/-- Run a computation in the `AtomQM` monad. -/
def AtomQM.run {α : Type} (m : AtomQM α)
    (evalAtom : ∀ {u : Level} {α : Q(Type u)} (a : Q($α)), MetaM ((x : Q($α)) × Q($x = $a)) :=
    fun a => pure ⟨a, q(rfl)⟩) :
    MetaM α :=
  (m { evalAtom }).run' {}

/-- If an atomic expression has already been encountered, get the index and the stored form of the
atom (which will be defeq at the specified transparency, but not necessarily syntactically equal).
If the atomic expression has *not* already been encountered, store it in the list of atoms, and
return the new index (and the stored form of the atom, which will be itself).

In a normalizing tactic, the expression returned by `addAtomQ` should be considered the normal form.
-/
def AtomQM.addAtomQ {u : Level} {α : Q(Type u)} (a : Q($α)) :
    AtomQM
      ((Nat × Nat × Nat) × (u' : Level) × (α' : Q(Type u')) × (a' : Q($α')) ×'
        (hu : u =QL u') ×' (hα : $α =Q $α') ×' (by exact $a : $α') =Q $a') := do
  let c ← get
  for hiu : iu in [:c.data.size] do
    let ⟨u', αs⟩ := c.data[iu]
    unless ← isLevelDefEq u u' do continue
    have hu : u =QL u' := .unsafeIntro
    for hiα : iα in [:αs.size] do
      let ⟨α', as⟩ := αs[iα]
      let .defEq hα ← Qq.isDefEqQ (α := q(Type u')) α α' | continue
      for hia : ia in [:as.size] do
        have a' := as[ia]
        let .defEq ha ← Qq.isDefEqQ (α := α') a a' | continue
        return ⟨(iu, iα, ia), u', α', a', hu, hα, ha⟩
      -- add a new atom
      modify fun c : State =>
        { data :=
          c.data.modify iu fun ⟨u, αs⟩ =>
            ⟨u, αs.modify iα fun ⟨α, as⟩ =>
              ⟨α, as.push a⟩⟩}
      return ⟨(iu, iα, as.size), u', α', a, hu, hα, .unsafeIntro⟩
    -- add a new type and atom
    modify fun c : State =>
      { data :=
        c.data.modify iu fun ⟨u, αs⟩ =>
          ⟨u, αs.push ⟨α, #[a]⟩⟩}
    return ⟨(iu, αs.size, 0), u', α, a, hu, .unsafeIntro, .unsafeIntro⟩
  -- add a new level, type, and atom
  modify fun c : State =>
    { data := c.data.push ⟨u, #[⟨α, #[a]⟩]⟩}
  return ⟨(c.data.size, 0, 0), u, α, a, .unsafeIntro, .unsafeIntro, .unsafeIntro⟩


end AtomQM

end Mathlib.Tactic
