/-
Copyright (c) 2024 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

This file implement a decision theory for the free theory of monotone functions on bounded lattices
(lattices with a top and a bottom),
following [1]. It could be extended to complete lattices, given an implementation of the
Dedekind MacNeille completion [2]

[1] https://link.springer.com/chapter/10.1007/11964810_15
[2] https://en.wikipedia.org/wiki/Dedekind%E2%80%93MacNeille_completion
-/
import Lean -- HashMap
import Lean.Elab.Tactic.ElabTerm
import Mathlib.Lean.Meta.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder
import Lean

open Lean

namespace Lattice
open Lean Elab Meta Tactic

structure Context where
  nvars : Nat

instance : EmptyCollection Context where
  emptyCollection := { nvars := 0 }

structure Context.Var (c : Context) where
  var : Fin c.nvars
deriving DecidableEq, Hashable, Repr

namespace Context.Var

@[simp]
def emptyElim {α : Sort _} (v : Var ∅) : α := v.var.elim0

end Context.Var


/-- atoms in SSA form, so each primitive operation returns a new variable -/
inductive NormAtom (Γ : Context)
| intersectEq (v l r : Γ.Var) -- v = l ∩ r
| uniteEq (v l r : Γ.Var) -- v = l ∪ r
| eq (l r : Γ.Var) -- l = r
| neq (l r : Γ.Var) -- l ≠ r
| leq (l r : Γ.Var) -- l ≤ r
| notLeq (l r : Γ.Var) -- l ≰ r
deriving DecidableEq, Hashable, Repr

-- TODO: need a hypothesis for `Assumption`.
inductive Derivation (Γ : Context)
| Assumption (e : Expr) (n : NormAtom Γ) : Derivation Γ
deriving BEq, Hashable, Repr
-- TODO: add all derivations here.

/-- The atom that is derived from the derivation. -/
def Derivation.derivedAtom {Γ : Context} (d : Derivation Γ) : NormAtom Γ :=
  match d with
  | Derivation.Assumption _ n => n

structure Model (Γ : Context) where
  /-- mapping from variables to Lean expressions. -/
  var2expr : HashMap Γ.Var Expr
  hmodel : ∀ (v : Γ.Var), var2expr.contains v

instance : EmptyCollection (Model ∅) where
  emptyCollection := {
      var2expr := HashMap.empty,
      hmodel := fun v => v.emptyElim
    }

def Context.Var.denote {Γ : Context} (v : Γ.Var) (m : Model Γ) : Expr :=
  m.var2expr.find! v

def NormAtom.denote {Γ : Context}
    (n : NormAtom Γ) (m : Model Γ) : Expr :=
  match n with
  | NormAtom.intersectEq v l r => l.denote m
  | NormAtom.uniteEq v l r => l.denote m
  | NormAtom.eq l r => l.denote m
  | NormAtom.neq l r => l.denote m
  | NormAtom.leq l r => l.denote m
  | NormAtom.notLeq l r => l.denote m


structure State where
  Γ : Context
  model : Model Γ
  /-- Current fuel available -/
  fuel : Nat
  /-- a mapping from normalized atoms to their derivations -/
  norm2derivation : HashMap (NormAtom Γ) (Derivation Γ)

structure Config where
  /-- number of basic operations to perform before giving up. -/
  fuel : Nat

namespace Algorithm
variable {Γ : Context}
/-- given the current set of derivations, perform a new derivation. Returns 'false' if no progress has been made. -/
def doWork
    (derivations : HashMap (NormAtom Γ) (Derivation Γ)) :
    HashMap (NormAtom Γ) (Derivation Γ) × Bool := sorry

/-- show falsity, by returning the proof of a derivation and its negation. -/
def isUnsat? : Option (Derivation Γ × Derivation Γ) := .none

def isSat? (atom : NormAtom Γ)
    (norm2derivation : HashMap (NormAtom Γ) (Derivation Γ))
 : Option ({ d : Derivation Γ // d.derivedAtom = atom}) := none
end Algorithm

/-- Core monad that tactic runs in. -/
abbrev LatticeM := StateRefT State (ReaderT Config TacticM)

end Lattice
