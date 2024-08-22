/-
Copyright (c) 2024 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

This file implement a decision theory for the free theory of monotone functions on bounded lattices
(lattices with a top and a bottom),
following [1]. It could be extended to complete lattices, given an implementation of the
Dedekind MacNeille completion [2]

[1] A Decision Procedure for Monotone Functions
    over Bounded and Complete Lattices
    (https://link.springer.com/chapter/10.1007/11964810_15)
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

class BoundedLattice (A : Sort _) extends Lattice A, BoundedOrder A where

class ToExprM (α : Type) where
  toExprM : α → MetaM Expr
open ToExprM

class OfExpr? (α : Type) where
  ofExpr? : Expr → Option α

class OfExpr (α : Type) where
  ofExpr : Expr → α

structure VarExpr where
  e : Expr
deriving BEq, Hashable

def VarExpr.toExpr (v : VarExpr) : Expr := v.e

instance : ToExprM VarExpr where
  toExprM v := return v.e

def VarExpr.ofExpr (e : Expr) : VarExpr := ⟨e⟩

structure EqExpr where
  ty? : Option Expr := .none
  lhs : VarExpr
  rhs : VarExpr
deriving BEq, Hashable

def EqExpr.inferType (e : EqExpr) : MetaM Expr := do
  match e.ty? with
  | some ty => return ty
  | none => do
    let ty ← Meta.inferType e.lhs.e
    return ty

def EqExpr.toExprM (e : EqExpr) : MetaM Expr :=
  mkAppOptM `Eq #[e.ty?, e.lhs.toExpr, e.rhs.toExpr]

instance : ToExprM EqExpr where
  toExprM e := e.toExprM

def EqExpr.ofExpr? (e : Expr) : Option EqExpr :=
  match_expr e with
  | Eq ty lhs rhs  => do
    let lhs := VarExpr.ofExpr lhs
    let rhs := VarExpr.ofExpr rhs
    some { ty? := ty, lhs := lhs, rhs := rhs }
  | _ => none

structure NotExpr (α : Type) where
  e : α
deriving BEq, Hashable

/-- info: Not (a : Prop) : Prop -/
#guard_msgs in #check Not

def NotExpr.toExpr {α : Type} [ToExprM α]
    (n : NotExpr α) : MetaM Expr := do
  return mkApp (mkConst `Not) (← toExprM n.e)

instance {α : Type} [ToExprM α] : ToExprM (NotExpr α) where
  toExprM n := do
    return mkApp (mkConst `NotExpr.mk) (← toExprM n.e)

def NeqExpr.ofExpr? {α : Type} [E : OfExpr? α] (e : Expr): Option (NotExpr α) :=
  match_expr e with
  | Not e' => do
    let e' ← E.ofExpr? e'
    some { e := e' }
  | _ => none

abbrev NeqExpr := NotExpr EqExpr

structure LeqExpr where
  lhs : VarExpr
  rhs : VarExpr
deriving BEq, Hashable

/-- info: LE.le.{u} {α : Type u} [self : LE α] : α → α → Prop -/
#guard_msgs in #check LE.le

def LeqExpr.ofExpr? (e : Expr) : Option LeqExpr :=
    match_expr e with
    | LE.le _α _self a b =>
      let lhs := VarExpr.ofExpr a
      let rhs := VarExpr.ofExpr b
      some { lhs := lhs, rhs := rhs }
    | _ => none

def LeqExpr.toExpr (leq : LeqExpr) : MetaM Expr := do
  mkAppOptM ``LE.le #[.none, .none, leq.lhs.toExpr, leq.rhs.toExpr]

instance : ToExprM LeqExpr where
  toExprM e := e.toExpr

instance : OfExpr? LeqExpr where
  ofExpr? e := LeqExpr.ofExpr? e

abbrev NotLeqExpr := NotExpr LeqExpr

/-- info: Inf.inf.{u_1} {α : Type u_1} [self : Inf α] : α → α → α -/
#guard_msgs in #check Inf.inf -- ⊓

structure InfExpr where
  ty : Expr
  self : Expr
  lhs : VarExpr
  rhs : VarExpr
deriving BEq, Hashable

def InfExpr.toExpr (e : InfExpr) :=
  mkApp4 (mkConst `Inf.inf) e.ty e.self e.lhs.toExpr e.rhs.toExpr

def InfExpr.ofExpr? (e : Expr) : Option InfExpr :=
  match_expr e with
  | Inf.inf α self a b =>
    let lhs := VarExpr.ofExpr a
    let rhs := VarExpr.ofExpr b
    some { ty := α, self := self, lhs := lhs, rhs := rhs }
  | _ => none

namespace Algorithm

/- TODO: Eventually use discrimination trees to store proofs. -/
#check DiscrTree

structure State where
  /-- Current fuel available -/
  fuel : Nat
  leqs : HashSet LeqExpr
  nleqs : HashSet NotLeqExpr
  neqs : HashSet NeqExpr
  eqs : HashSet EqExpr
  infs : HashSet InfExpr
  vars : HashSet VarExpr

structure Config where
  /-- number of basic operations to perform before giving up. -/
  fuel : Nat

def State.ofConfig (cfg : Config) : State :=
  { fuel := cfg.fuel,
    leqs := {},
    nleqs := {},
    neqs := {},
    eqs := {},
    infs := {},
    vars := {}
  }

/-- Core monad that tactic runs in. -/
abbrev LatticeM := StateRefT State (ReaderT Config TacticM)

namespace LatticeM

def get : LatticeM State := StateRefT'.get

def hasFuel? : LatticeM Bool := do
  return (← getThe State).fuel > 0

def consumeFuel : LatticeM Unit := do
  modify fun s => { s with fuel := s.fuel - 1 }


/-- returns if equation was new. -/
def addEquality (lhs : VarExpr) (rhs : VarExpr) : LatticeM Bool := do
  let refl := EqExpr.mk .none lhs rhs
  let s ← get
  if s.eqs.contains refl then
    return false
  else
    modify fun s => { s with eqs := s.eqs.insert refl }
    -- TODO: substitute all instances of lhs with rhs in all equations.
    return true


/--
Given the current set of derivations, perform a new derivation.
Returns 'false' if no progress has been made.
-/
def doWork : LatticeM Bool := do
  if ! (← hasFuel?) then
    return false
  let mut changed := false
  for v in (← get).vars do
    changed := changed || (← addEquality v v)

  return changed

def falseFromPosNegLit  {P : Prop} (t : P) (f : ¬ P) : False := f t

/-- info: Lattice.Algorithm.LatticeM.falseFromPosNegLit {P : Prop} (t : P) (f : ¬P) : False -/
#guard_msgs in #check falseFromPosNegLit


def tryUnsatFromEqNeq {α : Type} [ToExprM α]
    (pos : α) (neg : NotExpr α) : LatticeM (Option Expr) := do
  let epos ← toExprM pos
  let eneg ← toExprM neg.e
  if ← isDefEq epos eneg then
    let proof ← mkAppOptM ``falseFromPosNegLit
      #[none, epos, eneg]
    return proof
  return .none

/-- If succeeds, produce a proof of False -/
def tryUnsat : LatticeM (Option Expr) := do
  for neq in (← get).neqs do
    for eq in (← get).eqs do
      if let some proof ← tryUnsatFromEqNeq eq neq then
        return proof

  for nleq in (← get).nleqs do
    for leq in (← get).leqs do
      if let some proof ← tryUnsatFromEqNeq leq nleq then
        return proof

  return .none

end LatticeM

end Algorithm



end Lattice
