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
import Std.Data.DHashMap.Basic

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


structure VarContext where
  /-- Mapping from variable `v` to its underlying expression `e` -/
  var2Expr : Std.HashMap UInt64 Expr
  /-- Mapping from variable `v` to a canonical variable `c`, and a proof that `v = c`. -/
  var2canonical : Std.HashMap UInt64 (UInt64 × Expr)

structure VarVal where
  e : Expr
deriving BEq, Hashable

def VarVal.toExpr (v : VarVal) : Expr := v.e

instance : ToExprM VarVal where
  toExprM v := return v.e

def VarExpr.ofExpr (e : Expr) : VarVal := ⟨e⟩

structure EqTy where
  ty? : Option Expr := .none
  lhs : VarVal
  rhs : VarVal

instance : BEq EqTy where
  beq x y := x.lhs == y.lhs && x.rhs == y.rhs

instance : Hashable EqTy where
  hash x := hash (x.lhs, x.rhs)

def EqTy.toExprM (e : EqTy) : MetaM Expr :=
  mkAppOptM `Eq #[e.ty?, e.lhs.toExpr, e.rhs.toExpr]

instance : ToExprM EqTy where
  toExprM e := e.toExprM

def EqTy.ofExpr? (e : Expr) : Option EqTy :=
  match_expr e with
  | Eq ty lhs rhs  => do
    let lhs := VarExpr.ofExpr lhs
    let rhs := VarExpr.ofExpr rhs
    some { ty? := ty, lhs := lhs, rhs := rhs }
  | _ => none

structure NotTy (α : Type) where
  e : α
deriving BEq, Hashable

/-- info: Not (a : Prop) : Prop -/
#guard_msgs in #check Not

def NotTy.toExpr {α : Type} [ToExprM α]
    (n : NotTy α) : MetaM Expr := do
  return mkApp (mkConst `Not) (← toExprM n.e)

instance {α : Type} [ToExprM α] : ToExprM (NotTy α) where
  toExprM n := do
    return mkApp (mkConst `NotExpr.mk) (← toExprM n.e)

def NotTy.ofExpr? {α : Type} [E : OfExpr? α] (e : Expr): Option (NotTy α) :=
  match_expr e with
  | Not e' => do
    let e' ← E.ofExpr? e'
    some { e := e' }
  | _ => none

abbrev NeqTy := NotTy EqTy

structure LeqTy where
  lhs : VarVal
  rhs : VarVal
deriving BEq, Hashable

/-- info: LE.le.{u} {α : Type u} [self : LE α] : α → α → Prop -/
#guard_msgs in #check LE.le

def LeqTy.ofExpr? (e : Expr) : Option LeqTy :=
    match_expr e with
    | LE.le _α _self a b =>
      let lhs := VarExpr.ofExpr a
      let rhs := VarExpr.ofExpr b
      some { lhs := lhs, rhs := rhs }
    | _ => none

def LeqTy.toExpr (leq : LeqTy) : MetaM Expr := do
  mkAppOptM ``LE.le #[.none, .none, leq.lhs.toExpr, leq.rhs.toExpr]

instance : ToExprM LeqTy where
  toExprM e := e.toExpr

instance : OfExpr? LeqTy where
  ofExpr? e := LeqTy.ofExpr? e

abbrev NotLeqTy := NotTy LeqTy

/-- info: Inf.inf.{u_1} {α : Type u_1} [self : Inf α] : α → α → α -/
#guard_msgs in #check Inf.inf -- ⊓

-- a ∩ b = c
structure InfTy where
  ty? : Option Expr
  self? : Option Expr
  lhs : VarVal
  rhs : VarVal


instance : BEq InfTy where
  beq x y := x.lhs == y.lhs && x.rhs == y.rhs

instance : Hashable InfTy where
  hash x := hash (x.lhs, x.rhs)

def InfTy.toExpr (e : InfTy) : MetaM Expr :=
  mkAppOptM ``Inf.inf #[e.ty?, e.self?, e.lhs.toExpr, e.rhs.toExpr]

def InfTy.ofExpr? (e : Expr) : Option InfTy :=
  match_expr e with
  | Inf.inf α self a b =>
    let lhs := VarExpr.ofExpr a
    let rhs := VarExpr.ofExpr b
    some { ty? := α, self? := self, lhs := lhs, rhs := rhs }
  | _ => none

/-- A proof of some expressions α -/
structure Proof {α : Type} (ty : α) where
  proof : MetaM Expr

instance {α : Type} (a : α) : ToExprM (Proof a) where
  toExprM p := p.proof

namespace Algorithm

/- TODO: Eventually use discrimination trees to store proofs. -/
#check DiscrTree

structure State where
  /-- Current fuel available -/
  fuel : Nat
  leqs : Std.DHashMap LeqTy Proof
  nleqs : Std.DHashMap NotLeqTy Proof
  neqs : Std.DHashMap NeqTy Proof
  eqs : Std.DHashMap EqTy Proof
  infs : Std.DHashMap InfTy Proof
  vars : HashSet VarVal

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

/--
returns if equation was new.
Proof is lazily computed as necessary
-/
def addEqualityProof (ty : EqTy)
    (proof : Proof ty) : LatticeM Bool := do
  let s ← get
  if s.eqs.contains ty then
    return false
  else
    modify fun s => { s with eqs := s.eqs.insert ty proof }
    -- TODO: substitute all instances of lhs with rhs in all equations.
    return true

def addEqRefl (v : VarVal) : LatticeM Bool := do
  let eqTy : EqTy := { ty? := none, lhs := v, rhs := v }
  let proof := mkEqRefl v.e

  if (← get).eqs.contains eqTy then
    return false
  else
    modify fun s => { s with eqs := s.eqs.insert eqTy ⟨proof⟩ }
    return true

def addLeqProof {ty : LeqTy}
  (proof : Proof ty) : LatticeM Bool := do
  let s ← get
  if s.leqs.contains ty then
    return false
  else
    modify fun s => { s with leqs := s.leqs.insert ty proof }
    return true

/-- info: le_refl.{u} {α : Type u} [Preorder α] (a : α) : a ≤ a -/
#guard_msgs in #check le_refl

def mkLERefl (e : Expr) : MetaM Expr := do
  mkAppOptM ``le_refl #[none, none, e]

def addLeqRefl (v : VarVal) : LatticeM Bool := do
  let leqTy : LeqTy := { lhs := v, rhs := v }
  let proof : Proof leqTy :=
    Proof.mk <| mkLERefl v.e
  addLeqProof proof

def addVar (v : VarVal) : LatticeM Bool := do
  return (← addEqRefl v) || (← addLeqRefl v)

/--
info: Preorder.le_trans.{u} {α : Type u} [self : Preorder α] (a b c : α) : a ≤ b → b ≤ c → a ≤ c
-/
#guard_msgs in #check Preorder.le_trans

def mkLeqTransProof (a b c : Expr) (pab : Expr) (pbc : Expr) : MetaM Expr := do
  return ← mkAppOptM ``Preorder.le_trans #[none, none, a, b, c, pab, pbc]

def tryAddLeqTrans? {xy yz : LeqTy}
    (pxy : Proof xy) (pyz : Proof yz) : LatticeM Bool := do
  if ← isDefEq xy.rhs.e yz.lhs.e then
    let outTy : LeqTy := { lhs := xy.lhs, rhs := yz.rhs }
    if (← get).leqs.contains outTy then return false
    let proof : Proof outTy := Proof.mk <| do
      mkLeqTransProof xy.lhs.e xy.rhs.e yz.rhs.e (← pxy.proof) (← pyz.proof)
    addLeqProof proof
  else
    return false

/--
info: PartialOrder.le_antisymm.{u} {α : Type u} [self : PartialOrder α] (a b : α) : a ≤ b → b ≤ a → a = b
-/
#guard_msgs in #check PartialOrder.le_antisymm

def mkLeAntisymmProof (a b : Expr) (pab : Expr) (pba : Expr) : MetaM Expr := do
  return ← mkAppOptM ``Preorder.le_trans #[none, none, a, b, pab, pba]

def tryAddLeqAntiSymm? {xy yx : LeqTy}
    (pxy : Proof xy) (pyx : Proof yx) : LatticeM Bool := do
  if (← isDefEq xy.lhs.e yx.rhs.e) && (← isDefEq xy.rhs.e yx.lhs.e) then
    let outTy : EqTy := { lhs := xy.lhs, rhs := xy.rhs }
    if (← get).eqs.contains outTy then return false

    let proof : Proof outTy := Proof.mk <| do
      mkLeAntisymmProof xy.lhs.e xy.rhs.e (← pxy.proof) (← pyx.proof)
    addEqualityProof outTy proof
  else
    return false

/--
info: SemilatticeInf.inf_le_left.{u} {α : Type u} [self : SemilatticeInf α] (a b : α) : a ⊓ b ≤ a
-/
#guard_msgs in #check SemilatticeInf.inf_le_left

def mkInfLeLeftProof (a b : Expr) : MetaM Expr := do
  mkAppOptM ``SemilatticeInf.inf_le_left #[none, none, a, b]

/--
info: SemilatticeInf.inf_le_right.{u} {α : Type u} [self : SemilatticeInf α] (a b : α) : a ⊓ b ≤ b
-/
#guard_msgs in #check SemilatticeInf.inf_le_right

def mkInfLeRightProof (a b : Expr) : MetaM Expr := do
  mkAppOptM ``SemilatticeInf.inf_le_right #[none, none, a, b]

/--
info: SemilatticeInf.le_inf.{u} {α : Type u} [self : SemilatticeInf α] (a b c : α) : a ≤ b → a ≤ c → a ≤ b ⊓ c
-/
#guard_msgs in #check SemilatticeInf.le_inf

-- def tryAddInfLe? {xy : InfTy} (pxy : Proof xy) : LatticeM Bool := do
--   let leLeftTy : LeqTy := { lhs := xy.lhs, rhs := ← xy.toExpr }
--   if (← get).leqs.contains leLeftTy then return false
--   let proof : Proof leLeftTy := Proof.mk <| mkInfLeLeftProof xy.lhs.e xy.rhs.e
--   addLeqProof proof

def tryAddLeInf? {ab : LeqTy} {bc : LeqTy} {abc : InfTy} (pab : Proof ab) (pbc : Proof bc) {pabc : Proof abc} : LatticeM Bool := do
  return false


def try

/--
Given the current set of derivations, perform a new derivation.
Returns 'false' if no progress has been made.
-/
def doWork : LatticeM Bool := do
  if ! (← hasFuel?) then
    return false
  let mut changed := false
  for v in (← get).vars do
    changed := changed || (← addEqRefl v) || (← addLeqRefl v)

  for xy in (← get).leqs do
    for zw in (← get).leqs do
      changed := changed || (← tryAddLeqAntiSymm? xy.snd zw.snd)
      changed := changed || (← tryAddLeqTrans? xy.snd zw.snd)

  return changed

def falseFromPosNegLit  {P : Prop} (t : P) (f : ¬ P) : False := f t

/-- info: Lattice.Algorithm.LatticeM.falseFromPosNegLit {P : Prop} (t : P) (f : ¬P) : False -/
#guard_msgs in #check falseFromPosNegLit


/--
example: α : EqTy, na : NotTy EqTy
@bollu: I find the below very confusing to think about.
  I need to ask Alex how to think about this.
-/
def tryUnsatFromEqNeq {τ : Type} [ToExprM τ] {prop : τ} {notProp : NotTy τ}
    (pos : Proof prop) (neg : Proof notProp) : LatticeM (Option Expr) := do
  let epos ← toExprM pos
  let eneg ← toExprM neg
  if ← isDefEq epos eneg then
    let proof ← mkAppOptM ``falseFromPosNegLit
      #[none, epos, eneg]
    return proof
  return .none

/-- If succeeds, produce a proof of False -/
def tryUnsat : LatticeM (Option Expr) := do
  for neq in (← get).neqs do
    for eq in (← get).eqs do
      if let some proof ← tryUnsatFromEqNeq eq.snd neq.snd then
        return proof

  for nleq in (← get).nleqs do
    for leq in (← get).leqs do
      if let some proof ← tryUnsatFromEqNeq leq.snd nleq.snd then
        return proof

  return .none

end LatticeM

end Algorithm



end Lattice
