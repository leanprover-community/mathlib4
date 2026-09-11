/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.ToSet
public meta import Mathlib.Tactic.Inclusion.Core.Types

/-!
# Expr helpers for the `inclusion` tactic

This file defines helpers for matching or building certain expressions that are used in the
core of the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- If `e` is an `Expr` of the form `x ∈ s` using a `ToSet` instance, return
`some (x, s, toSetInst)`. -/
def toSetMem? (e : Expr) : Option (Expr × Expr × Expr) := do
  let_expr Membership.mem _ _ membershipInst s x := e | none
  let_expr instMembershipOfToSet _ _ toSetInst := membershipInst | none
  return (x, s, toSetInst)

/-- Given expressions `x : xType`, `s : setType`, and `toSetInst : ToSet setType xType`, create
the expression `x ∈ s`. -/
def mkToSetMem (xType setType x s toSetInst : Expr) : MetaM Expr := do
  let membershipInst ← mkAppOptM ``instMembershipOfToSet #[setType, xType, toSetInst]
  mkAppOptM ``Membership.mem #[xType, setType, membershipInst, s, x]

/-- Given `iExpr : IExpr` and `set : iExpr.iType.setType`, create the expression
`iExpr.expr ∈ set`. -/
def IExpr.mkMem (iExpr : IExpr) (set : Expr) : MetaM Expr :=
  mkToSetMem iExpr.iType.elemType iExpr.iType.setType iExpr.expr set iExpr.iType.toSetInst

/-- Given

· `source : iVar.type.setType`,
· `outputType : IType`,
· `cover : Cover iVar.type.setType iVar.type.elemType`,
· `coarsen : Coarsen outputType.setType outputType.elemType`, and
· `inclusion : iVar.type.setType → outputType.setType`,

create the expression `cover.coverMap source inclusion : outputType.setType`. -/
def IVar.mkCoverMap (iVar : IVar) (outputType : IType)
    (source cover coarsen inclusion : Expr) : MetaM Expr :=
  mkAppOptM ``Cover.coverMap
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      outputType.setType, outputType.elemType, outputType.toSetInst, coarsen,
      source, inclusion]

/-- Given

· a source inclusion body for `iVar`,
· `output : IExpr`,
· `cover : Cover iVar.type.setType iVar.type.elemType`,
· `coarsen : Coarsen output.iType.setType output.iType.elemType`,
· `inclusion : iVar.type.setType → output.iType.setType`, and
· `proof : ∀ s, iVar.expr ∈ s → output.expr ∈ inclusion s`,

create a proof of `output.expr ∈ cover.coverMap source.inclusionBody inclusion`. -/
def IVar.mkCoverMapProof (iVar : IVar) (output : IExpr)
    (source : ExprInclusionBody) (cover coarsen inclusion proof : Expr) : MetaM Expr := do
  let outputLevel ← getDecLevel output.iType.setType
  let setLevel ← getDecLevel iVar.type.setType
  let elemLevel ← getDecLevel iVar.type.elemType
  return mkAppN (mkConst ``Cover.mem_coverMap [outputLevel, setLevel, elemLevel])
    #[iVar.type.setType, iVar.type.elemType, iVar.type.toSetInst, cover,
      output.iType.setType, output.iType.elemType, output.iType.toSetInst, coarsen,
      source.inclusionBody, inclusion, iVar.expr, output.expr, source.proofBody, proof]

/-- Given `iType : IType`, synthesize an expression of type
`Coarsen iType.setType iType.elemType`. -/
def IType.synthCoarsen (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Coarsen #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Coarsen` instance is registered for {iType.setType}"

/-- Given `iType : IType`, `refiner : Refine iType.setType iType.elemType`, and expressions
`left right : iType.setType`, create the expression `refiner.refine left right`. -/
def IType.mkRefine (iType : IType) (refiner left right : Expr) : MetaM Expr :=
  mkAppOptM ``Refine.refine #[iType.setType, iType.elemType, iType.toSetInst, refiner, left, right]

/-- Given `iType : IType`, synthesize an expression of type
`Refine iType.setType iType.elemType`. -/
def IType.synthRefine (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Refine #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Refine` instance is registered for {iType.setType}"

/-- Given `iType : IType` and `univ : Univ iType.setType iType.elemType`, create the expression
`univ.univ : iType.setType`. -/
def IType.mkUniv (iType : IType) (univ : Expr) : MetaM Expr :=
  mkAppOptM ``Univ.univ #[iType.setType, iType.elemType, iType.toSetInst, univ]

/-- Given `iExpr : IExpr` and `univ : Univ iExpr.iType.setType iExpr.iType.elemType`, create a
proof of `iExpr.expr ∈ univ.univ`. -/
def IExpr.mkMemUniv (iExpr : IExpr) (univ : Expr) : MetaM Expr := do
  let setLevel ← getDecLevel iExpr.iType.setType
  let elemLevel ← getDecLevel iExpr.iType.elemType
  return mkAppN (mkConst ``Univ.mem_univ [setLevel, elemLevel])
    #[iExpr.iType.setType, iExpr.iType.elemType, iExpr.iType.toSetInst, univ, iExpr.expr]

/-- Given `iType : IType`, synthesize an expression of type `Univ iType.setType iType.elemType`. -/
def IType.synthUniv (iType : IType) : MetaM Expr := do
  let type ← mkAppOptM ``Univ #[iType.setType, iType.elemType, iType.toSetInst]
  try synthInstance type catch _ =>
    throwError "No `Univ` instance is registered for {iType.setType}"

/-- Given an expression `b : IntervalBool`, create the expression proving `b = b`. -/
def mkIntervalBoolRefl (b : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``IntervalBool) b

/-- Given an `ExprInclusion` `inc` for `goal`, and a proof
`inclusionProof : inc.inclusion = IntervalBool.true` create a proof of `goal`. -/
def ExprInclusion.mkGoalProof (inc : ExprInclusion) (goal inclusionProof : Expr) : Expr :=
  mkAppN (mkConst ``true_of_mem_intervalBool_eq_true)
    #[goal, inc.inclusion, inc.proof, inclusionProof]

end Inclusion
