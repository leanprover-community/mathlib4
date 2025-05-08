/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Algebra.Notation.Pi
import Mathlib.Init

/-!
# Reducing Pi instances for indexing in the RefinedDiscrTree
-/

-- This file is only concerned with notation, and should avoid importing the actual algebraic
-- hierarchy.
assert_not_exists Monoid

namespace Lean.Meta.RefinedDiscrTree

variable {α}

/-- Introduce new lambdas by η-expansion. -/
@[specialize]
def etaExpand (args : Array Expr) (type : Expr) (lambdas : List FVarId) (goalArity : Nat)
    (k : Array Expr → List FVarId → MetaM α) : MetaM α  := do
  if args.size < goalArity then
    withLocalDeclD `_η type fun fvar =>
      etaExpand (args.push fvar) type (fvar.fvarId! :: lambdas) goalArity k
  else
    k args lambdas

/-- Normalize an application of a heterogeneous binary operator like `HAdd.hAdd`, using:
- `f = fun x => f x` to increase the arity to 6
- `(f + g) a = f a + g a` to decrease the arity to 6
- `(fun x => f x + g x) = f + g` to get rid of any lambdas in front -/
def reduceHBinOpAux (args : Array Expr) (lambdas : List FVarId) (instH instPi : Name) :
    OptionT MetaM (Expr × Expr × Expr × List FVarId) := do
  let some (mkApp2 (.const instH' _) type inst) := args[3]? | failure
  guard (instH == instH')
  if args.size ≤ 6 then
    etaExpand args type lambdas 6 fun args lambdas =>
      distributeLambdas lambdas type args[4]! args[5]!
  else
  /- use that `(f + g) a = f a + g a` -/
  let mut type := type
  let mut inst := inst
  let mut lhs := args[4]!
  let mut rhs := args[5]!
  for arg in args[6:] do
    let mkApp3 (.const i _) _ f inst' := inst | return (type, lhs, rhs, lambdas)
    unless i == instPi do return (type, lhs, rhs, lambdas)
    type := .app f arg
    inst := inst'
    lhs := .app lhs arg
    rhs := .app rhs arg
  distributeLambdas lambdas type lhs rhs
where
  /-- use that `(fun x => f x + g x) = f + g` -/
  distributeLambdas (lambdas : List FVarId) (type lhs rhs : Expr) :
    MetaM (Expr × Expr × Expr × List FVarId) := match lambdas with
    | fvarId :: lambdas => do
      let decl ← fvarId.getDecl
      let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
      let lhs  := .lam     decl.userName decl.type (lhs.abstract  #[.fvar fvarId]) decl.binderInfo
      let rhs  := .lam     decl.userName decl.type (rhs.abstract  #[.fvar fvarId]) decl.binderInfo
      distributeLambdas lambdas type lhs rhs
    | [] => return (type, lhs, rhs, [])

/-- Normalize an application if the head is  `+`, `*`, `-` or `/`.
Optionally return the `(type, lhs, rhs, lambdas)`. -/
@[inline] def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × Expr × Expr × List FVarId)) :=
  match n with
  | ``HAdd.hAdd => reduceHBinOpAux args lambdas ``instHAdd ``Pi.instAdd
  | ``HMul.hMul => reduceHBinOpAux args lambdas ``instHMul ``Pi.instMul
  | ``HSub.hSub => reduceHBinOpAux args lambdas ``instHSub ``Pi.instSub
  | ``HDiv.hDiv => reduceHBinOpAux args lambdas ``instHDiv ``Pi.instDiv
  | _ => return none

/-- Normalize an application of a unary operator like `Inv.inv`, using:
- `f⁻¹ a = (f a)⁻¹` to decrease the arity to 3
- `(fun x => (f a)⁻¹) = f⁻¹` to get rid of any lambdas in front -/
def reduceUnOpAux (args : Array Expr) (lambdas : List FVarId) (instPi : Name) :
    OptionT MetaM (Expr × Expr × List FVarId) := do
  guard (args.size ≥ 3)
  let mut type := args[0]!
  let mut inst := args[1]!
  let mut arg := args[2]!
  if args.size == 3 then
    distributeLambdas lambdas type arg
  else
  /- use that `f⁻¹ a = (f a)⁻¹` -/
  for arg' in args[3:] do
    let mkApp3 (.const i _) _ f inst' := inst | return (type, arg, lambdas)
    unless i == instPi do return (type, arg, lambdas)
    type := .app f arg'
    inst := inst'
    arg := .app arg arg'
  distributeLambdas lambdas type arg
where
  /-- use that `(fun x => (f x)⁻¹) = f⁻¹` -/
  distributeLambdas (lambdas : List FVarId) (type arg : Expr) :
    MetaM (Expr × Expr × List FVarId) := match lambdas with
    | fvarId :: lambdas => do
      let decl ← fvarId.getDecl
      let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
      let arg  := .lam     decl.userName decl.type (arg.abstract  #[.fvar fvarId]) decl.binderInfo
      distributeLambdas lambdas type arg
    | [] => return (type, arg, [])

/-- Normalize an application if the head is `⁻¹` or `-`.
Optionally return the `(type, arg, lambdas)`. -/
@[inline] def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × Expr × List FVarId)) :=
  match n with
  | ``Neg.neg => reduceUnOpAux args lambdas ``Pi.instNeg
  | ``Inv.inv => reduceUnOpAux args lambdas ``Pi.instInv
  | _ => return none

end Lean.Meta.RefinedDiscrTree
