import Mathlib.Tactic.DeriveToExpr

namespace tests
open Lean Qq

-- TODO this file fails without this line due to a bug in the handler?
set_option autoImplicit true
--set_option trace.Elab.Deriving.toExprQ true

inductive MyMaybe (α : Type u)
  | none | some (x : α)
  deriving ToExprQ

run_cmd Elab.Command.liftTermElabM do
  guard <| "MyMaybe.some 2" == s!"{← Lean.PrettyPrinter.ppExpr <| toExpr (MyMaybe.some 2)}"
#eval toExpr (MyMaybe.some 2)

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr (MyMaybe.some 2)

deriving instance ToExprQ for ULift

run_cmd Elab.Command.liftTermElabM do
  let e := toExpr (MyMaybe.none : MyMaybe (ULift.{1,0} Nat))
  let ty := toTypeExpr (MyMaybe (ULift.{1,0} Nat))
  Meta.check e
  Meta.check ty
  guard <| ← Meta.isDefEq (← Meta.inferType e) ty
  guard <| (← Meta.getLevel ty).normalize == Level.zero.succ.succ

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr <| (MyMaybe.some (ULift.up 2) : MyMaybe (ULift.{1,0} Nat))

deriving instance ToExprQ for List

inductive Foo
  | l (x : List Foo)
  deriving ToExprQ

run_cmd Elab.Command.liftTermElabM <|
  Meta.check <| toExpr (Foo.l [Foo.l [], Foo.l [Foo.l []]])

inductive Bar
  | func (x : Bool → Nat)
  -- deriving ToExprQ
/- As expected:
failed to synthesize instance
  ToExprQ (Bool → Nat)
-/

def boolFunHelper (x y : α) (b : Bool) : α := if b then x else y

instance [ToExprQ α] : ToExprQ (Bool → α) where
  level := ToExprQ.level α
  toTypeExprQ := q(Bool → $(toTypeExprQ α))
  toExprQ g := q(boolFunHelper $(toExprQ (g true)) $(toExprQ (g false)))

deriving instance ToExprQ for Bar

example : True := by
  run_tac do
    let f : Bool → Nat | false => 0 | true => 1
    let e := toExpr <| Bar.func f
    Meta.check e
    guard <| ← Meta.isDefEq (← Meta.inferType e) (toTypeExpr Bar)
  trivial

mutual
inductive A
  | a
deriving ToExprQ
inductive B
  | b
deriving ToExprQ
end

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr A.a
  Meta.check <| toExpr B.b

mutual
inductive C
  | c (x : List D)
deriving ToExprQ
inductive D
  | b (y : List C)
deriving ToExprQ
end

-- An incomplete `ToExpr` instance just to finish deriving `ToExpr` for `Expr`.
instance : ToExprQ MData where
  level := .zero
  toExprQ _ := mkConst ``MData.empty
  toTypeExprQ := mkConst ``MData

deriving instance ToExprQ for FVarId
deriving instance ToExprQ for MVarId
deriving instance ToExprQ for LevelMVarId
deriving instance ToExprQ for Level
deriving instance ToExprQ for BinderInfo
deriving instance ToExprQ for Literal
deriving instance ToExprQ for Expr

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr <| toExpr [1,2,3]

end tests
