import Lean

namespace DeriveToExprTests
open Lean

-- set_option trace.Elab.Deriving.toExpr true

inductive MyMaybe (α : Type u)
  | none | some (x : α)
  deriving ToExpr

run_cmd Elab.Command.liftTermElabM do
  guard <| "MyMaybe.some 2" == s!"{← Lean.PrettyPrinter.ppExpr <| toExpr (MyMaybe.some 2)}"

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr (MyMaybe.some 2)

deriving instance ToExpr for ULift

run_cmd Elab.Command.liftTermElabM do
  let e := toExpr (MyMaybe.none : MyMaybe (ULift.{1,0} Nat))
  let ty := toTypeExpr (MyMaybe (ULift.{1,0} Nat))
  Meta.check e
  Meta.check ty
  guard <| ← Meta.isDefEq (← Meta.inferType e) ty
  guard <| (← Meta.getLevel ty) == Level.zero.succ.succ

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr <| (MyMaybe.some (ULift.up 2) : MyMaybe (ULift.{1,0} Nat))

deriving instance ToExpr for List

inductive Foo
  | l (x : List Foo)
  deriving ToExpr

run_cmd Elab.Command.liftTermElabM <|
  Meta.check <| toExpr (Foo.l [Foo.l [], Foo.l [Foo.l []]])

/--
error: failed to synthesize
  ToExpr (Bool → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
inductive Bar
  | func (x : Bool → Nat)
  deriving ToExpr

def boolFunHelper (x y : α) (b : Bool) : α := if b then x else y

instance {α : Type u} [ToExpr α] [ToLevel.{u+1}] : ToExpr (Bool → α) where
  toExpr g :=
    mkApp3 (.const ``boolFunHelper [toLevel.{u+1}])
      (toTypeExpr α) (toExpr <| g true) (toExpr <| g false)
  toTypeExpr := .forallE `x (.const ``Bool []) (toTypeExpr α) .default

deriving instance ToExpr for Bar

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
deriving ToExpr
inductive B
  | b
deriving ToExpr
end

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr A.a
  Meta.check <| toExpr B.b

mutual
inductive C
  | c (x : List D)
deriving ToExpr
inductive D
  | b (y : List C)
deriving ToExpr
end

-- An incomplete `ToExpr` instance just to finish deriving `ToExpr` for `Expr`.
instance : ToExpr MData where
  toExpr _ := mkConst ``MData.empty
  toTypeExpr := mkConst ``MData

deriving instance ToExpr for FVarId
deriving instance ToExpr for MVarId
deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for Literal
deriving instance ToExpr for Expr

run_cmd Elab.Command.liftTermElabM do
  Meta.check <| toExpr <| toExpr [1,2,3]

end DeriveToExprTests
