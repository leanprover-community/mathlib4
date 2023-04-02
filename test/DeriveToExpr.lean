import Mathlib.Tactic.DeriveToExpr

namespace tests
open Lean
set_option trace.Elab.Deriving.toExpr true

inductive MyMaybe (α : Type u)
  | none | some (x : α)
  deriving ToExpr

#eval do Lean.PrettyPrinter.ppExpr <| toExpr (MyMaybe.some 2)

deriving instance ToExpr for ULift

#eval toExpr (MyMaybe.none : MyMaybe (ULift.{1,0} Nat))

#eval do
  Meta.check <| toExpr <| (MyMaybe.none : MyMaybe (ULift.{1,0} Nat))

attribute [-instance] Lean.instToExprList
deriving instance ToExpr for List

inductive Foo
  | l (x : List Foo)
  deriving ToExpr

inductive Bar
  | func (x : Nat → Nat)
  --deriving ToExpr
/- As expected:
failed to synthesize instance
  ToExpr (Nat → Nat)
-/

mutual
inductive A
| a
deriving ToExpr
inductive B
| b
deriving ToExpr
end

mutual
inductive C
| c (x : List D)
deriving ToExpr
inductive D
| b (y : List C)
deriving ToExpr
end

-- Bad ToExpr instance, just to finish deriving `ToExpr` for `Expr`.
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

#eval do
  Meta.check <| toExpr (MyMaybe.some 2)
  Meta.check <| toExpr (Foo.l [Foo.l [], Foo.l [Foo.l []]])
  Meta.check <| toExpr A.a
  Meta.check <| toExpr B.b
  Meta.check <| toExpr <| toExpr [1,2,3]

end tests
