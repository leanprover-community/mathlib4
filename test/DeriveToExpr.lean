import Mathlib.Tactic.DeriveToExpr

namespace tests
open Lean
set_option trace.Elab.Deriving.toExpr true

inductive MyMaybe (α : Type)
  | none | some (x : α)
  deriving ToExpr

#eval do Lean.PrettyPrinter.ppExpr <| toExpr (MyMaybe.some 2)

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
inductive B
| b
deriving ToExpr
end

mutual
inductive C
| c (x : List D)
inductive D
| b (y : List C)
deriving ToExpr
end

-- Bad instance, just to finish deriving `ToExpr` for `Expr`.
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

end tests
