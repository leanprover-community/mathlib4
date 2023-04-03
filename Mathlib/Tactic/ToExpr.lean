import Mathlib.Tactic.DeriveToExpr

/-! # `ToExpr` instances for Mathlib

This module should be imported by any module that intends to define `ToExpr` instances.
It provides necessary dependencies (the `Lean.ToLevel` class) and it also overrides the instances
that come from core Lean 4 that do not handle universe polymorphism.
(See the module `Lean.ToExpr` for the instances that are overridden.)

In addition, we provide some additional `ToExpr` instances for core definitions.
-/

section override
namespace Lean

attribute [-instance] Lean.instToExprOption

deriving instance ToExpr for Option

attribute [-instance] Lean.instToExprList

deriving instance ToExpr for List

attribute [-instance] Lean.instToExprArray

instance {α : Type u} [ToExpr α] [ToLevel.{u}] : ToExpr (Array α) :=
  let type := toTypeExpr α
  { toExpr     := fun as => mkApp2 (mkConst ``List.toArray [toLevel.{u}]) type (toExpr as.toList)
    toTypeExpr := mkApp (mkConst ``Array [toLevel.{u}]) type }

attribute [-instance] Lean.instToExprProd

deriving instance ToExpr for Prod

end Lean
end override

namespace Mathlib
open Lean

deriving instance ToExpr for ULift

/-- Hand-written instance since `PUnit` is a `Sort` rather than a `Type`. -/
instance [ToLevel.{u}] : ToExpr PUnit.{u+1} where
  toExpr _ := mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExpr := mkConst ``PUnit [toLevel.{u+1}]

end Mathlib
