/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Util.WhatsNew

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

deriving instance ToExpr for System.FilePath

end Lean
end override

namespace Mathlib
open Lean

deriving instance ToExpr for Int

deriving instance ToExpr for ULift

/-- Hand-written instance since `PUnit` is a `Sort` rather than a `Type`. -/
instance [ToLevel.{u}] : ToExpr PUnit.{u+1} where
  toExpr _ := mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExpr := mkConst ``PUnit [toLevel.{u+1}]

deriving instance ToExpr for String.Pos
deriving instance ToExpr for Substring
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax.Preresolved
deriving instance ToExpr for Syntax

open DataValue in
private def toExprMData (md : MData) : Expr := Id.run do
  let mut e := mkConst ``MData.empty
  for (k, v) in md do
    let k := toExpr k
    e := match v with
          | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (mkStrLit v)
          | ofBool v   => mkApp3 (mkConst ``KVMap.setBool) e k (toExpr v)
          | ofName v   => mkApp3 (mkConst ``KVMap.setName) e k (toExpr v)
          | ofNat v    => mkApp3 (mkConst ``KVMap.setNat) e k (mkNatLit v)
          | ofInt v    => mkApp3 (mkConst ``KVMap.setInt) e k (toExpr v)
          | ofSyntax v => mkApp3 (mkConst ``KVMap.setSyntax) e k (toExpr v)
  return e

instance : ToExpr MData where
  toExpr := toExprMData
  toTypeExpr := mkConst ``MData

deriving instance ToExpr for FVarId
deriving instance ToExpr for MVarId
deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for Literal
deriving instance ToExpr for Expr

end Mathlib
