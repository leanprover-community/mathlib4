/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.DeriveToExpr

/-! # `ToExprQ` instances for Mathlib

This module should be imported by any module that intends to define `ToExprQ` instances.
It provides necessary dependencies (the `Lean.ToLevel` class) and it also overrides the instances
that come from core Lean 4 that do not handle universe polymorphism.
(See the module `Lean.ToExprQ` for the instances that are overridden.)

In addition, we provide some additional `ToExprQ` instances for core definitions.
-/

section override
namespace Lean
open Qq

attribute [-instance] Lean.instToExprOption

deriving instance ToExprQ for Option

attribute [-instance] Lean.instToExprList

deriving instance ToExprQ for List

attribute [-instance] Lean.instToExprArray

instance {α : Type u} [ToExprQ α] : ToExprQ (Array α) where
  level := ToExprQ.level α
  toTypeExprQ := q(Array $(toTypeExprQ α))
  toExprQ as := q(List.toArray $(toExprQ as.toList))

attribute [-instance] Lean.instToExprProd

deriving instance ToExprQ for Prod

end Lean
end override

namespace Mathlib
open Lean Qq

deriving instance ToExprQ for Int

deriving instance ToExprQ for ULift

/-- Hand-written instance since `PUnit` is a `Sort` rather than a `Type`. -/
instance [ToLevel.{u}] : ToExprQ PUnit.{u+1} where
  level := toLevel.{u}
  toExprQ _ := mkConst ``PUnit.unit [toLevel.{u+1}]
  toTypeExprQ := mkConst ``PUnit [toLevel.{u+1}]

deriving instance ToExprQ for String.Pos
deriving instance ToExprQ for Substring
deriving instance ToExprQ for SourceInfo
deriving instance ToExprQ for Syntax.Preresolved
deriving instance ToExprQ for Syntax

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

instance : ToExprQ MData where
  level := toLevel.{0}
  toExprQ := toExprMData
  toTypeExprQ := mkConst ``MData

deriving instance ToExprQ for FVarId
deriving instance ToExprQ for MVarId
deriving instance ToExprQ for LevelMVarId
deriving instance ToExprQ for Level
deriving instance ToExprQ for BinderInfo
deriving instance ToExprQ for Literal
deriving instance ToExprQ for Expr

end Mathlib
