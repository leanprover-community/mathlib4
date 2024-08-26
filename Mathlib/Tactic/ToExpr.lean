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

universe u in
instance {α : Type u} [ToExpr α] [ToLevel.{u}] : ToExpr (Option α) :=
  let type := toTypeExpr α
  { toExpr     := fun o => match o with
      | none   => mkApp (mkConst ``Option.none [toLevel.{u}]) type
      | some a => mkApp2 (mkConst ``Option.some [toLevel.{u}]) type (toExpr a),
    toTypeExpr := mkApp (mkConst ``Option [toLevel.{u}]) type }

attribute [-instance] Lean.instToExprList

universe u in
private def List.toExprAux {α : Type u} [ToExpr α] (nilFn : Expr) (consFn : Expr) : List α → Expr
  | []    => nilFn
  | a::as => mkApp2 consFn (toExpr a) (toExprAux nilFn consFn as)

universe u in
instance {α : Type u} [ToExpr α] [ToLevel.{u}] : ToExpr (List α) :=
  let type := toTypeExpr α
  let nil  := mkApp (mkConst ``List.nil [toLevel.{u}]) type
  let cons := mkApp (mkConst ``List.cons [toLevel.{u}]) type
  { toExpr     := List.toExprAux nil cons,
    toTypeExpr := mkApp (mkConst ``List [toLevel.{u}]) type }

attribute [-instance] Lean.instToExprArray

universe u in
instance {α : Type u} [ToExpr α] [ToLevel.{u}] : ToExpr (Array α) :=
  let type := toTypeExpr α
  { toExpr     := fun as => mkApp2 (mkConst ``List.toArray [toLevel.{u}]) type (toExpr as.toList)
    toTypeExpr := mkApp (mkConst ``Array [toLevel.{u}]) type }

attribute [-instance] Lean.instToExprProd

universe u v in
instance {α : Type u} {β : Type v} [ToExpr α] [ToExpr β] [ToLevel.{u}] [ToLevel.{v}] :
    ToExpr (α × β) :=
  let αType := toTypeExpr α
  let βType := toTypeExpr β
  { toExpr     := fun ⟨a, b⟩ =>
      mkApp4 (mkConst ``Prod.mk [toLevel.{u}, toLevel.{v}]) αType βType (toExpr a) (toExpr b),
    toTypeExpr := mkApp2 (mkConst ``Prod [toLevel.{u}, toLevel.{v}]) αType βType }

deriving instance ToExpr for System.FilePath

end Lean
end override

namespace Mathlib
open Lean

deriving instance ToExpr for Int

universe u v in
instance {α : Type u} [ToExpr α] [ToLevel.{v}] [ToLevel.{u}] : ToExpr (ULift.{v, u} α) :=
  let type := toTypeExpr α
  { toExpr     := fun _ => type
    toTypeExpr := mkApp (mkConst ``ULift [toLevel.{v}, toLevel.{u}]) type }

universe u in
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
/-- Core of a hand-written `ToExpr` handler for `MData`.
Uses the `KVMap.set*` functions rather than going into the internals
of the `KVMap` data structure. -/
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
