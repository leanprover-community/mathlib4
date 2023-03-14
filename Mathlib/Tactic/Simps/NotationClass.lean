/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import Std.Lean.NameMapAttribute
import Mathlib.Lean.Expr.Basic
-- import Lean.Elab.Exception
import Qq.MetaM

/-!
# `@[notation_class]` attribute for `@[simps]`

We put this in a separate file so that we can already tag some declarations with this attribute
in the file where we declare `@[simps]`. For further documentation, see `Tactic.Simps.Basic`.
-/

/-- The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by `@[simps]`.
  Adding a `*` indicates that this is a coercion class instead of a notation class.
  The name argument is the projection name we use as the key to search for this class
  (default: name of first projection of the class).
  The optional term is a term of type
  `Name → Name → Array Expr → MetaM (Array (Option Expr))` that specifies how to generate the
  arguments of the class. Specifying this is experimental. -/
syntax (name := notation_class) "notation_class" "*"? (ppSpace ident)? (ppSpace term)? : attr

open Lean Meta Elab Term Qq

namespace Simps

/-- Find arguments for a notation class -/
def defaultfindArgs (_str className : Name) (args : Array Expr) :
  MetaM (Array (Option Expr)) := do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumForallBinders
  if arity == args.size then
    return args.map some
  else if args.size == 1 then
    return mkArray arity args[0]!
  else
    throwError "initialize_simps_projections cannot automatically find arguments for class {
      className}"

/-- Find arguments of a coercion class (`FunLike` or `SetLike`) -/
def findCoercionArgs (str className : Name) (args : Array Expr) :
  MetaM (Array (Option Expr)) := do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumForallBinders
  let eStr := mkAppN (← mkConstWithLevelParams str) args
  let classArgs := mkArray (arity - 1) none
  return #[some eStr] ++ classArgs

/-- Data needed to generate automatic projections. This data is associated to a name of a projection
  in a structure that must be used to trigger the search. -/
structure AutomaticProjectionData where
  /-- `className` is the name of the class we are looking for. -/
  className : Name
  /-- `isNotation` is a boolean that specifies whether this is notation
    (false for the coercions `FunLike` and SetLike`). If this is set to true, we add the current
    class as hypothesis during type-class synthesis. -/
  isNotation := true
  /-- The method to find the arguments of the class. -/
  findArgs : Name → Name → Array Expr → MetaM (Array (Option Expr)) := defaultfindArgs
deriving Inhabited

-- /-- todo: replace by attribute. -/
-- def defaultCoercions : NameMap AutomaticProjectionData :=
-- .ofList [
--   (`toFun, { className := `FunLike, isNotation := false, findArgs := findCoercionArgs }),
--   (`carrier, { className := `SetLike, isNotation := false, findArgs := findCoercionArgs }),
--   (`neg, { className := `Neg }),
--   (`mul, { className := `HMul }),
--   (`npow, { className := `Pow,
--             findArgs  := fun _ _ xs => return xs.push (.const `Nat []) |>.map some })]

/-- `@[notation_class]` attribute. Note: this is *not* a `NameMapAttribute` because we key on the
  argument of the attribute, not the declaration name. -/
initialize notationClassAttr : NameMapExtension AutomaticProjectionData ← do
  let ext ← registerNameMapExtension AutomaticProjectionData
  registerBuiltinAttribute {
    name := `notation_class
    descr := "An attribute specifying that this is a notation class. Used by @[simps]."
    add := fun src stx _kind => do
      unless isStructure (← getEnv) src do
        throwError "@[notation_class] attribute can only be added to classes."
      match stx with
      | `(attr|notation_class $[*%$coercion]? $[$projName?]? $[$findArgs?]?) => do
        let projName ← match projName? with
          | none => pure (getStructureFields (← getEnv) src)[0]!
          | some projName => pure projName.getId
        let findArgs ← MetaM.run' <| TermElabM.run' <|
          match findArgs? with
          | none => pure defaultfindArgs
          | some findArgs =>
            unsafe evalTerm (Name → Name → Array Expr → MetaM (Array (Option Expr)))
                           q(Name → Name → Array Expr → MetaM (Array (Option Expr))) findArgs
        ext.add projName ⟨src, coercion.isNone, findArgs⟩
      | _ => throwUnsupportedSyntax }
  return ext

end Simps
