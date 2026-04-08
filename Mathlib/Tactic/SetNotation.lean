/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Batteries.Lean.NameMapAttribute
public meta import Lean.Elab.App
public meta import Mathlib.Lean.PrettyPrinter.Delaborator

/-!
# Set Notation

This file allows the use of `⊆` notation while the underlying constant is `≤`.
Similarly for `⊂`/`<`, `⊇`/`≥` and `⊃`/`>`.

A new copy of the `a ⊆ b` syntax is declared, which overwrites the original one.
To elaborate this notation, `a` and `b` are elaborated, and if the type of `a` and `b` is
tagged with `@[use_set_notation]`, `LE.le` is used instead of `Subset`.
A new delaborator for `LE.le` is also added so that `a ≤ b` prints as `a ⊆ b` whenever the type is
tagged with `@[use_set_notation]`. This tag is used for `Set`, `Finset`, `PSet` and `ZFSet`.

`Multiset` and `List` have both `≤` and `⊆` defined on them, with different meanings.
These still work and are unaffected, as they are not tagged with `@[use_set_notation]`.

TODO: The same trick should allow us to make `∪`/`⊔` and `∩`/`⊓` refer to the same constant.
-/

meta section

namespace Mathlib.Meta.SetNotation

open Lean Meta Elab Term PrettyPrinter.Delaborator SubExpr

/-- The `@[use_set_notation]` attribute marks that order operations on the given type should use
set-style notation, e.g. `⊆` instead of `≤`. This affects both elaboration and delaboration. -/
initialize setNotationExt : NameMapExtension Unit ← registerNameMapExtension _

@[inherit_doc setNotationExt]
initialize
  registerBuiltinAttribute {
    name  := `use_set_notation
    descr := "use set notation for this type"
    add   := fun declName _stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `use_set_notation kind
      setNotationExt.add declName () }

/-- Whether to use set notation for the given type or not. -/
def useSetNotationFor (type : Expr) : MetaM Bool := do
  let .const n _ := (← whnfR type).getAppFn | return false
  return (setNotationExt.find? (← getEnv) n).isSome

/-! ## Delaboration -/

/-- Delaborate `x ≤ y` into `x ⊆ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab LE.le]
public def delabLe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LE.le α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊆ $y)
  annotateGoToDef stx decl_name%

/-- Delaborate `x < y` into `x ⊂ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab LT.lt]
public def delabLt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LT.lt α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊂ $y)
  annotateGoToDef stx decl_name%

/-- Delaborate `x ≥ y` into `x ⊇ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab GE.ge]
public def delabGe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GE.ge α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊇ $y)
  annotateGoToDef stx decl_name%

/-- Delaborate `x > y` into `x ⊃ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab GT.gt]
public def delabGt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GT.gt α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊃ $y)
  annotateGoToDef stx decl_name%

/-! ## Elaboration -/

/-- This relation is an implementation detail of the `⊆` elaborator. -/
opaque SubsetElabAux.{u} {α : Type u} : α → α → Prop

/-- Elaborate a notation like `a ⊆ b` by elaborating `a` and `b`, and then deciding
based on their type whether to return `a ⊆ b` or `a ≤ b`.
Use `a ≤ b` whenever `useSetNotationFor` returns true for the type.
If the type is not known, elaboration of this term is postponed.

We assume that `le` and `sub` are names for declarations of exactly the form
`decl.{u} {α : Type u} [Cls.{u} α] (a b : α) : Prop`, and that likewise `leCls` and `subCls` are
names for declarations of exactly the form  `Cls.{u} (α : Type u) : Type u`. -/
def elabSubsetLike (x y : Term) (le leCls sub subCls : Name) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let rel ← `(SubsetElabAux $x $y)
  let e ← elabApp rel expectedType?
  let_expr f@SubsetElabAux α x y := e | throwError "unexpected result {e} when elaborating {rel}"
  -- If the type cannot be determined yet, we postpone elaboration until it is known.
  -- This behaviour is inspired by `resolveLValLoop`.
  tryPostponeIfMVar α
  if ← isMVarApp α then
    synthesizeSyntheticMVarsUsingDefault
  if ← useSetNotationFor α then
    let inst ← mkInstMVar <| .app (.const leCls f.constLevels!) α
    return mkApp4 (.const le f.constLevels!) α inst x y
  else
    let inst ← mkInstMVar <| .app (.const subCls f.constLevels!) α
    return mkApp4 (.const sub f.constLevels!) α inst x y

/-- Subset relation: `a ⊆ b`.

For types tagged with `@[use_set_notation]`, this elaborates to `a ≤ b`. -/
syntax:50 (name := subsetStx') (priority := high) term:51 " ⊆ " term:51 : term

/-- Strict subset relation: `a ⊂ b`.

For types tagged with `@[use_set_notation]`, this elaborates to `a < b`. -/
syntax:50 (name := ssubsetStx') (priority := high) term:51 " ⊂ " term:51 : term

/-- Superset relation: `a ⊇ b`.

For types tagged with `@[use_set_notation]`, this elaborates to `a ≥ b`. -/
syntax:50 (name := supsetStx') (priority := high) term:51 " ⊇ " term:51 : term

/-- Strict superset relation: `a ⊃ b`.

For types tagged with `@[use_set_notation]`, this elaborates to `a > b`. -/
syntax:50 (name := ssupsetStx') (priority := high) term:51 " ⊃ " term:51 : term

/-- Elaborator for `x ⊆ y` notation. -/
@[term_elab subsetStx']
public def elabSubsetStx' : TermElab
  | `($x ⊆ $y), expectedType? =>
    elabSubsetLike x y ``LE.le ``LE ``Subset ``HasSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊂ y` notation. -/
@[term_elab ssubsetStx']
public def elabSSubsetStx' : TermElab
  | `($x ⊂ $y), expectedType? =>
    elabSubsetLike x y ``LT.lt ``LT ``SSubset ``HasSSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊇ y` notation. -/
@[term_elab supsetStx']
public def elabSupsetStx' : TermElab
  | `($x ⊇ $y), expectedType? =>
    elabSubsetLike x y ``GE.ge ``LE ``Superset ``HasSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊃ y` notation. -/
@[term_elab ssupsetStx']
public def elabSSupsetStx' : TermElab
  | `($x ⊃ $y), expectedType? =>
    elabSubsetLike x y ``GT.gt ``LT ``SSuperset ``HasSSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Declare `∀ x ⊆ y, ...` as syntax for `∀ x, x ⊆ y → ...` and `∃ x ⊆ y, ...` as syntax for
`∃ x, x ⊆ y ∧ ...` -/
binder_predicate (priority := high) x " ⊆ " y:term => `($x ⊆ $y)

/-- Declare `∀ x ⊂ y, ...` as syntax for `∀ x, x ⊂ y → ...` and `∃ x ⊂ y, ...` as syntax for
`∃ x, x ⊂ y ∧ ...` -/
binder_predicate (priority := high) x " ⊂ " y:term => `($x ⊂ $y)

/-- Declare `∀ x ⊇ y, ...` as syntax for `∀ x, x ⊇ y → ...` and `∃ x ⊇ y, ...` as syntax for
`∃ x, x ⊇ y ∧ ...` -/
binder_predicate (priority := high) x " ⊇ " y:term => `($x ⊇ $y)

/-- Declare `∀ x ⊃ y, ...` as syntax for `∀ x, x ⊃ y → ...` and `∃ x ⊃ y, ...` as syntax for
`∃ x, x ⊃ y ∧ ...` -/
binder_predicate (priority := high) x " ⊃ " y:term => `($x ⊃ $y)

end Mathlib.Meta.SetNotation
