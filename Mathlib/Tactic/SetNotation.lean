/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Mathlib.Lean.PrettyPrinter.Delaborator
public meta import Lean.Elab.Extra

/-!
# Set Notation

This file allows the use of `⊆` notation while the underlying constant is `≤`.
Similarly for `⊂`/`<`, `⊇`/`≥` and `⊃`/`>`.

A new copy of the `a ⊆ b` syntax is declared, which overwrites the original one. It tries to
elaborate to the original `a ⊆ b` notation, and if that doesn't work, then it elaborates to `a ≤ b`.

A new delaborator for `LE.le` is added so that `a ≤ b` prints as `a ⊆ b` whenever the type is
tagged with `@[use_set_notation]`. This tag is used for `Set`, `Finset`, `PSet` and `ZFSet`.

`Multiset` has both `≤` and `⊆` defined on it, with different meanings. This still works and is
unaffected.

Some types in Lean core have instances of `HasSubset`, such as `List`. This also still works.

TODO: The same trick should allow us to make `∪`/`⊔` and `∩`/`⊓` refer to the same constant.
-/

public meta section

namespace Mathlib.Meta

open Lean Meta Elab Term PrettyPrinter.Delaborator SubExpr

/-- The `@[use_set_notation]` attribute marks that order notation on the given type should be
pretty printed using set-style notation, i.e. `⊆` instead of `≤`. -/
initialize setNotationExt : TagDeclarationExtension ← mkTagDeclarationExtension

@[inherit_doc setNotationExt]
initialize
  registerBuiltinAttribute {
    name  := `use_set_notation
    descr := "use set notation for this type"
    add   := fun declName _stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `coe kind
      modifyEnv (setNotationExt.tag · declName) }

/-- Whether to use set notation for the given type or not. -/
def useSetNotationFor (type : Expr) : MetaM Bool := do
  let .const n _ := (← whnfR type).getAppFn | return false
  return setNotationExt.isTagged (← getEnv) n

/-! ## Elaboration -/

/-- This relation is an implementation detail of the `⊆` elatorator. -/
opaque SubsetElabAux.{u} {α : Type u} : α → α → Prop

def elabSubsetLike (x y : Term) (le leCls sub subCls : Name) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let rel ← `(SubsetElabAux $x $y)
  let e ← elabApp rel expectedType?
  -- `e` may have `_patWithRef` mdata annotations, so we use `whnfCore`.
  let mkApp3 (.const ``SubsetElabAux [u]) α x y ← whnfCore e
    | throwError "unexpected result {e} when elaborating {rel}"
  -- If the type cannot be determined yet, we postpone elaboration until it is known.
  -- This behaviour is inspired by `resolveLValLoop`.
  tryPostponeIfMVar α
  if (← isMVarApp α) then
    synthesizeSyntheticMVarsUsingDefault
  if ← useSetNotationFor α then
    let inst ← mkInstMVar <| .app (.const leCls [u]) α
    return mkApp4 (.const le [u]) α inst x y
  else
    let inst ← mkInstMVar <| .app (.const subCls [u]) α
    return mkApp4 (.const sub [u]) α inst x y

/-- Subset relation: `a ⊆ b`, but overwritten  -/
syntax:50 (name := subsetStx') (priority := high) term:51 " ⊆ " term:51 : term
/-- Strict subset relation: `a ⊂ b`  -/
syntax:50 (name := ssubsetStx') (priority := high) term:51 " ⊂ " term:51 : term
/-- Superset relation: `a ⊇ b`  -/
syntax:50 (name := supsetStx') (priority := high) term:51 " ⊇ " term:51 : term
/-- Strict superset relation: `a ⊃ b`  -/
syntax:50 (name := ssupsetStx') (priority := high) term:51 " ⊃ " term:51 : term

/-- Elaborator for `x ⊆ y` notation. -/
@[term_elab subsetStx']
def elabSubsetStx' : TermElab
  | `($x ⊆ $y), expectedType? =>
    elabSubsetLike x y ``LE.le ``LE ``Subset ``HasSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊂ y` notation. -/
@[term_elab ssubsetStx']
def elabSsubsetStx' : TermElab
  | `($x ⊂ $y), expectedType? =>
    elabSubsetLike x y ``LT.lt ``LT ``SSubset ``HasSSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊇ y` notation. -/
@[term_elab supsetStx']
def elabSupsetStx' : TermElab
  | `($x ⊇ $y), expectedType? =>
    elabSubsetLike x y ``GE.ge ``LE ``Superset ``HasSubset expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Elaborator for `x ⊃ y` notation. -/
@[term_elab ssupsetStx']
def elabSsupsetStx' : TermElab
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


/-! ## Delaboration -/

/-- Delaborate `x ≤ y` into `x ⊆ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab LE.le]
def delabLe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LE.le α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊆ $y)
  annotateGoToDef stx `Mathlib.Meta.delabLe

/-- Delaborate `x < y` into `x ⊂ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab LT.lt]
def delabLt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LT.lt α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊂ $y)
  annotateGoToDef stx `Mathlib.Meta.delabLt

/-- Delaborate `x ≥ y` into `x ⊇ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab GE.ge]
def delabGe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GE.ge α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊇ $y)
  annotateGoToDef stx `Mathlib.Meta.delabGe

/-- Delaborate `x > y` into `x ⊃ y` if the type is tagged with `@[use_set_notation]`. -/
@[app_delab GT.gt]
def delabGt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GT.gt α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊃ $y)
  annotateGoToDef stx `Mathlib.Meta.delabGt

end Mathlib.Meta
