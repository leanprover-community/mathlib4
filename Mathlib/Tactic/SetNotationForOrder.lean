/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Batteries.Lean.NameMapAttribute
public meta import Lean.Elab.App
public meta import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Init

/-!
# Set notation for order operations

This file allows the use of `⊆` notation while the underlying constant is `≤`.
Similarly for `⊂`/`<`, `⊇`/`≥` and `⊃`/`>`.

A new copy of the `a ⊆ b` syntax is declared, which overwrites the original one.
To elaborate this notation, `a` and `b` are elaborated, and if the type of `a` and `b` is
tagged with `@[use_set_notation_for_order]`, `LE.le` is used instead of `Subset`.
A new delaborator for `LE.le` is also added so that `a ≤ b` prints as `a ⊆ b` whenever the type is
tagged with `@[use_set_notation_for_order]`.

This tag is used for `Set`, `Finset`, `PSet` and `ZFSet`. It is not used for `Multiset` and `List`,
since they have both `≤` and `⊆` defined on them, with different meanings.

TODO: Unify more order operations suh as `∪`/`⊔` and `∩`/`⊓`.
-/

meta section

namespace Mathlib.Meta.SetNotationForOrder

open Lean Meta Elab Term PrettyPrinter.Delaborator SubExpr

/-- The `@[use_set_notation_for_order]` attribute marks that order operations on the given type
should use set-style notation. For example, `⊆` for `≤` and `∪` for `⊔`.
This affects both elaboration and delaboration. -/
initialize setNotationExt : NameMapExtension Unit ← registerNameMapExtension _

@[inherit_doc setNotationExt]
initialize
  registerBuiltinAttribute {
    name := `use_set_notation_for_order
    descr := "use set notation for order operations on this type"
    add declName _stx kind := do
      unless kind == .global do
        throwAttrMustBeGlobal `use_set_notation_for_order kind
      setNotationExt.add declName () }

/-- Whether to use set notation for the given type or not. -/
def useSetNotationFor (type : Expr) : MetaM Bool := do
  let .const n _ := (← whnfR type).getAppFn | return false
  return (setNotationExt.find? (← getEnv) n).isSome

/-! ## Delaboration -/

/-- Delaborate `x ≤ y` into `x ⊆ y` if the type is tagged with `@[use_set_notation_for_order]`. -/
@[app_delab LE.le]
public def delabLe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LE.le α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊆ $y)
  annotateGoToDef stx decl_name%

/-- Delaborate `x < y` into `x ⊂ y` if the type is tagged with `@[use_set_notation_for_order]`. -/
@[app_delab LT.lt]
public def delabLt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr LT.lt α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊂ $y)
  annotateGoToDef stx decl_name%

/-- Delaborate `x ≥ y` into `x ⊇ y` if the type is tagged with `@[use_set_notation_for_order]`. -/
@[app_delab GE.ge]
public def delabGe : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GE.ge α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊇ $y)
  annotateGoToDef stx decl_name%

/-- Delaborate `x > y` into `x ⊃ y` if the type is tagged with `@[use_set_notation_for_order]`. -/
@[app_delab GT.gt]
public def delabGt : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let_expr GT.gt α _ _ _ := ← getExpr | failure
  guard <| ← useSetNotationFor α
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  let stx ← `($x ⊃ $y)
  annotateGoToDef stx decl_name%

/-! ## Elaboration -/

/-- Linter for ambiguous use of subset notation notation. -/
register_option linter.setNotationForOrder : Bool := {
  defValue := true
  descr := "Linter for ambiguous use of subset notation notation" }

/-- This relation is an implementation detail of the `⊆` elaborator. -/
public opaque SubsetElabAux.{u} {α : Type u} : α → α → Prop

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
  -- This behaviour is inspired by `resolveLValLoop` from the file `Lean.Elab.App`.
  tryPostponeIfMVar α
  if ← isMVarApp α then
    synthesizeSyntheticMVarsUsingDefault
    if ← isMVarApp α then
      Linter.logLintIf linter.setNotationForOrder (← getRef)
        m!"Ambiguous use of subset notation: the type is a metavariable.\n\
        Consider adding a type annotation, e.g. `(_ : Set _) ⊆ _`.\n\
        The term will elaborate to a different constant depending on \
        whether the type is tagged with `@[use_set_notation_for_order]`."
  let (rel, cls) := if ← useSetNotationFor α then (le, leCls) else (sub, subCls)
  let inst ← mkInstMVar <| .app (.const cls f.constLevels!) α
  let rel := mkApp2 (.const rel f.constLevels!) α inst
  -- Add the relation (e.g. `LE.le : Set Nat → Set Nat → Prop`) as a hover on the whole term
  addTermInfo' (← getRef) rel (isDisplayableTerm := true)
  return mkApp2 rel x y

/-- Subset relation: `a ⊆ b`.
For types tagged with `@[use_set_notation_for_order]`,
the relation `LE.le` is used instead of `Subset`.
The hover info shows which one is used. -/
syntax:50 (name := subsetStx') (priority := high) term:51 " ⊆ " term:51 : term

/-- Strict subset relation: `a ⊂ b`.
For types tagged with `@[use_set_notation_for_order]`,
the relation `LT.lt` is used instead of `SSubset`.
The hover info shows which one is used. -/
syntax:50 (name := ssubsetStx') (priority := high) term:51 " ⊂ " term:51 : term

/-- Superset relation: `a ⊇ b`.
For types tagged with `@[use_set_notation_for_order]`,
the relation `GE.ge` is used instead of `Superset`.
The hover info shows which one is used. -/
syntax:50 (name := supsetStx') (priority := high) term:51 " ⊇ " term:51 : term

/-- Strict superset relation: `a ⊃ b`.
For types tagged with `@[use_set_notation_for_order]`,
the relation `GT.gt` is used instead of `SSuperset`.
The hover info shows which one is used. -/
syntax:50 (name := ssupsetStx') (priority := high) term:51 " ⊃ " term:51 : term

recommended_spelling "subset" for "⊆" in [subsetStx']
recommended_spelling "ssubset" for "⊂" in [ssubsetStx']
recommended_spelling "superset" for "⊇" in [supsetStx']
recommended_spelling "ssuperset" for "⊃" in [ssupsetStx']

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

end Mathlib.Meta.SetNotationForOrder
