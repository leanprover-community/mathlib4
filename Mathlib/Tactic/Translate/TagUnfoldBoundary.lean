/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Translate.Core
public meta import Mathlib.Tactic.Translate.Core

/-!
# Tagging of unfold boundaries for translation attributes

The file `Mathlib.Tactic.Translate.UnfoldBoundary` defines how to add unfold boundaries in terms.
In this file, we define the infrastructure for tagging declaration to be used for that.
This is in a separate file, because we need to import `Mathlib.Tactic.Translate.Core` here.
-/

meta section

namespace Mathlib.Tactic.Translate

open Lean Meta Elab Command Term UnfoldBoundary

/-- There are 3 kinds of casting functions for a definition `foo := body`:
1. Equality: `foo = body`
2. Unfolding: `foo → body`
3. Refolding: `body → foo`
-/
inductive CastKind where
  | eq | unfoldFun | refoldFun

/-- Construct the type of the cast of the given `CastKind`. -/
def CastKind.mkRel (lhs body : Expr) : CastKind → MetaM Expr
  | .eq => mkEq lhs body
  | .unfoldFun => return .forallE `_ lhs body .default
  | .refoldFun => return .forallE `_ body lhs .default

/-- Construct the value of the cast of the given `CastKind`.
This is a proof by reflexivity for equalities, and an identity function for functions. -/
def CastKind.mkProof (lhs : Expr) : CastKind → MetaM Expr
  | .eq => mkEqRefl lhs
  | _ => return .lam `_ lhs (.bvar 0) .default

/-- `elabInsertCastAux` is used to implement the `insert_cast` and `insert_cast_fun` commands.
Given a definition `declName`, we create a casting function and a dual of this casting function.
The casting function is defined using reflexivity/the identity function,
and its translation is defined using the user-provided term `stx`.
`castKind` specifies which kind of cast we are creating. -/
def elabInsertCastAux (declName : Name) (castKind : CastKind) (stx : Term) (t : TranslateData) :
    CommandElabM (Name × Name) :=
  Command.liftTermElabM do withDeclNameForAuxNaming declName do withExporting do
  let info ← getConstInfoDefn declName
  let addDecl (name : Name) (type value : Expr) : MetaM Unit := do
    addDecl <| ←
      if castKind matches .eq then
        mkThmOrUnsafeDef { name, type, value, levelParams := info.levelParams }
      else
        .defnDecl <$> mkDefinitionValInferringUnsafe name info.levelParams type value .opaque
  let name ← mkAuxDeclName ((t.attrName.appendBefore "_").appendAfter "_cast")
  -- To obtain the unfolded form of `declName`, we telescope into its value.
  let (type, numFVars) ← lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    -- First, create the casting theorem/def that is proved by rfl/id respectively.
    let lhs := mkAppN (.const info.name <| info.levelParams.map mkLevelParam) xs
    let type ← mkForallFVars xs (← castKind.mkRel lhs body)
    let value ← mkLambdaFVars xs (← castKind.mkProof lhs)
    addDecl name type value
    return (type, xs.size)
  -- Then, create the translated version, using `stx` to construct the value.
  let (newType, _) ← (applyReplacementFun t type).run #[] #[]
  let newValue ← forallBoundedTelescope newType numFVars fun xs goalType ↦ do
    -- Make the goal easier to prove by unfolding the new lhs
    let goalType := (← unfoldLHS? castKind goalType).getD goalType
    let newValue ← elabTermEnsuringType stx goalType <* synthesizeSyntheticMVarsNoPostponing
    mkLambdaFVars xs (← instantiateMVars newValue)
  let newName ← mkAuxDeclName ((t.attrName.appendBefore "_").appendAfter "_cast")
  addDecl newName newType newValue
  -- Now add the translation attribute to relate the two new declarations
  _ ← addTranslationAttr t name { tgt := newName, existing := true, ref := .missing }
  return (name, newName)
where
  unfoldLHS? : CastKind → Expr → OptionT TermElabM Expr
  | .eq, mkApp2 eq lhs body => return mkApp2 eq (← .mk <| unfoldDefinition? lhs) body
  | .unfoldFun, .forallE n lhs body bi => return .forallE n (← .mk <| unfoldDefinition? lhs) body bi
  | .refoldFun, .forallE n body lhs bi => return .forallE n body (← .mk <| unfoldDefinition? lhs) bi
  | _, _ => .fail

/-- The `insert_cast foo := ...` command should be used when the translation of some
definition `foo` is not definitionally equal to the translation of its value.
It requires a proof that these two are equal. For example,

```
to_dual_insert_cast Monotone := by grind
```

If the definition is a type, you should use `insert_cast_fun` instead.

The command internally generates an unfolding theorem for `foo`, and a translation of this theorem.
When type checking a term requires the definition `foo` to be unfolded, then in order to translate
that term, a `cast` is first inserted into the term using this unfolding theorem.
As a result, type checking the term won't anymore require unfolding `foo`, so the term
can be safely translated. -/
public def elabInsertCast (declName : Ident) (valStx : Term) (t : TranslateData) :
    CommandElabM Unit := do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo declName
  let (name, _) ← elabInsertCastAux declName .eq valStx t
  let some ext := t.unfoldBoundaries? | throwError "{t.attrName} doesn't support unfold boundaries"
  modifyEnv (ext.addEntry · (.unfold declName name))

/-- The `insert_cast_fun foo := ..., ...` command should be used when the translation of some
type `foo` is not definitionally equal to the translation of its value.
It requires a function from the translation of `foo` to the translation of the value of `foo`,
and a function in the opposite direction. For example,

```
to_dual_insert_cast_fun DecidableLE := fun inst a b ↦ inst b a, fun inst a b ↦ inst b a
```

The command internally generates these unfold/refold functions for `foo`, and their translations.
If type checking a term requires the definition `foo` to be unfolded, then before translating
that term, the unfold/refold function is inserted into the term.
As a result, type checking the term won't anymore require unfolding `foo`, so the term
can be safely translated. After translating, the unfold/refold functions are again unfolded. -/
public def elabInsertCastFun (declName : Ident) (valStx₁ valStx₂ : Term) (t : TranslateData) :
    CommandElabM Unit := do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo declName
  let (name₁, translatedName₁) ← elabInsertCastAux declName .unfoldFun valStx₁ t
  let (name₂, translatedName₂) ← elabInsertCastAux declName .refoldFun valStx₂ t
  let some ext := t.unfoldBoundaries? | throwError "{t.attrName} doesn't support unfold boundaries"
  modifyEnv (ext.addEntry · (.cast declName name₁ name₂ translatedName₁ translatedName₂))

end Mathlib.Tactic.Translate
