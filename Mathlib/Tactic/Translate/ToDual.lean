/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Bryan Gin-ge Chen
-/
module

public import Mathlib.Tactic.Translate.Core

/-!
# The `@[to_dual]` attribute.

The `@[to_dual]` attribute is used to translate declarations to their dual equivalent.
See the docstrings of `to_dual` and `to_additive` for more information.

Known limitations:
- Reordering arguments of arguments is not yet supported.
  This usually comes up in constructors of structures. e.g. `Pow.mk` or `OrderTop.mk`
- When combining `to_additive` and `to_dual`, we need to make sure that all translations are added.
  For example `attribute [to_dual (attr := to_additive) le_mul] mul_le` should generate
  `le_mul`, `le_add` and `add_le`, and in particular should realize that `le_add` and `add_le`
  are dual to eachother. Currently, this requires writing
  `attribute [to_dual existing le_add] add_le`.
-/

public meta section

namespace Mathlib.Tactic.ToDual
open Lean Meta Elab Term Command Std Translate UnfoldBoundary

@[inherit_doc TranslateData.ignoreArgsAttr]
syntax (name := to_dual_ignore_args) "to_dual_ignore_args" (ppSpace num)* : attr

@[inherit_doc relevantArgOption]
syntax (name := to_dual_relevant_arg) "to_dual_relevant_arg " num : attr

@[inherit_doc TranslateData.doTranslateAttr]
syntax (name := to_dual_do_translate) "to_dual_do_translate" : attr

@[inherit_doc TranslateData.doTranslateAttr]
syntax (name := to_dual_dont_translate) "to_dual_dont_translate" : attr

/-- The attribute `to_dual` can be used to automatically transport theorems
and definitions (but not inductive types and structures) to their dual version.
It uses the same implementation as `to_additive`.

To use this attribute, just write:

```
@[to_dual]
theorem max_comm' {α} [LinearOrder α] (x y : α) : max x y = max y x := max_comm x y
```

This code will generate a theorem named `min_comm'`. It is also
possible to manually specify the name of the new declaration:

```
@[to_dual le_max_left]
lemma min_le_left (a b : α) : min a b ≤ a := sorry
```

An existing documentation string will _not_ be automatically used, so if the theorem or definition
has a doc string, a doc string for the dual version should be passed explicitly to `to_dual`.

```
/-- The maximum is commutative. -/
@[to_dual /-- The minimum is commutative. -/]
theorem max_comm' {α} [LinearOrder α] (x y : α) : max x y = max y x := max_comm x y
```

Use the `(reorder := ...)` syntax to reorder the arguments compared to the dual declaration.
This is specified using cycle notation. For example `(reorder := α β, 5 6)` swaps the arguments
`α` and `β` with each other and the fifth and the sixth argument and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. For example, this is used when tagging `LE.le`
with `to_dual self (reorder := 3 4)`, so that `a ≤ b` gets transformed into `b ≤ a`.

Use the `to_dual self` syntax to mark the lemma as its own dual. This is needed if the lemma is
its own dual, up to a reordering of its arguments. `to_dual self` (and `to_dual existing`) tries to
autogenerate the `(reorder := ...)` argument, so it is usually not necessary to give it explicitly.

Use the `to_dual existing` syntax to use an existing dual declaration,
instead of automatically generating it.

Use the `(attr := ...)` syntax to apply attributes to both the original and the dual version:
```
@[to_dual (attr := simp)] lemma min_self (a : α) : min a a = a := sorry
```
 -/
syntax (name := to_dual) "to_dual" "?"? attrArgs : attr

@[inherit_doc to_dual]
macro "to_dual?" rest:attrArgs : attr => `(attr| to_dual ? $rest)

@[inherit_doc to_dual_ignore_args]
initialize ignoreArgsAttr : NameMapExtension (List Nat) ←
  registerNameMapAttribute {
    name  := `to_dual_ignore_args
    descr :=
      "Auxiliary attribute for `to_dual` stating that certain arguments are not dualized."
    add   := fun _ stx ↦ do
        let ids ← match stx with
          | `(attr| to_dual_ignore_args $[$ids:num]*) => pure <| ids.map (·.1.isNatLit?.get!)
          | _ => throwUnsupportedSyntax
        return ids.toList }

@[inherit_doc UnfoldBoundaryExt.unfolds]
initialize unfolds : NameMapExtension SimpTheorem ← registerNameMapExtension _

@[inherit_doc UnfoldBoundaryExt.casts]
initialize casts : NameMapExtension (Name × Name) ← registerNameMapExtension _

@[inherit_doc UnfoldBoundaryExt.insertionFuns]
initialize insertionFuns : NameMapExtension Unit ← registerNameMapExtension _

@[inherit_doc TranslateData.unfoldBoundaries]
def unfoldBoundaries : UnfoldBoundaryExt := { unfolds, casts, insertionFuns }

@[inherit_doc TranslateData.argInfoAttr]
initialize argInfoAttr : NameMapExtension ArgInfo ← registerNameMapExtension _

@[inherit_doc TranslateData.doTranslateAttr]
initialize doTranslateAttr : NameMapExtension Bool ← registerNameMapExtension _

initialize
  registerBuiltinAttribute {
    name := `to_dual_do_translate
    descr := "Auxiliary attribute for `to_dual` stating \
      that the operations on this type should be translated."
    add name _ _ := doTranslateAttr.add name true }
  registerBuiltinAttribute {
    name := `to_dual_dont_translate
    descr := "Auxiliary attribute for `to_dual` stating \
      that the operations on this type should not be translated."
    add name _ _ := doTranslateAttr.add name false }

/-- Maps names to their dual counterparts. -/
initialize translations : NameMapExtension Name ← registerNameMapExtension _

@[inherit_doc GuessName.GuessNameData.nameDict]
def nameDict : Std.HashMap String (List String) := .ofList [
  ("top", ["Bot"]),
  ("bot", ["Top"]),
  ("inf", ["Sup"]),
  ("sup", ["Inf"]),
  ("min", ["Max"]),
  ("max", ["Min"]),
  ("untop", ["Unbot"]),
  ("unbot", ["Untop"]),
  ("minimal", ["Maximal"]),
  ("maximal", ["Minimal"]),
  ("lower", ["Upper"]),
  ("upper", ["Lower"]),

  ("epi", ["Mono"]),
  /- `mono` can also refer to monotone, so we don't translate it. -/
  -- ("mono", ["Epi"]),
  ("terminal", ["Initial"]),
  ("initial", ["Terminal"]),
  ("precompose", ["Postcompose"]),
  ("postcompose", ["Precompose"]),
  ("cone", ["Cocone"]),
  ("cocone", ["Cone"]),
  ("cones", ["Cocones"]),
  ("cocones", ["Cones"]),
  ("fan", ["Cofan"]),
  ("cofan", ["Fan"]),
  ("limit", ["Colimit"]),
  ("colimit", ["Limit"]),
  ("limits", ["Colimits"]),
  ("colimits", ["Limits"]),
  ("product", ["Coproduct"]),
  ("coproduct", ["Product"]),
  ("products", ["Coproducts"]),
  ("coproducts", ["Products"]),
  ("pushout", ["Pullback"]),
  ("pullback", ["Pushout"]),
  ("pushouts", ["Pullbacks"]),
  ("pullbacks", ["Pushouts"]),
  ("span", ["Cospan"]),
  ("cospan", ["Span"]),
  ("kernel", ["Cokernel"]),
  ("cokernel", ["Kernel"]),
  ("kernels", ["Cokernel"]),
  ("cokernels", ["Kernel"]),
  ("unit", ["Counit"]),
  ("counit", ["Unit"]),
  ("monad", ["Comonad"]),
  ("comonad", ["Monad"]),
  ("monadic", ["Comonadic"]),
  ("comonadic", ["Monadic"])]

@[inherit_doc GuessName.GuessNameData.abbreviationDict]
def abbreviationDict : Std.HashMap String String := .ofList [
  ("wellFoundedLT", "WellFoundedGT"),
  ("wellFoundedGT", "WellFoundedLT")
]

/-- The bundle of environment extensions for `to_dual` -/
def data : TranslateData where
  ignoreArgsAttr; argInfoAttr; doTranslateAttr; unfoldBoundaries; translations
  attrName := `to_dual
  changeNumeral := false
  isDual := true
  guessNameData := { nameDict, abbreviationDict }

initialize registerBuiltinAttribute {
    name := `to_dual
    descr := "Transport to dual"
    add := fun src stx kind ↦ discard do
      addTranslationAttr data src (← elabTranslationAttr src stx) kind
    applicationTime := .afterCompilation
  }

/-- This function is based on `Lean.Meta.mkSimpleEqThm`. -/
private def mkSimpleEqThm (declName : Name) (name : Name) (isThm : Bool)
    (mkTypeVal : Expr → Expr → MetaM (Expr × Expr)) : MetaM Unit := do
  let .defnInfo info ← getConstInfo declName | throwError "`{declName}` is not a definition"
  lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let lhs := mkAppN (mkConst info.name <| info.levelParams.map mkLevelParam) xs
    let (type, val) ← mkTypeVal lhs body
    let type ← mkForallFVars xs type
    let value ← mkLambdaFVars xs val
    addDecl <| ←
      if isThm then mkThmOrUnsafeDef {
        name, type, value
        levelParams := info.levelParams }
      else
        .defnDecl <$> mkDefinitionValInferringUnsafe name info.levelParams type value (.regular 0)

elab "to_dual_insert_cast" declName:ident " := " valStx:term : command => do
  let declName := declName.getId
  withDeclNameForAuxNaming declName do
  let name ← mkAuxDeclName `_to_dual_insert_cast
  Command.liftTermElabM do
    mkSimpleEqThm declName name true fun lhs body => return (← mkEq lhs body, ← mkEqRefl lhs)
  let dualName ← mkAuxDeclName `_to_dual_insert_cast
  Command.liftTermElabM do
    unfolds.add declName { origin := .decl name, proof := mkConst name, rfl := true }
    let cinfo ← getConstInfo name
    let dualType ← applyReplacementFun data cinfo.type
    let value ← forallTelescope dualType fun xs dualTypeBody => do
      -- Make the goal easier to prove by unfolding the lhs of the equality, if possible
      let dualTypeBody' ← (do
        if let mkApp2 eq lhs body := dualTypeBody then
          if let some lhs ← unfoldDefinition? lhs then
            return mkApp2 eq lhs body
        return dualTypeBody)
      let value ← elabTermEnsuringType valStx dualTypeBody'
      synthesizeSyntheticMVarsNoPostponing
      mkLambdaFVars xs (← instantiateMVars value)
    addDecl <| ← mkThmOrUnsafeDef {
      name := dualName, type := dualType, value
      levelParams := cinfo.levelParams }
  elabCommand <| ← `(command|
    attribute [to_dual existing $(mkIdent name):ident] $(mkIdent dualName))

elab "to_dual_insert_cast_fun" declName:ident " := " valStx₁:term ", " valStx₂:term : command => do
  let declName := declName.getId
  withDeclNameForAuxNaming declName do
  let name₁ ← mkAuxDeclName `_to_dual_insert_cast_fun
  Command.liftTermElabM do mkSimpleEqThm declName name₁ false fun lhs body =>
      return (.forallE `this lhs body .default, .lam `this lhs (.bvar 0) .default)
  let dualName₁ ← mkAuxDeclName `_to_dual_insert_cast_fun
  Command.liftTermElabM do
    let cinfo₁ ← getConstInfo name₁
    let dualType₁ ← applyReplacementFun data cinfo₁.type
    let value ← forallTelescope dualType₁ fun xs dualTypeBody => do
      let value ← elabTermEnsuringType valStx₁ dualTypeBody
      synthesizeSyntheticMVarsNoPostponing
      mkLambdaFVars xs (← instantiateMVars value)
    addDecl <| .defnDecl <|
      ← mkDefinitionValInferringUnsafe dualName₁ cinfo₁.levelParams dualType₁ value (.regular 0)
  elabCommand <| ← `(command|
    attribute [to_dual existing $(mkIdent name₁):ident] $(mkIdent dualName₁))
  insertionFuns.add name₁ ()
  insertionFuns.add dualName₁ ()

  let name₂ ← mkAuxDeclName `_to_dual_insert_cast_invFun
  casts.add declName (name₁, name₂)
  Command.liftTermElabM do
    mkSimpleEqThm declName name₂ false fun lhs body =>
      return (.forallE `this body lhs .default, .lam `this lhs (.bvar 0) .default)
  let dualName₂ ← mkAuxDeclName `_to_dual_insert_cast_invFun
  Command.liftTermElabM do
    let cinfo₂ ← getConstInfo name₂
    let dualType₂ ← applyReplacementFun data cinfo₂.type
    let value ← forallTelescope dualType₂ fun xs dualTypeBody => do
      let value ← elabTermEnsuringType valStx₂ dualTypeBody
      synthesizeSyntheticMVarsNoPostponing
      mkLambdaFVars xs (← instantiateMVars value)
    addDecl <| .defnDecl <|
      ← mkDefinitionValInferringUnsafe dualName₂ cinfo₂.levelParams dualType₂ value (.regular 0)
  elabCommand <| ← `(command|
    attribute [to_dual existing $(mkIdent name₂):ident] $(mkIdent dualName₂))
  insertionFuns.add name₂ ()
  insertionFuns.add dualName₂ ()

end Mathlib.Tactic.ToDual
