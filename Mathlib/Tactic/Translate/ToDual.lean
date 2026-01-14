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
  are dual to each other. Currently, this requires writing
  `attribute [to_dual existing le_add] add_le`.
-/

public meta section

namespace Mathlib.Tactic.ToDual
open Lean Meta Elab Term Command Std Translate UnfoldBoundary

@[inherit_doc TranslateData.ignoreArgsAttr]
syntax (name := to_dual_ignore_args) "to_dual_ignore_args" (ppSpace num)* : attr

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

Some definitions are dual to something other than the dual of their value. Some examples:
- `Ico a b := { x | a ≤ x ∧ x < b }` is dual to `Ioc b a := { x | b < x ∧ x ≤ a }`.
- `Monotone f := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b` is dual to itself.
- `DecidableLE α := ∀ a b : α, Decidable (a ≤ b)` is dual to itself.

To be able to translate a term involfing such constants, `to_dual` needs to insert casts,
so that the term's correctness doesn't rely on unfolding them.
You can instruct `to_dual` to do this using the `to_dual_insert_cast` or `to_dual_insert_cast_fun`
commands.

When troubleshooting `to_dual`, you can see what it is doing by replacing it with `to_dual?` and/or
by using `set_option trace.translate_detail true`.
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

@[inherit_doc TranslateData.unfoldBoundaries?]
def unfoldBoundaries? : Option UnfoldBoundaryExt := some { unfolds, casts, insertionFuns }

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
  ("succ", ["Pred"]),
  ("pred", ["Succ"]),
  ("ico", ["Ioc"]),
  ("ioc", ["Ico"]),
  ("iio", ["Ioi"]),
  ("ioi", ["Iio"]),
  ("ici", ["Iic"]),
  ("iic", ["Ici"]),
  ("u", ["L"]),
  ("l", ["U"]),
  ("disjoint", ["Codisjoint"]),
  ("codisjoint", ["Disjoint"]),

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
  ("kernels", ["Cokernels"]),
  ("cokernels", ["Kernels"]),
  ("unit", ["Counit"]),
  ("counit", ["Unit"]),
  ("monad", ["Comonad"]),
  ("comonad", ["Monad"]),
  ("monadic", ["Comonadic"]),
  ("comonadic", ["Monadic"])]

@[inherit_doc GuessName.GuessNameData.abbreviationDict]
def abbreviationDict : Std.HashMap String String := .ofList [
  ("wellFoundedLT", "WellFoundedGT"),
  ("wellFoundedGT", "WellFoundedLT"),
  ("succColimit", "SuccLimit"),
  ("predColimit", "PredLimit")
]

/-- The bundle of environment extensions for `to_dual` -/
def data : TranslateData where
  ignoreArgsAttr; argInfoAttr; doTranslateAttr; unfoldBoundaries?; translations
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

private inductive CastKind where
| eq | unfoldFun | refoldFun

private def CastKind.mkRel (lhs body : Expr) : CastKind → MetaM Expr
  | .eq => mkEq lhs body
  | .unfoldFun => return .forallE `_ lhs body .default
  | .refoldFun => return .forallE `_ body lhs .default

private def CastKind.mkProof (lhs : Expr) : CastKind → MetaM Expr
  | .eq => mkEqRefl lhs
  | _ => return .lam `_ lhs (.bvar 0) .default

private def elabInsertCast (declName : Name) (castKind : CastKind) (stx : Term) :
    CommandElabM (Name × Name) :=
  Command.liftTermElabM do withDeclNameForAuxNaming declName do withExporting do
  let .defnInfo info ← getConstInfo declName | throwError "`{declName}` is not a definition"
  lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let addDecl name type value : MetaM Unit := do
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs value
      addDecl <| ←
        if castKind matches .eq then
          mkThmOrUnsafeDef { name, type, value, levelParams := info.levelParams }
        else
          .defnDecl <$> mkDefinitionValInferringUnsafe name info.levelParams type value .opaque
    let lhs := mkAppN (.const info.name <| info.levelParams.map mkLevelParam) xs
    let name ← mkAuxDeclName `_to_dual_cast
    addDecl name (← castKind.mkRel lhs body) (← castKind.mkProof lhs)

    let dualLhs ← applyReplacementFun data lhs
    let dualBody ← applyReplacementFun data body
    let dualType ← castKind.mkRel dualLhs dualBody
    -- Make the goal easier to prove by unfolding the dual lhs
    let dualType' ← castKind.mkRel ((← unfoldDefinition? dualLhs).getD dualLhs) dualBody
    let dualValue ← elabTermEnsuringType stx dualType' <* synthesizeSyntheticMVarsNoPostponing
    let dualName ← mkAuxDeclName `_to_dual_cast
    addDecl dualName dualType (← instantiateMVars dualValue)

    let relevantArg? := (argInfoAttr.find? (← getEnv) declName).map (·.relevantArg)
    _ ← addTranslationAttr data name
      { tgt := dualName, existing := true, ref := .missing, relevantArg? }
    return (name, dualName)

/-- The `to_dual_insert_cast foo := ...` command should be used when the translation of some
definition `foo` is not definitionally equal to the translation of its value.
It requires a proof that these two are equal, which `by grind` can usually prove.

The command internally generates an unfolding theorem for `foo`, and a dual of this theorem.
When type checking a term requires the definition `foo` to be unfolded, then in order to translate
that term, a `cast` is first inserted into the term using this unfolding theorem.
As a result, type checking the term won't anymore require unfolding `foo`, so the term
can be safely translated. -/
elab "to_dual_insert_cast" declName:ident " := " valStx:term : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo declName
  let (name, _) ← elabInsertCast declName .eq valStx
  unfolds.add declName { origin := .decl name, proof := mkConst name, rfl := true }

/-- The `to_dual_insert_cast_fun foo := ...` command should be used when the translation of some
type `foo` is not definitionally equal to the translation of its value.
It requires a dual of the function that unfolds `foo` and of the function that refolds `foo`.

The command internally generates these unfold/refold functions for `foo`, and their duals.
If type checking a term requires the definition `foo` to be unfolded, then before translating
that term, the unfold/refold function is inserted into the term.
As a result, type checking the term won't anymore require unfolding `foo`, so the term
can be safely translated. After translating, the unfold/refold functions are again unfolded. -/
elab "to_dual_insert_cast_fun" declName:ident " := " valStx₁:term ", " valStx₂:term : command => do
  let declName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo declName
  let (name₁, dualName₁) ← elabInsertCast declName .unfoldFun valStx₁
  let (name₂, dualName₂) ← elabInsertCast declName .refoldFun valStx₂
  casts.add declName (name₁, name₂)
  insertionFuns.add name₁ (); insertionFuns.add dualName₁ ()
  insertionFuns.add name₂ (); insertionFuns.add dualName₂ ()

end Mathlib.Tactic.ToDual
