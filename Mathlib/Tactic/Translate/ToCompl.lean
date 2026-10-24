/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Bryan Gin-ge Chen, Snir Broshi
-/
module

public import Mathlib.Tactic.Translate.TagUnfoldBoundary

/-!
# The `@[to_compl]` attribute.

The `@[to_compl]` attribute is used to translate declarations to their complemented versions.
-/

public meta section

namespace Mathlib.Tactic.ToCompl
open Lean Meta Elab Command Std Translate UnfoldBoundary

@[inherit_doc TranslateData.dontTranslateAttr]
syntax (name := to_compl_do_translate) "to_compl_do_translate" : attr

@[inherit_doc TranslateData.dontTranslateAttr]
syntax (name := to_compl_dont_translate) "to_compl_dont_translate" : attr

/-- The attribute `to_compl` can be used to automatically transport theorems
and definitions (but not inductive types and structures) to their compl version.
It uses the same implementation as `to_dual`. -/
syntax (name := to_compl) "to_compl" "?"? attrArgs : attr

@[inherit_doc to_compl]
macro "to_compl?" rest:attrArgs : attr => `(attr| to_compl ? $rest)

@[inherit_doc TranslateData.dontTranslateAttr]
initialize dontTranslateAttr : NameMapExtension Unit ← registerNameMapExtension _

/-- Maps names to their complemented counterparts. -/
initialize translations : NameMapExtension TranslationInfo ← registerNameMapExtension _

initialize
  registerBuiltinAttribute {
    name := `to_compl_do_translate
    descr := "Auxiliary attribute for `to_compl` stating \
      that the operations on this type should be translated."
    add name _ _ := translations.add name { translation := name, relevantArg := .noArg} }
  registerBuiltinAttribute {
    name := `to_compl_dont_translate
    descr := "Auxiliary attribute for `to_compl` stating \
      that the operations on this type should not be translated."
    add name _ _ := dontTranslateAttr.add name () }

@[inherit_doc GuessName.GuessNameExt]
initialize guessNameExt : GuessName.GuessNameExt ←
  GuessName.registerGuessNameExt { nameDict := .ofList [], abbreviationDict := .ofList [] }


/-- The bundle of environment extensions for `to_compl` -/
def data : TranslateData where
  dontTranslateAttr; translations
  attrName := `to_compl
  changeNumeral := false
  isDual := false
  guessNameExt

/-- The `to_compl_insert_cast` attribute is used to tag declarations `foo` that should not be
unfolded in a proof that is translated. Instead, a rewrite with an equality theorem is inserted.
This equality theorem can then be translated by the translation attribute. -/
elab "to_compl_insert_cast" declName:ident " := " valStx:term : command =>
  elabInsertCast declName valStx data

/-- The `to_compl_insert_cast_fun` attribute is used to tag types that should not be unfolded in a
proof that is translated. Instead, a casting function is inserted. This casting function then may be
translated by the translation attribute. -/
elab "to_compl_insert_cast_fun" declName:ident " := " valStx₁:term ", " valStx₂:term : command =>
  elabInsertCastFun declName valStx₁ valStx₂ data

initialize registerBuiltinAttribute {
    name := `to_compl
    descr := "Transport to complement"
    add := fun src stx kind ↦ discard do
      profileitM Exception "to_compl" (← getOptions) do
        addTranslationAttr data src (← elabTranslationAttr src stx) kind
    applicationTime := .afterCompilation
  }

/-- `insert_to_compl_translation name complName` inserts the translation `name → complName`
into the `to_compl` dictionary. This is useful for translating namespaces that don't (yet)
have a corresponding translated declaration. -/
elab "insert_to_compl_translation" src:ident tgt:ident : command => do
  translations.add src.getId { translation := tgt.getId }

/-- `to_compl_name_hint src₁ tgt₁, ..., srcₙ tgtₙ` lets `to_compl` translate between the name
segments `srcᵢ` and `tgtᵢ` for the rest of the file current. The name segments should be
capitalized. -/
elab "to_compl_name_hint" hints:(ident ident),* : command => do
  for ⟨hint⟩ in hints.getElems do
    guessNameExt.addTranslation ⟨hint[0]⟩ ⟨hint[1]⟩

/-- `to_compl_for src := e` tells `to_compl` to translate the constant `src` to `e`,
where `e` can be an arbitrary expression.

TODO: this currently doesn't accept the `(dont_translate := ...)`/`(relevant_arg := ...)` syntax.
  This can be added if necessary.
-/
elab tk:"to_compl_for" src:ident " := " tgt:term : command => Command.liftTermElabM do
  let src ← realizeGlobalConstNoOverloadWithInfo src
  withRef tk do
    addTranslationFor data src tgt (dontTranslate := []) (relevantArg? := none)

end Mathlib.Tactic.ToCompl
