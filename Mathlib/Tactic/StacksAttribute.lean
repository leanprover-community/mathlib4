/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
# The `stacks` attribute

This allows tagging of mathlib lemmas with the corresponding
[Tags](https://stacks.math.columbia.edu/tags) from the Stacks Project.
-/

open Lean

namespace Mathlib.Stacks

/-- `Tag` is the structure that carries the data to check if a declaration or an
import are meant to exist somewhere in Mathlib. -/
structure Tag where
  /-- The Stacks Project tag. -/
  tag : String
  /-- The name of the declaration with the given tag. -/
  declName : Name
  deriving BEq, Hashable

/-- Defines the `tagExt` extension for adding a `HashSet` of `Tag`s
to the environment. -/
initialize tagExt : SimplePersistentEnvExtension Tag (HashSet Tag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addTagEntry tag declName` takes as input the `String` `tag` and the `Name` `declName` of
a declaration with the `stacks` attribute.
It extends the `Tag` environment extension with the data `tag, declName`.
-/
def addTagEntry {m : Type → Type} [MonadEnv m] (tag : String) (declName : Name) : m Unit :=
  modifyEnv (tagExt.addEntry · { tag := tag, declName := declName })

/--
The syntax for a Stacks tag: it is an optional number followed by an optional identifier.
This allows `044Q3` and `GH3F6` as possibilities.
-/
declare_syntax_cat stackTag

@[inherit_doc Parser.Category.stackTag]
syntax (num)? (ident)? : stackTag

/-- The `stacks` attribute.
Use it as `@[stacks TAG "Optional comment"]`.
The `TAG` is mandatory.

See the [Tags page](https://stacks.math.columbia.edu/tags) in the Stacks project for more details.
-/
syntax (name := stacks) "stacks " (stackTag)? (ppSpace str)? : attr

initialize stacksTagAttribute : TagAttribute ←
  registerTagAttribute `stacks1 "hel"

initialize Lean.registerBuiltinAttribute {
  name := `stacks
  descr := "Apply a Stacks project tag to a theorem."
  add := fun decl stx _attrKind => Lean.withRef stx do
    -- check that the tag consists of 4 characters and
    -- that only digits and uppercase letter are present
    let tag := stx[1]
    match tag.getSubstring? with
      | none => logWarning "Please, enter a Tag after `stacks`."
      | some str =>
        let str := str.toString.trimRight
        if str.length != 4 then
          logWarningAt tag
            m!"Tag '{str}' is {str.length} characters long, but it should be 4 characters long"
        else if 2 ≤ (str.split (fun c => (!c.isUpper) && !c.isDigit)).length then
          logWarningAt tag m!"Tag '{str}' should only consist of digits and uppercase letters"
        else match stx with
          | `(attr| stacks $_:stackTag $_:str) => addTagEntry str decl
          | `(attr| stacks $_:stackTag) => addTagEntry str decl
          | _ => Elab.throwUnsupportedSyntax
}

end Mathlib.Stacks

open Mathlib.Stacks
/--
`getSortedTags env` returns the array of `Tags`, sorted by alphabetical order of declaration name.
-/
def _root_.Lean.Environment.getSortedTags (env : Environment) : Array Tag :=
  tagExt.getState env |>.toArray.qsort (·.declName.toString < ·.declName.toString)

open Elab Command in
/--
`#stacks_tags` retrieves all declarations that have the `stacks` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#stacks_tags!` also adds the theorem statement after each summary line.
-/
elab (name := Mathlib.Stacks.stacksTags) "#stacks_tags" tk:("!")?: command => do
  let env ← getEnv
  let entries := env.getSortedTags
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let dname ← liftCoreM do realizeGlobalConstNoOverloadWithInfo (mkIdent d.declName)
    msgs := msgs.push m!"'{dname}' corresponds to tag '{d.tag}'."
    if tk.isSome then
      let dType := ((env.find? dname).getD default).type
      msgs := (msgs.push m!"{dType}").push ""
  let msg := MessageData.joinSep msgs.toList "\n"
  logInfo msg
