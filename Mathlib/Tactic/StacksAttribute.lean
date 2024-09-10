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

open Lean Elab

namespace Mathlib.Stacks

/-- `Tag` is the structure that carries the data of a Stacks Projects tag and a corresponding
Mathlib declaration. -/
structure Tag where
  /-- The name of the declaration with the given tag. -/
  declName : Name
  /-- The Stacks Project tag. -/
  tag : String
  /-- The (optional) comment that comes with the given tag. -/
  comment : String
  deriving BEq, Hashable

/-- Defines the `tagExt` extension for adding a `HashSet` of `Tag`s
to the environment. -/
initialize tagExt : SimplePersistentEnvExtension Tag (HashSet Tag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addTagEntry declName tag comment` takes as input the `Name` `declName` of a declaration and
the `String`s `tag` and `comment` of the `stacks` attribute.
It extends the `Tag` environment extension with the data `declName, tag, comment`.
-/
def addTagEntry {m : Type → Type} [MonadEnv m] (declName : Name) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry · { declName := declName, tag := tag, comment := comment })

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
          | `(attr| stacks $_:stackTag $comment:str) => addTagEntry decl str comment.getString
          | `(attr| stacks $_:stackTag) => addTagEntry decl str ""
          | _ => throwUnsupportedSyntax
}

end Mathlib.Stacks

open Mathlib.Stacks
/--
`getSortedStackProjectTags env` returns the array of `Tags`, sorted by alphabetical order of tag.
-/
def Lean.Environment.getSortedStackProjectTags (env : Environment) : Array Tag :=
  tagExt.getState env |>.toArray.qsort (·.tag < ·.tag)

/--
`getSortedStackProjectDeclNames env tag` returns the array of declaration names of results
with Stacks Project tag equal to `tag`.
-/
def Lean.Environment.getSortedStackProjectDeclNames (env : Environment) (tag : String) :
    Array Name :=
  let tags := env.getSortedStackProjectTags
  tags.filterMap fun d => if d.tag == tag then some d.declName else none

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
  let entries := env.getSortedStackProjectTags
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let dname ← Command.liftCoreM do realizeGlobalConstNoOverloadWithInfo (mkIdent d.declName)
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment ++ parR
    msgs := msgs.push
      m!"[Stacks Tag {d.tag}](https://stacks.math.columbia.edu/tag/{d.tag}) \
        corresponds to declaration '{dname}'.{cmt}"
    if tk.isSome then
      let dType := ((env.find? dname).getD default).type
      msgs := (msgs.push m!"{dType}").push ""
  let msg := MessageData.joinSep msgs.toList "\n"
  logInfo msg
