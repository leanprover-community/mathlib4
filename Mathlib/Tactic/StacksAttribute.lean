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

open Parser

/-- `stacksTag` is the node kind of Stacks Project Tags: a sequence of digits and
uppercase letters. -/
abbrev stacksTagKind : SyntaxNodeKind := `stacksTag

/-- The main parser for Stacks Project Tags: it accepts any letter or digit, even though
tags do not allow lowercase letters.
This allows for better error messages raised by the elaborator. -/
def stacksTagFn : ParserFn := fun c s =>
  let i := s.pos
  let st := takeWhileFn (·.isAlphanum) c s
  mkNodeToken stacksTagKind i c st

@[inherit_doc stacksTagFn]
def stacksTagNoAntiquot : Parser := {
  fn   := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]
def stacksTag : Parser :=
  withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

end Mathlib.Stacks

namespace Lean.PrettyPrinter
open Mathlib.Stacks

namespace Formatter

/-- The formatter for Stacks Project Tags syntax. -/
@[combinator_formatter stacksTagNoAntiquot] def stacksTagNoAntiquot.formatter :=
  visitAtom stacksTagKind

end Formatter

namespace Parenthesizer

/-- The parenthesizer for Stacks Project Tags syntax. -/
@[combinator_parenthesizer stacksTagNoAntiquot] def stacksTagAntiquot.parenthesizer := visitToken

end Lean.PrettyPrinter.Parenthesizer

namespace Mathlib.Stacks

/-- The `stacks` attribute.
Use it as `@[stacks TAG "Optional comment"]`.
The `TAG` is mandatory and should be a sequence of 4 digits or uppercase letters.

See the [Tags page](https://stacks.math.columbia.edu/tags) in the Stacks project for more details.
-/
syntax (name := stacks) "stacks " stacksTag (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `stacks
  descr := "Apply a Stacks project tag to a theorem."
  add := fun decl stx _attrKind => Lean.withRef stx do
    let `(attr| stacks $tag $[$comment]?) := stx | throwUnsupportedSyntax
    let str := tag.raw[0].getAtomVal
    if str.isEmpty then logWarning "Please, enter a Tag after `stacks`." else
    -- check that the tag consists of 4 characters
    if str.length != 4 then
      logWarningAt tag
        m!"Tag '{str}' is {str.length} characters long, but it should be 4 characters long"
    -- check that the tag only contains digits and uppercase letter
    else if str.any (·.isLower) then
      logWarningAt tag m!"Tag '{str}' should only consist of digits and uppercase letters"
    else
      addTagEntry decl str <| (comment.map (·.getString)).getD ""
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
