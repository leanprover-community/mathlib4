/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Mathlib.Init

/-!
# The `stacks` and `kerodon` attributes

This allows tagging of mathlib results with the corresponding
tags from the [Stacks Project](https://stacks.math.columbia.edu/tags) and
[Kerodon](https://kerodon.net/tag/).

While the Stacks Project is the main focus, because the tag format at Kerodon is
compatible, the attribute can be used to tag results with Kerodon tags as well.
-/

open Lean Elab

namespace Mathlib.StacksTag

/-- Web database users of projects tags -/
inductive Database where
  | kerodon
  | stacks
  deriving BEq, Hashable

/-- `Tag` is the structure that carries the data of a project tag and a corresponding
Mathlib declaration. -/
structure Tag where
  /-- The name of the declaration with the given tag. -/
  declName : Name
  /-- The online database where the tag is found. -/
  database : Database
  /-- The database tag. -/
  tag : String
  /-- The (optional) comment that comes with the given tag. -/
  comment : String
  deriving BEq, Hashable

/-- Defines the `tagExt` extension for adding a `HashSet` of `Tag`s
to the environment. -/
initialize tagExt : SimplePersistentEnvExtension Tag (Std.HashSet Tag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addTagEntry declName tag comment` takes as input the `Name` `declName` of a declaration and
the `String`s `tag` and `comment` of the `stacks` attribute.
It extends the `Tag` environment extension with the data `declName, tag, comment`.
-/
def addTagEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (db : Database) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })

open Parser

/-- `stacksTag` is the node kind of Stacks Project Tags: a sequence of digits and
uppercase letters. -/
abbrev stacksTagKind : SyntaxNodeKind := `stacksTag

/-- The main parser for Stacks Project Tags: it accepts any sequence of 4 digits or
uppercase letters. -/
def stacksTagFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "stacks tag"
  else
    let tag := c.extract i s.pos
    if !tag.all fun c => c.isDigit || c.isUpper then
      ParserState.mkUnexpectedError s
        "Stacks tags must consist only of digits and uppercase letters."
    else if tag.length != 4 then
      ParserState.mkUnexpectedError s "Stacks tags must be exactly 4 characters"
    else
      mkNodeToken stacksTagKind i c s

@[inherit_doc stacksTagFn]
def stacksTagNoAntiquot : Parser := {
  fn   := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]
def stacksTagParser : Parser :=
  withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

end Mathlib.StacksTag

open Mathlib.StacksTag

/-- Extract the underlying tag as a string from a `stacksTag` node. -/
def Lean.TSyntax.getStacksTag (stx : TSyntax stacksTagKind) : CoreM String := do
  let some val := Syntax.isLit? stacksTagKind stx | throwError "Malformed Stacks tag"
  return val

namespace Lean.PrettyPrinter

namespace Formatter

/-- The formatter for Stacks Project Tags syntax. -/
@[combinator_formatter stacksTagNoAntiquot] def stacksTagNoAntiquot.formatter :=
  visitAtom stacksTagKind

end Formatter

namespace Parenthesizer

/-- The parenthesizer for Stacks Project Tags syntax. -/
@[combinator_parenthesizer stacksTagNoAntiquot] def stacksTagAntiquot.parenthesizer := visitToken

end Lean.PrettyPrinter.Parenthesizer

namespace Mathlib.StacksTag

/-- The syntax category for the database name. -/
declare_syntax_cat stacksTagDB

/-- The syntax for a "kerodon" database identifier in a `@[kerodon]` attribute. -/
syntax "kerodon" : stacksTagDB
/-- The syntax for a "stacks" database identifier in a `@[stacks]` attribute. -/
syntax "stacks" : stacksTagDB

/-- The `stacksTag` attribute.
Use it as `@[kerodon TAG "Optional comment"]` or `@[stacks TAG "Optional comment"]`
depending on the database you are referencing.

The `TAG` is mandatory and should be a sequence of 4 digits or uppercase letters.

See the [Tags page](https://stacks.math.columbia.edu/tags) in the Stacks project or
[Tags page](https://kerodon.net/tag/) in the Kerodon project for more details.
-/
syntax (name := stacksTag) stacksTagDB stacksTagParser (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `stacksTag
  descr := "Apply a Stacks or Kerodon project tag to a theorem."
  add := fun decl stx _attrKind => do
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let (SorK, database, url, tag, comment) := ← match stx with
      | `(attr| stacks $tag $[$comment]?) =>
        return ("Stacks", Database.stacks, "https://stacks.math.columbia.edu/tag", tag, comment)
      | `(attr| kerodon $tag $[$comment]?) =>
        return ("Kerodon", Database.kerodon, "https://kerodon.net/tag", tag, comment)
      | _ => throwUnsupportedSyntax
    let tagStr ← tag.getStacksTag
    let comment := (comment.map (·.getString)).getD ""
    let commentInDoc := if comment = "" then "" else s!" ({comment})"
    let newDoc := [oldDoc, s!"[{SorK} Tag {tagStr}]({url}/{tagStr}){commentInDoc}"]
    addDocStringCore decl <| "\n\n".intercalate (newDoc.filter (· != ""))
    addTagEntry decl database tagStr <| comment
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

end Mathlib.StacksTag

/--
`getSortedStackProjectTags env` returns the array of `Tags`, sorted by alphabetical order of tag.
-/
private def Lean.Environment.getSortedStackProjectTags (env : Environment) : Array Tag :=
  tagExt.getState env |>.toArray.qsort (·.tag < ·.tag)

/--
`getSortedStackProjectDeclNames env tag` returns the array of declaration names of results
with Stacks Project tag equal to `tag`.
-/
private def Lean.Environment.getSortedStackProjectDeclNames (env : Environment) (tag : String) :
    Array Name :=
  let tags := env.getSortedStackProjectTags
  tags.filterMap fun d => if d.tag == tag then some d.declName else none

namespace Mathlib.StacksTag

private def databaseURL (db : Database) : String :=
  match db with
  | .kerodon => "https://kerodon.net/tag/"
  | .stacks => "https://stacks.math.columbia.edu/tag/"

/--
`traceStacksTags db verbose` prints the tags of the database `db` to the user and
inlines the theorem statements if `verbose` is `true`.
-/
def traceStacksTags (db : Database) (verbose : Bool := false) :
    Command.CommandElabM Unit := do
  let env ← getEnv
  let entries := env.getSortedStackProjectTags |>.filter (·.database == db)
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment ++ parR
    msgs := msgs.push
      m!"[Stacks Tag {d.tag}]({databaseURL db ++ d.tag}) \
        corresponds to declaration '{.ofConstName d.declName}'.{cmt}"
    if verbose then
      let dType := ((env.find? d.declName).getD default).type
      msgs := (msgs.push m!"{dType}").push ""
  let msg := MessageData.joinSep msgs.toList "\n"
  logInfo msg

/--
`#stacks_tags` retrieves all declarations that have the `stacks` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#stacks_tags!` also adds the theorem statement after each summary line.
-/
elab (name := stacksTags) "#stacks_tags" tk:("!")?: command =>
  traceStacksTags .stacks (tk.isSome)

/-- The `#kerodon_tags` command retrieves all declarations that have the `kerodon` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#kerodon_tags!` also adds the theorem statement after each summary line.
-/
elab (name := kerodonTags) "#kerodon_tags" tk:("!")?: command =>
  traceStacksTags .kerodon (tk.isSome)

end Mathlib.StacksTag
