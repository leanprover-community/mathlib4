/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Michael Rothgang
-/
module

public meta import Lean.Elab.Command
public meta import Mathlib.Util.SuggestAttr
public import Lean.Meta.Tactic.TryThis

/-!
# The `stacks`, `kerodon` and `informal` attributes

This allows tagging of mathlib results with a natural language concept name,
or the corresponding tags from the [Stacks Project](https://stacks.math.columbia.edu/tags) and
[Kerodon](https://kerodon.net/tag/).

The `informal` attribute allows annotating a declaration as corresponding to a natural language
mathematics concept (such as "linear map", "smooth manifold" or "Faltings' theorem").

While the Stacks Project is the main focus over Kerodon, because the tag format at Kerodon is
compatible, the attribute can be used to tag results with Kerodon tags as well.
-/

public meta section

open Lean Elab

namespace Mathlib.DatabaseTag

/-- Web database users of projects tags -/
inductive Database where
  | kerodon
  | stacks
  | informal
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

/-- Defines the `tagExt` extension for storing all `Tag`s in the environment.
`addImportedFn` is a constant function to avoid a performance overhead during initialization. -/
initialize tagExt : SimplePersistentEnvExtension Tag (Array (Array Tag)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn tags := tags
    addEntryFn tags _ := tags
  }

/--
`addTagEntry declName db tag comment` takes as input the `Name` `declName` of a declaration,
whether it is a Kerodon, Stacks tag or natural language concept (`db`),
the `String`s `tag` and `comment` of the `stacks` or `kerodon` attribute.
It extends the `Tag` environment extension with the data `declName, db, tag, comment`.
-/
def addTagEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (db : Database) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry ·
    { declName := declName, database := db, tag := tag, comment := comment })

/--
Gets the `db` tag entry for `declName` if there is one.
-/
def getTagEntry? (env : Environment) (declName : Name) (db : Database)
    (inCurrentModule? : Option Bool := none) : Option Tag := Id.run do
  if inCurrentModule?.isNone || inCurrentModule?.isEqSome true then
    for tag in tagExt.getEntries env do
      if tag.declName == declName && tag.database == db then
        return tag
  if inCurrentModule?.isNone || inCurrentModule?.isEqSome false then
    for tags in tagExt.getState env do
      for tag in tags do
        if tag.declName == declName && tag.database == db then
          return tag
  return none

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
    if !tag.all fun (c : Char) => c.isDigit || c.isUpper then
      ParserState.mkUnexpectedError s
        "Stacks tags must consist only of digits and uppercase letters."
    else if tag.length != 4 then
      ParserState.mkUnexpectedError s "Stacks tags must be exactly 4 characters"
    else
      mkNodeToken stacksTagKind i true c s

@[inherit_doc stacksTagFn]
def stacksTagNoAntiquot : Parser := {
  fn   := stacksTagFn
  info := mkAtomicInfo "stacksTag"
}

@[inherit_doc stacksTagFn]
def stacksTagParser : Parser :=
  withAntiquot (mkAntiquot "stacksTag" stacksTagKind) stacksTagNoAntiquot

end Mathlib.DatabaseTag

open Mathlib.DatabaseTag

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

namespace Mathlib.DatabaseTag

/-- The syntax category for the database name. -/
declare_syntax_cat stacksTagDB

/-- The syntax for a "kerodon" database identifier in a `@[kerodon]` attribute. -/
syntax "kerodon" : stacksTagDB
/-- The syntax for a "stacks" database identifier in a `@[stacks]` attribute. -/
syntax "stacks" : stacksTagDB

/-- The `informalMathTag` attribute. Use it as `@[informal "concept" "Optional comment"]` -/
syntax (name := informalMathTag) "informal" ppSpace str (ppSpace str)? : attr

-- TODO: can we this with the parser below?
/-- The `informal` attribute: use it as `@[informal "concept" "Optional comment"]`
to annotate a declaration corresponding to an informal concept (or result).
At the moment, no formatting restrictions on "concept" are imposed.
-/
initialize Lean.registerBuiltinAttribute {
  name := `informalMathTag
  descr := "Tag a declaration as corresponding to an informal math concept or result."
  add := fun decl stx _attrKind => do
    let (tag, comment) ← match stx with
    | `(attr| informal $tag $[$comment]?) => pure (tag, comment)
    | _ => throwUnsupportedSyntax
    addTagEntry decl .informal tag.getString ((comment.map (·.getString)).getD "")
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

@[specialize f]
private partial def foldKeysAsNamesAux {α} (acc : α) (pfx : Name) (f : α → Name → String → α) :
    Json → α
  | .obj t => t.foldl (init := acc) fun a k v => foldKeysAsNamesAux a (.str pfx k) f v
  | .str val => f acc pfx val
  | _ => acc

/-- Treats each path of keys as a name, and accumulates via `f acc keypath strVal` for each
`strVal` that's a string value of the (innermost) key. Ignores non-string values. -/
@[inline]
def _root_.Lean.Json.foldKeysAsNames {α} (json : Json) (f : α → Name → String → α) (init : α) : α :=
  foldKeysAsNamesAux init .anonymous f json

/-- `overview.json` as a `NameMap` from the decls that are the values in the json to the path of
keys that lead to them, represented as a `Name`. The innermost key is the last component of the
name. Not sure it's great to parse the whole file on every file load. -/
initialize mathOverview : NameMap Name ← do
  initSearchPath (← findSysroot)
  let file ← IO.FS.readFile <| (← IO.currentDir) / "docs" / "overview.json"
  let json ← match Json.parse file with
    | .ok json => pure json
    | .error e => throw <| .userError e
  return json.foldKeysAsNames (init := {}) fun m k v => m.insert v.toName k

/-- This should exist somewhere, right? -/
def _root_.Lean.Name.getSuffix : Name → String
  | .str _ suf => suf
  | .num pre _ => pre.getSuffix
  | .anonymous => "[anonymous]"

/-- Suggests adding `@[informal tag]` if `decl` exists in `overview.json`. `tag` is currently the
innermost key. -/
def addInformalTagFromOverview : Linter where
  run := insertAttrsOnDecls fun decl cmd => do
    if let some tag := mathOverview.get? decl then
      unless (getTagEntry? (← getEnv) decl .informal (inCurrentModule? := true)).isSome do
        let tagStr := Syntax.mkStrLit tag.getSuffix
        return #[← `(Parser.Term.attrInstance| informal $tagStr:str)]
    return #[]

initialize addLinter addInformalTagFromOverview

open Lean Elab Command

elab tk:"#imported_informal?" : command => do
  let env ← getEnv
  let mut attrs := #[]
  for (decl, fulltag) in mathOverview do
    unless env.contains decl do continue
    if env.isImportedConst decl then
    -- let some idx := env.getModuleIdxFor? decl | continue
    -- if !(`Mathlib).isPrefixOf env.header.moduleNames[idx]! then
      attrs := attrs.push (decl, ← `(command|
        attribute [informal $(Syntax.mkStrLit fulltag.getSuffix)] $(mkIdent decl)))
  liftCoreM do
    let attrs := attrs.qsort (·.1.lt ·.1)
    let attrs ← attrs.mapM fun (_, stx) => return (← PrettyPrinter.ppCommand stx).pretty
    let attrs := "\n".intercalate attrs.toList
    Meta.Tactic.TryThis.addSuggestion tk attrs

/-- Checks that every tag in the overview is reflected on a declaration in lean correctly. (Does
not check that every tag is in the overview.) -/
elab "#check_overview" : command => do
  let env ← getEnv
  let mut unknown := #[]
  let mut notLeanTagged := #[]
  let mut wrongTag := #[]
  for (decl, fulltag) in mathOverview do
    if !env.contains decl then
      unknown := unknown.push (decl, fulltag)
    else if let some tag := getTagEntry? env decl .informal then
      if tag.tag != fulltag.getSuffix then
        wrongTag := wrongTag.push (decl, fulltag, tag)
    else
      notLeanTagged := notLeanTagged.push (decl, fulltag)
  if unknown.isEmpty && notLeanTagged.isEmpty && wrongTag.isEmpty then
    logInfo m!"Every tag in the overview appears in Lean!"
  else
    let mut msgs := []
    unless wrongTag.isEmpty do
      let wrongTagMsgs := wrongTag.map fun (decl,fulltag,tag) =>
        m!"• {MessageData.ofConstName decl} @ {fulltag} is tagged in lean with \
        `@[informal {tag.tag}{tag.comment}]`"
      msgs := m!"Decalarations which have the wrong tag:\n\
        {m!"\n".joinSep wrongTagMsgs.toList}}" :: msgs
    unless notLeanTagged.isEmpty do
      let notLeanTaggedMsgs := notLeanTagged.map fun (decl,fulltag) =>
        m!"• {MessageData.ofConstName decl} @ {fulltag} is not tagged in lean."
      msgs := m!"Decalarations which are not tagged:\n\
        {m!"\n".joinSep notLeanTaggedMsgs.toList}}" :: msgs
    unless unknown.isEmpty do
      let unknownMsgs := unknown.map fun (decl,fulltag) =>
        m!"• {decl} @ {fulltag}"
      msgs := m!"Decalarations which could not be found:\n\
        {m!"\n".joinSep unknownMsgs.toList}}" :: msgs
    logWarning (m!"\n\n".joinSep msgs)

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
    let (SorK, database, url, tagStr, comment) := ← match stx with
      | `(attr| stacks $tag $[$comment]?) =>
        return ("Stacks", Database.stacks, "https://stacks.math.columbia.edu/tag", ← tag.getStacksTag, comment)
      | `(attr| kerodon $tag $[$comment]?) =>
        return ("Kerodon", Database.kerodon, "https://kerodon.net/tag", ← tag.getStacksTag, comment)
      | _ => throwUnsupportedSyntax
    let comment := (comment.map (·.getString)).getD ""
    let commentInDoc := if comment = "" then "" else s!" ({comment})"
    let newDoc := [oldDoc, s!"[{SorK} Tag {tagStr}]({url}/{tagStr}){commentInDoc}"]
    addDocStringCore decl <| "\n\n".intercalate (newDoc.filter (· != ""))
    addTagEntry decl database tagStr <| comment
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

end Mathlib.DatabaseTag

/--
`getSortedStackProjectTags env` returns the array of `Tags`, sorted by alphabetical order of tag.
-/
private def Lean.Environment.getSortedStackProjectTags (env : Environment) : Array Tag :=
  let tags := PersistentEnvExtension.getState tagExt env
  tags.2.flatten.appendList tags.1 |>.qsort (·.tag < ·.tag)

/--
`getSortedStackProjectDeclNames env tag` returns the array of declaration names of results
with Stacks Project tag equal to `tag`.
-/
private def Lean.Environment.getSortedStackProjectDeclNames (env : Environment) (tag : String) :
    Array Name :=
  let tags := env.getSortedStackProjectTags
  tags.filterMap fun d => if d.tag == tag then some d.declName else none

namespace Mathlib.DatabaseTag

private def databaseURL (db : Database) : String :=
  match db with
  | .kerodon => "https://kerodon.net/tag/"
  | .stacks => "https://stacks.math.columbia.edu/tag/"
  | .informal => ""

/--
`traceDatabaseTags db verbose` prints the tags of the database `db` to the user and
inlines the theorem statements if `verbose` is `true`.
-/
def traceDatabaseTags (db : Database) (verbose : Bool := false) :
    Command.CommandElabM Unit := do
  let env ← getEnv
  let entries := env.getSortedStackProjectTags |>.filter (·.database == db)
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment ++ parR
    let start := if db == Database.informal then m!"informal concept \"{d.tag}\"" else
      s!"[Stacks Tag {d.tag}]({databaseURL db ++ d.tag})"
    msgs := msgs.push m!"{start} corresponds to declaration '{.ofConstName d.declName}'.{cmt}"
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
The variant `#stacks_tags!` also adds the theorem statement (for theorems)
or declaration type (for definitions, structures, instances, etc.) after each summary line.
-/
elab (name := stacksTags) "#stacks_tags" tk:("!")? : command =>
  traceDatabaseTags .stacks (tk.isSome)

/-- The `#kerodon_tags` command retrieves all declarations that have the `kerodon` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#kerodon_tags!` also adds the theorem statement (for theorems)
or declaration type (for definitions, structures, instances, etc.) after each summary line.
-/
elab (name := kerodonTags) "#kerodon_tags" tk:("!")? : command =>
  traceDatabaseTags .kerodon (tk.isSome)

/--
`#informal_concepts` retrieves all declarations that have the `informal` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `informal_concepts!` also adds the theorem statement after each summary line.
-/
elab (name := informalConcepts) "#informal_concepts" tk:("!")?: command =>
  traceDatabaseTags Database.informal (tk.isSome)

end Mathlib.DatabaseTag
