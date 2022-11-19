/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Evgenia Karunus
-/

import Std.Util.TermUnsafe

/-!
# Documentation commands

We generate html documentation from mathlib source code.
Throughout mathlib, we add documentation entries using `add_tactic_doc` command.
Then [doc-gen](https://github.com/leanprover-community/doc-gen) calls `getTacticDocEntries`
to gather all documentation entries, and generate html docs.
-/

open Lean Elab

/-- The possible categories for `tacticDocEntry.category`. -/
inductive DocCategory where
  | tactic   : DocCategory
  | cmd      : DocCategory
  | hole_cmd : DocCategory
  | attr     : DocCategory
deriving Repr

/-- Prettier name for `docCategory`. -/
def DocCategory.toString : DocCategory → String
  | DocCategory.tactic   => "tactic"
  | DocCategory.cmd      => "command"
  | DocCategory.hole_cmd => "hole_command"
  | DocCategory.attr     => "attribute"

/-- The information used to generate a doc entry. -/
structure TacticDocEntry :=
  /-- Determines under which name the doc entry is shown in mathlib docs. -/
  name                     : String
  /-- Determines under which of predetermined sections (tactics, commands, etc.) this doc entry
  will lie in mathlib docs. -/
  category                 : DocCategory
  /-- Determines the links to which declarations are shown in mathlib docs.
  Can be used as a source of a docstring (second priority). -/
  decl_names               : List Lean.Name
  /-- Free-form tags, e.g. ["simplification", "decision procedure"]. -/
  tags                     : List String      := []
  /-- Can be used as a source of a docstring (first priority). -/
  inherit_description_from : Option Lean.Name := Option.none
deriving Repr

/-- Turns a `tacticDocEntry` into a JSON representation. -/
def TacticDocEntry.toJson (tde : TacticDocEntry) (description : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("name",       tde.name),
    ("category",   tde.category.toString),
    ("decl_names", Lean.Json.arr (List.toArray (tde.decl_names.map (λ x =>
      Lean.Json.str (toString x)
    )))),
    ("tags",        Lean.Json.arr (List.toArray (tde.tags.map Lean.Json.str))),
    ("description", description)
  ]

/--
Serves as a global storage for all `TacticDocEntry`s we have added throughout mathlib codebase.
When [doc-gen](https://github.com/leanprover-community/doc-gen) generates documentation, it will
access this storage to find each `tacticDocEntry` along with its greatest-priority docstring.
-/
initialize docNamesExtension : SimplePersistentEnvExtension
  (TacticDocEntry × String) (List (TacticDocEntry × String)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := λ _ => {}
    addEntryFn    := λ xs x => x :: xs
  }

/--
A command used to add documentation for a tactic, command, hole command, or attribute.

Usage: after defining an interactive tactic, command, or attribute,
add its documentation as follows.
```lean
/--
describe what the command does here
-/
add_tactic_doc
{ name := "display name of the tactic",
  category := cat,
  decl_names := [`dcl_1, `dcl_2],
  tags := ["tag_1", "tag_2"] }
```

The argument to `add_tactic_doc` is a structure of type `TacticDocEntry`.
* `name` refers to the display name of the tactic; it is used as the header of the doc entry.
* `category` refers to the category of doc entry.
  Options: `doc_category.tactic`, `doc_category.cmd`, `doc_category.hole_cmd`, `doc_category.attr`
* `decl_names` is a list of the declarations associated with this doc. For instance,
  the entry for `linarith` would set ``decl_names := [`tactic.interactive.linarith]``.
  Some entries may cover multiple declarations.
  It is only necessary to list the interactive versions of tactics.
* `tags` (optional) is a list of strings used to categorize entries.
* `inherit_description_from` (optional) is a name of the declaration that contains a docstring.

Now, the body of the doc entry is determined as follows:
* 1st priority: the docstring on top of the `add_tactic_doc` command call itself.
* 2nd priority: the docstring of the declaration from the `inherit_description_from` field.
* 3rd priotiy: if none of the above were found, and if `decl_names` contains
  one and only one declaration, we get the docstring from that declaration.

So, if there are multiple declarations, you can select the one to be used
by passing a name to the `inherit_description_from` field.
If you prefer your tactic/command/etc. to have a docstring that is different from
the online documentation entry, you should write the doc entry as a docstring for
the `add_tactic_doc` invocation.

Note that providing a badly formed `tactic_doc_entry` to the command can result in strange error
messages.
-/
elab metaDocString:docComment ? "add_tactic_doc " tdeStx:term : command => do
  -- 1. Turn tde:TSyntax argument into the actual tde:TacticDocEntry object
  let tdeName : Name ← resolveGlobalConstNoOverloadWithInfo tdeStx
  let tde : TacticDocEntry ← unsafe evalConstCheck TacticDocEntry ``TacticDocEntry tdeName
  -- 2. Determine tde's docstring
  let tdeDoc : String ←
    if let some metaDocString := metaDocString then
      let metaDocString ← getDocStringText metaDocString
      pure metaDocString
    else
      let inheritFrom ←
        match tde.inherit_description_from, tde.decl_names with
        | some x, _   => pure x
        | none,   [x] => pure x
        | none,    _  => throwError
        "A tactic doc entry must either:
        1. have a description written as a docstring for the `add_tactic_doc` invocation, or
        2. explicitly indicate the declaration to inherit the docstring from
        using `inherit_description_from`, or
        3. have a single declaration in the `decl_names` field, to inherit a docstring from."
      if let some docString ← findDocString? (← getEnv) inheritFrom then
        pure docString
      else
        throwError s!"${inheritFrom} has no docstring"
  -- 3. Add tde's name and docstring to the global storage (aka environment extension)
  let tdeAndDoc : TacticDocEntry × String := (tde, tdeDoc)
  modifyEnv (λ env => docNamesExtension.addEntry env tdeAndDoc)

/-- Returns all documentation entries (added via `add_tactic_doc` command) along with their
corresponding docstrings. -/
def tactic.getTacticDocEntries : CoreM (List (TacticDocEntry × String)) := do
  let env ← getEnv
  pure (docNamesExtension.getState env)
