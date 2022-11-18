import Std.Util.TermUnsafe
open Lean Elab

inductive DocCategory where
  | tactic   : DocCategory
  | cmd      : DocCategory
  | hole_cmd : DocCategory
  | attr     : DocCategory
deriving Repr

def DocCategory.toString : DocCategory → String
  | DocCategory.tactic   => "tactic"
  | DocCategory.cmd      => "command"
  | DocCategory.hole_cmd => "hole_command"
  | DocCategory.attr     => "attribute"

structure TacticDocEntry :=
  name                     : String
  category                 : DocCategory
  decl_names               : List Lean.Name
  tags                     : List String      := []
  inherit_description_from : Option Lean.Name := Option.none
deriving Repr

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

initialize docNamesExtension : SimplePersistentEnvExtension (TacticDocEntry × String) (List (TacticDocEntry × String)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := λ _ => {}
    addEntryFn    := λ xs x => x :: xs
  }

elab "add_tactic_doc " tdeStx:term : command => do
  -- 1. Turn tde:TSyntax argument into the actual tde:TacticDocEntry object
  let tdeName : Name ← resolveGlobalConstNoOverloadWithInfo tdeStx
  let tde : TacticDocEntry ← unsafe evalConstCheck TacticDocEntry ``TacticDocEntry tdeName
  -- 2. Determine tde's docstring
  let tdeDoc ←
    if let some docString ← findDocString? (← getEnv) tdeName then
      pure docString
    else
      let inheritFrom ←
        match tde.inherit_description_from, tde.decl_names with
        | some x, _   => pure x
        | none,   [x] => pure x
        | none,    _  => throwError
        "A tactic doc entry must either:
        1. have a description written as a doc-string for the `add_tactic_doc` invocation, or
        2. have a single declaration in the `decl_names` field, to inherit a description from, or
        3. explicitly indicate the declaration to inherit the description from using `inherit_description_from`."
      if let some docString ← findDocString? (← getEnv) inheritFrom then
        pure docString
      else
        throwError s!"${inheritFrom} has no doc string"
  -- 3. Add tde's name and docstring to the global storage (aka environment extension)
  let tdeAndDoc : TacticDocEntry × String := (tde, tdeDoc)
  modifyEnv (λ env => docNamesExtension.addEntry env tdeAndDoc)

def tactic.getTacticDocEntries : CoreM (List (TacticDocEntry × String)) := do
  let env ← getEnv
  pure (docNamesExtension.getState env)
