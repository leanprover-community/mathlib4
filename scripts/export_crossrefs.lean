/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Export cross-reference data as JSON

Elaborating this file writes a JSON file listing every Mathlib declaration tagged with
`@[wikidata ...]`, `@[stacks ...]`, or `@[kerodon ...]`, together with its source file, line
number, and the referenced identifiers.

The cross-references are read from the ambient environment (like the `#stacks_tags` command), so
the file must be run with the full `Mathlib` import elaborated:

  lake env lean scripts/export_crossrefs.lean

The output path is taken from the `CROSSREFS_OUT` environment variable (default `crossrefs.json`)
and the recorded source commit from `CROSSREFS_COMMIT` (default `unknown`).
-/

open Lean Mathlib.CrossRef Elab Command

namespace ExportCrossRefs

/-- The relative source path of a module: `Mathlib.Data.Nat.Basic ↦ Mathlib/Data/Nat/Basic.lean`. -/
meta def moduleFile (mod : Name) : String :=
  mod.toString.replace "." "/" ++ ".lean"

/-- The source file and 1-based line number of `decl`, if known. -/
meta def declLocation (env : Environment) (decl : Name) : Option (String × Nat) := do
  let ranges ← declRangeExt.find? (level := .exported) env decl <|>
                declRangeExt.find? (level := .server) env decl
  let mod := env.header.moduleNames[(← env.getModuleIdxFor? decl).toNat]!
  return (moduleFile mod, ranges.range.pos.line)

/-- Every cross-reference tag recorded in `env`, across all databases. -/
meta def allCrossRefs (env : Environment) : Array Tag :=
  let (localTags, importedTags) := PersistentEnvExtension.getState tagExt env
  importedTags.flatten.appendList localTags

meta def dbName : Database → String
  | .kerodon  => "kerodon"
  | .stacks   => "stacks"
  | .wikidata => "wikidata"

/-- One JSON entry per declaration, sorted by declaration name. A declaration carrying several
cross-references (e.g. both a Stacks and a Wikidata tag) gets a single entry with multiple `refs`. -/
meta def buildEntries (env : Environment) : Array Json :=
  let byDecl : Std.HashMap Name (Array Tag) :=
    (allCrossRefs env).foldl (init := {}) fun m t =>
      m.insert t.declName ((m[t.declName]?.getD #[]).push t)
  let sorted := byDecl.toArray.qsort fun a b => a.1.toString < b.1.toString
  sorted.map fun (decl, tags) =>
    -- Canonical ref order (by database, then id) keeps the published file stable.
    let tags := tags.qsort fun a b =>
      dbName a.database < dbName b.database ||
        (dbName a.database == dbName b.database && a.tag < b.tag)
    let refs : Array Json := tags.map fun t =>
      Json.mkObj [("db", .str (dbName t.database)), ("id", .str t.tag), ("comment", .str t.comment)]
    let (file, line) := declLocation env decl |>.getD ("", 0)
    Json.mkObj [("decl", .str decl.toString), ("file", .str file), ("line", .num line),
      ("refs", .arr refs)]

end ExportCrossRefs

open ExportCrossRefs in
run_cmd do
  let entries := buildEntries (← getEnv)
  let now ← IO.Process.run { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  let json := Json.mkObj [
    ("generated", .str now.trimAscii.toString),
    ("commit",    .str ((← IO.getEnv "CROSSREFS_COMMIT").getD "unknown")),
    ("entries",   .arr entries)
  ]
  let path := (← IO.getEnv "CROSSREFS_OUT").getD "crossrefs.json"
  IO.FS.writeFile path (json.pretty ++ "\n")
  logInfo m!"Wrote {entries.size} cross-reference entries to {path}"
