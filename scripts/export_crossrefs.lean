/-
Copyright (c) 2026 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
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

/-- The source file and 1-based line number of `decl`, if known. -/
def declLocation (env : Environment) (decl : Name) : Option (String × Nat) := do
  let ranges ← declRangeExt.find? (level := .exported) env decl <|>
                declRangeExt.find? (level := .server) env decl
  let mod ← env.getModuleFor? decl
  return (mod.toString, ranges.range.pos.line)

/-- One JSON entry per declaration, sorted by declaration name. A declaration carrying several
cross-references (e.g. both a Stacks and a Wikidata tag) gets a single entry with multiple `refs`. -/
def buildEntries (env : Environment) : Array Json := Id.run do
  let mut byDecl : Std.HashMap Name (Array Tag) := {}
  let (localTags, importedTags) := PersistentEnvExtension.getState tagExt env
  for tags in importedTags do
    for tag in tags do
      byDecl := byDecl.alter tag.declName fun val? => val?.getD #[] |>.push tag
  for tag in localTags do
    byDecl := byDecl.alter tag.declName fun val? => val?.getD #[] |>.push tag
  let sorted := byDecl.toArray.qsort fun a b => a.1.toString < b.1.toString
  sorted.map fun (decl, tags) =>
    -- Canonical ref order (by database, then id) keeps the published file stable.
    let tags := tags.qsort fun a b =>
      (compare a.database b.database).then (compare a.tag b.tag) |>.isLT
    let refs : Array Json := tags.map fun t =>
      json% { db : $(t.database.shortName), id : $(t.tag), comment : $(t.comment) }
    let (mod, line) := declLocation env decl |>.getD ("", 0)
    json% { decl : $(decl.toString), module : $(mod), line : $(line), refs : $(refs) }

end ExportCrossRefs

open ExportCrossRefs in
run_cmd do
  let entries := buildEntries (← getEnv)
  let now ← IO.Process.run { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  let json := json% {
    generated :  $(now.trimAscii.toString),
    commit : $((← IO.getEnv "CROSSREFS_COMMIT").getD "unknown"),
    entries : $(entries)
  }
  let path := (← IO.getEnv "CROSSREFS_OUT").getD "crossrefs.json"
  IO.FS.writeFile path (json.pretty ++ "\n")
  logInfo m!"Wrote {entries.size} cross-reference entries to {path}"
