import Mathlib

/-
Usage:

```bash
lake env lean scripts/undocumented_tactics.lean
```
to list tactics without documentation.

```
COUNT_ONLY=1 lake env lean scripts/undocumented.tactics.lean
```
to report the total count (for use in the weekly tech debt metric report).
-/

open Lean Parser Elab Command

open Tactic.Doc

/-- Does this tactic have a docstring, or an `extensionDoc` defined later? -/
def isNonemptyDoc (doc : TacticDoc) : Bool :=
  doc.docString.isSome || doc.extensionDocs.any (! ·.isEmpty)

/-- Count or list the undocumented tactics available in Mathlib.

If the environment variable `COUNT_ONLY` is set to `"1"`, then this reports a number,
otherwise it prints a list of undocumented tactics.
-/
def undocumentedTactics : CommandElabM Unit := liftTermElabM do
  let env ← getEnv

  -- Find all tactics. Deduplicate them according to the `@[tactic_alt]` attribute.
  let tactics := (Parser.getParserCategory? env `tactic).get!
  let dedupTactics := tactics.kinds.toArray.map Prod.fst |>.filter
    fun tac => (alternativeOfTactic env tac).isNone
  -- Find the associated documentation.
  let docs ← Tactic.Doc.allTacticDocs
  let docMap : NameMap _ := docs.foldl (init := {}) fun m doc =>
    m.insert doc.internalName doc
  -- This `get?` should not return `none` for normally declared tactics,
  -- but if we do environment manipulation it might give us weird results.
  -- So we keep track of the original tactic declaration name too.
  let tacticDocs := dedupTactics.map fun tac => (tac, docMap.get? tac)
  let emptyTacticDocs := tacticDocs.filter fun (_, doc) => !doc.any isNonemptyDoc

  if (← IO.getEnv "COUNT_ONLY").any (· == "1") then
    IO.println s!"{emptyTacticDocs.size}|tactics without documentation"
  else if emptyTacticDocs.size > 0 then
    IO.println s!"The following {emptyTacticDocs.size} tactics have no docstrings.\n\
    Hint: put a docstring on the declaration, or use the `@[tactic_alt]` attribute.\n"
    for (tac, doc) in emptyTacticDocs do
      if let some doc := doc then
        IO.println s!"{doc.userName}, declaration: {doc.internalName}"
      else
        IO.println s!"<unknown> (cause: missing `TacticDoc`), declaration: {tac}"
  else
    IO.println "All tactics have a docstring."

run_cmd undocumentedTactics
