/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dump every cross-reference tag in Mathlib to TSV

```sh
lake env lean --run scripts/dump_crossref_tags.lean <out.tsv>
```

Loads the elaborated Mathlib environment, walks `Mathlib.CrossRef.tagExt`,
and writes one TSV record per tag:

```
<database>\t<tag>\t<declName>\t<module>\t<comment>
```

This is the only piece of cross-reference review machinery that has to live
in mathlib4: the rest (snippet fetching, filtering by PR diff, Markdown
rendering, comment posting) is in `leanprover-community/external-tags`
and `leanprover-community/mathlib-ci`. The TSV emitted here is treated as
untrusted data by the privileged workflow_run consumer.

Implementation: we use `importModules (loadExts := true)` rather than the
`withImportModules` wrapper, because the latter passes `loadExts := false`
and would leave `tagExt` empty for imported modules.

Hygiene: fields are normalised (tabs / newlines in comments become single
spaces) so they can't break the TSV framing, and the whole file is capped
at `maxBytes`. This script lives in `scripts/` and runs with the PR's
permissions, so the cap is defence-in-depth — the trusted consumer
(mathlib-ci's `post-comment.sh`) enforces its own cap on the artifact
before parsing.
-/

open Lean Mathlib.CrossRef

/-- Hard cap on the output. The current population is ~55 KB (491 tags);
2 MB is ample headroom. -/
def maxBytes : Nat := 2 * 1024 * 1024

/-- Replace tabs, newlines, and carriage returns with single spaces so a
field can't break the TSV framing. -/
def sanitiseField (s : String) : String :=
  s.replace "\t" " " |>.replace "\r\n" " " |>.replace "\n" " " |>.replace "\r" " "

/-- Convert a module name like `` `Mathlib.Algebra.Foo `` to its source path
(e.g. `"Mathlib/Algebra/Foo.lean"`). -/
def moduleToFilePath (m : Name) : String :=
  m.toString.replace "." "/" ++ ".lean"

unsafe def run (outPath : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[`Mathlib] {} 1024
  let tagsPair : List Tag × Array (Array Tag) :=
    PersistentEnvExtension.getState tagExt env
  let allTags := tagsPair.2.flatten.appendList tagsPair.1
  let mut rows : Array String := #[]
  for tag in allTags do
    let some mod := env.getModuleFor? tag.declName | continue
    let file := moduleToFilePath mod
    let dbName : String := match tag.database with
      | .kerodon  => "kerodon"
      | .stacks   => "stacks"
      | .wikidata => "wikidata"
    rows := rows.push s!"{dbName}\t{sanitiseField tag.tag}\t\
      {sanitiseField tag.declName.toString}\t\
      {sanitiseField file}\t{sanitiseField tag.comment}"
  let body := String.intercalate "\n" rows.toList ++ if rows.isEmpty then "" else "\n"
  if body.utf8ByteSize > maxBytes then
    throw <| .userError s!"dump exceeds {maxBytes} bytes (got {body.utf8ByteSize})"
  IO.FS.writeFile outPath body
  IO.eprintln s!"Wrote {rows.size} cross-reference tag(s) to {outPath} \
    ({body.utf8ByteSize} bytes)."
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [out] => run out
  | _ =>
    IO.eprintln "Usage: lake env lean --run scripts/dump_crossref_tags.lean <out.tsv>"
    return 64
