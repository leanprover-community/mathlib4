/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Data.Json
import NoExpose.Paths

/-!
# `NoExpose.Restore` — backup, restore, orphan detection

Tiny safety wrapper around "modify a file, run something, put it
back." Used by `NoExpose.Diagnostics` (lakefile patch + per-file
patches) and by `NoExpose.Edit` to keep an audit trail.

* `backup path`: copy `path` into `restoreDir` under a sanitised name,
  recording the mapping in `state.json`.
* `restoreAll`: read `state.json`, copy every backup back to its
  original location, then `rm -rf` `restoreDir`.
* `detectOrphan`: at startup, if `state.json` exists, prompt/restore
  before continuing — this means a previous `collect` was killed
  mid-run and the source tree is still patched.
* `withBackups [paths] body`: bracket pattern. Backs up every path,
  runs `body`, restores in `finally` even on exception.
-/

open System Lean

namespace NoExpose

/-- Sanitise a path into a flat backup file name.
`Mathlib/Foo/Bar.lean` → `Mathlib_Foo_Bar.lean`. -/
private def sanitise (p : FilePath) : String :=
  p.toString.replace "/" "_" |>.replace "\\" "_"

/-- One entry in `state.json`: original path + backup path. -/
structure RestoreEntry where
  original : String
  backup   : String
  deriving Inhabited

private def entryToJson (e : RestoreEntry) : Json :=
  Json.mkObj [("original", e.original), ("backup", e.backup)]

private def parseStateFile (s : String) : Array RestoreEntry :=
  match Json.parse s with
  | .error _ => #[]
  | .ok j => Id.run do
    let arr := j.getObjVal? "entries" |>.toOption |>.bind (·.getArr?.toOption)
              |>.getD #[]
    let mut out : Array RestoreEntry := #[]
    for entry in arr do
      let some original := entry.getObjValAs? String "original" |>.toOption | continue
      let some backup := entry.getObjValAs? String "backup" |>.toOption | continue
      out := out.push { original, backup }
    return out

private def writeStateFile (entries : Array RestoreEntry) : IO Unit := do
  IO.FS.createDirAll restoreDir
  let body := Json.mkObj [("entries", Json.arr (entries.map entryToJson))]
  IO.FS.writeFile restoreStatePath body.compress

private def readStateFile : IO (Array RestoreEntry) := do
  if ← System.FilePath.pathExists restoreStatePath then
    let s ← IO.FS.readFile restoreStatePath
    return parseStateFile s
  return #[]

/-- Copy `path` into `restoreDir` and append it to the state file. Idempotent:
calling twice with the same path is a no-op. -/
def backup (path : FilePath) : IO Unit := do
  IO.FS.createDirAll restoreDir
  let entries ← readStateFile
  let pathStr := path.toString
  if entries.any (·.original == pathStr) then return
  unless ← System.FilePath.pathExists path do
    throw <| IO.userError s!"NoExpose.backup: {pathStr} does not exist"
  let bkName := sanitise path
  let bkPath := restoreDir / bkName
  IO.FS.writeFile bkPath (← IO.FS.readFile path)
  writeStateFile (entries.push { original := pathStr, backup := bkPath.toString })

/-- Restore all backups recorded in `state.json`, then remove `restoreDir`. -/
def restoreAll : IO Unit := do
  let entries ← readStateFile
  for e in entries do
    if ← System.FilePath.pathExists e.backup then
      let content ← IO.FS.readFile e.backup
      IO.FS.writeFile e.original content
  if ← System.FilePath.pathExists restoreDir then
    IO.FS.removeDirAll restoreDir

/-- Called at every startup. If `state.json` exists, a previous `collect`
was interrupted; restore everything before continuing. -/
def detectOrphan : IO Unit := do
  unless ← System.FilePath.pathExists restoreStatePath do return
  let entries ← readStateFile
  if entries.isEmpty then
    if ← System.FilePath.pathExists restoreDir then
      IO.FS.removeDirAll restoreDir
    return
  IO.eprintln s!"[no_expose] detected {entries.size} orphan backup(s) from a previous run; restoring."
  restoreAll

/-- Bracket pattern: back up every path, run `body`, restore even on
exception. Returns `body`'s result. -/
def withBackups {α : Type} (paths : Array FilePath) (body : IO α) : IO α := do
  for p in paths do backup p
  try
    let r ← body
    restoreAll
    return r
  catch e =>
    restoreAll
    throw e

end NoExpose
