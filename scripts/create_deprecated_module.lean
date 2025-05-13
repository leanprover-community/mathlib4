/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Lean.Elab.Command
import Mathlib.Tactic.Linter.DeprecatedModule
-- a comment here

/-!
#  Create a deprecated module

This file defines the lean script for creating a deprecated module.
-/

open Lean Elab Command

namespace DeprecatedModule

def getHeader (fname fileContent : String) (keepTrailing : Bool) : IO String := do
  let (stx, _) ← Parser.parseHeader (Parser.mkInputContext fileContent fname)
  let stx := if keepTrailing then stx.raw else stx.raw.unsetTrailing
  let some substring := stx.getSubstring? | throw <| .userError "No substring: we have a problem!"
  let upToAllImports : Substring := {substring with startPos := 0}
  return upToAllImports.toString

def getHeaderFromFileName (fname : String) (keepTrailing : Bool) : IO String := do
  getHeader fname (← IO.FS.readFile fname) keepTrailing

def mkDeprecation (customMessage : String := "auto-generated") : CommandElabM Format := do
  let msgStx := if customMessage.isEmpty then none else some <| Syntax.mkStrLit customMessage
  let dateStx := Syntax.mkStrLit s!"{← Std.Time.PlainDate.now}"
  let stx ← `(command|deprecated_module $[$msgStx]? (since := $dateStx))
  liftCoreM <| PrettyPrinter.ppCategory `command stx


def mkDeprecatedModule
    (fname : String) (customMessage : String := "auto-generated") (keepTrailing : Bool := false)
    (write : Bool := false) :
    CommandElabM Unit := do
  let msgStx := if customMessage.isEmpty then none else some <| Syntax.mkStrLit customMessage
  let dateStx := Syntax.mkStrLit s!"{← Std.Time.PlainDate.now}"
  let header ← getHeaderFromFileName fname keepTrailing
  let stx ← `(command|deprecated_module $[$msgStx]? (since := $dateStx))
  let fmt ← liftCoreM <| PrettyPrinter.ppCategory `command stx
  let nm := fname ++ "_deprecatedModule"
  unless (← System.FilePath.pathExists fname) do
    logWarning m!"The file '{fname}' was expected to exist: something went wrong!"
    return
  let fileContent := s!"{header.trimRight}\n\n{fmt}\n"
  logInfo m!"The file '{fname}' exists, as expected!\n\n\
          Its deprecated version is:\n--- Start ---\n{fileContent}--- End ---"
  if write then
    IO.FS.writeFile nm fileContent
  else
    logInfo m!"The file '{nm}' was not deprecated. Set `write := true` if you wish to deprecate it."
  --return
  --return s!"{header.trimRight}\n\n{fmt}\n"

elab "#create_deprecated_modules" write:(&" write")? : command => do
  let mut msgs := #[]
  let getHash (n : Nat) := do
    let log ← IO.Process.run {cmd := "git", args := #["log", "--pretty=oneline", s!"-{n}"]}
    let some last := log.trim.splitOn "\n" |>.getLast? | throwError "Found no commits!"
    let commitHash := last.takeWhile (!·.isWhitespace)
    return commitHash
  let getFilesAtHash (hash : String) := do
    let files ← IO.Process.run
      {cmd := "git", args := #["ls-tree", "-r", "--name-only", hash, "Mathlib/"]}
    let h : Std.HashSet String := .ofList <| files.splitOn "\n"
    return h
  let currentHash ← getHash 1
  let currentFiles ← getFilesAtHash currentHash
  msgs := msgs.push m!"{currentFiles.size} files at the current hash {currentHash}\n"
  let pastHash ← getHash 150
  let pastFiles ← getFilesAtHash pastHash
  msgs := msgs.push m!"{pastFiles.size} files at the past hash {pastHash}\n"
  let onlyPastFiles := pastFiles.filter fun fil ↦
    fil.takeRight ".lean".length == ".lean" &&
    !currentFiles.contains fil
  let noFiles := onlyPastFiles.size
  msgs := msgs.push
    m!"{noFiles} Lean file{if noFiles == 1 then "" else "s"} in 'Mathlib/' that no longer exist:"
  --msgs := msgs.push "" ++ (onlyPastFiles.toArray.map (indentD m!"{·}"))
  let deprecation ← mkDeprecation
  msgs := msgs.push ""
  for fname in onlyPastFiles do
    let file ← IO.Process.run {
      cmd := "git"
      args := #["show", s!"{pastHash}:{fname}"]
    }
    let fileHeader ← getHeader fname file false
    let deprecatedFile := s!"{fileHeader.trimRight}\n\n{deprecation.pretty.trimRight}\n"
    --dbg_trace "\nDeprecating {fname} as:\n\n---\n{deprecatedFile}---"
    msgs := msgs.push <| .trace {cls := `Deprecation} m!"{fname}" #[m!"\n{deprecatedFile}"]
    if write.isSome then
      IO.FS.writeFile fname deprecatedFile
  if write.isNone then
    msgs :=msgs.push
      m!"The files were not deprecated. Use '#create_deprecated_modules write' \
        if you wish to deprecate them."
  logInfo <| .joinSep msgs.toList "\n"

#create_deprecated_modules

/--
info: /-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Lean.Elab.Command
import Mathlib.Tactic.Linter.DeprecatedModule
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeaderFromFileName fname false
  logInfo head

/--
info: /-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Lean.Elab.Command
import Mathlib.Tactic.Linter.DeprecatedModule
-- a comment here
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeaderFromFileName fname true
  logInfo head
