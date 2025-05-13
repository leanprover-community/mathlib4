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

def getHeader (fname : String) (keepTrailing : Bool) : IO String := do
  let fil := fname
  let fileContent ← IO.FS.readFile fil
  let (stx, _) ← Parser.parseHeader (Parser.mkInputContext fileContent fil)
  let stx := if keepTrailing then stx.raw else stx.raw.unsetTrailing
  let some substring := stx.getSubstring? | throw <| .userError "No substring: we have a problem!"
  let upToAllImports : Substring := {substring with startPos := 0}
  return upToAllImports.toString

def mkDeprecatedModule
    (fname : String) (customMessage : String := "auto-generated") (keepTrailing : Bool := false)
    (write : Bool := false) :
    CommandElabM Unit := do
  let msgStx := if customMessage.isEmpty then none else some <| Syntax.mkStrLit customMessage
  let dateStx := Syntax.mkStrLit s!"{← Std.Time.PlainDate.now}"
  let header ← getHeader fname keepTrailing
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

elab "#create_deprecated_modules" : command => do
  let oldFiles := Std.HashSet.ofArray (← IO.FS.lines "oldListOfFiles.txt")
  let currentFiles := Std.HashSet.ofArray (← IO.FS.lines "currentListOfFiles.txt")
  let onlyOld := oldFiles.filter (!currentFiles.contains ·)
  dbg_trace onlyOld.toArray
  for file in onlyOld do
    mkDeprecatedModule file

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
  let head ← getHeader fname false
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
  let head ← getHeader fname true
  logInfo head
