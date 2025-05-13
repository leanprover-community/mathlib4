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
  if (← System.FilePath.pathExists nm) then
    logWarning m!"A file called '{nm}' exists, not writing over it!"
    return
  logInfo "Continuing"
  let fileContent := s!"{header.trimRight}\n\n{fmt}\n"
  dbg_trace fileContent
  if write then
    IO.FS.writeFile nm fileContent
  else
    logInfo m!"File '{nm}' not written. Set `write := true` if you wish to create it."
  --return
  --return s!"{header.trimRight}\n\n{fmt}\n"
#check Std.HashSet
run_cmd
  let oldFiles := Std.HashSet.ofArray (← IO.FS.lines "oldListOfFiles.txt")
  let currentFiles := Std.HashSet.ofArray (← IO.FS.lines "currentListOfFiles.txt")
  let onlyOld := oldFiles.filter (!currentFiles.contains ·)

  dbg_trace onlyOld.toArray
  for file in onlyOld do
    mkDeprecatedModule file
  --IO.Process.run {cmd := "comm", args := #["-13", "<(sort currentListOfFiles.txt)", "<(sort oldListOfFiles.txt)"]}
--run_cmd
--  mkDeprecatedModule (← getFileName)

run_cmd
  let fname := "Mathlib/Init.lean"
  let fname := "/home/maskal/.elan/toolchains/leanprover--lean4---v4.20.0-rc5/src/lean/Init/System/IOError.lean"
  let fname := "/home/maskal/.elan/toolchains/leanprover--lean4---v4.20.0-rc5/src/lean/Init/Prelude.lean"
  let fname := "Mathlib/Tactic/Linter/CommandStart.lean"
  let fname ← getFileName

  let head ← getHeader fname false--true
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
