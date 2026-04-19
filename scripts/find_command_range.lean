/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Parser.Module
import Lean.Util.Path

/-!
# Find command range

A standalone helper script that finds the byte range of the top-level command containing a given
source position. Used by `nightly-testing-checklist` to identify declarations to delete.

Usage: `lean --run find_command_range.lean <file> <line> <col>`

Outputs: `<startByte> <endByte>` on success, or exits with code 1.

This works at the syntax level only (no elaboration), so it handles files with build errors.

Note: without the full environment, the parser can't fully parse terms (e.g. infix operators like
`=` aren't recognized). So we use command START positions as boundaries: the range for a command
is from its start to the start of the next command. This correctly captures the full declaration
including any proof body that the parser failed to parse.

When a declaration has preceding attributes or doc comments that the parser splits into separate
commands, we merge them by walking backwards from the target command.
-/

open Lean Parser in
partial def findRange (args : List String) : IO UInt32 := do
  match args with
  | [filePath, lineStr, colStr] =>
    let targetLine := lineStr.toNat!
    let targetCol := colStr.toNat!
    let contents ← IO.FS.readFile filePath
    initSearchPath (← findSysroot)
    let env ← importModules #[{module := `Init}] {}
    let inputCtx := mkInputContext contents filePath
    let (_, mps, msgs) ← parseHeader inputCtx
    let pmctx : ParserModuleContext := { env, options := {} }
    let fm := inputCtx.fileMap
    let targetPos := fm.ofPosition ⟨targetLine, targetCol⟩
    -- Collect all command start positions
    let mut state := mps
    let mut messages := msgs
    let mut starts : Array String.Pos.Raw := #[]
    repeat
      let (stx, state', msgs') := parseCommand inputCtx pmctx state messages
      if isTerminalCommand stx then break
      if let some range := stx.getRange? then
        starts := starts.push range.start
      state := state'
      messages := msgs'
    -- Find the command containing targetPos
    for i in [:starts.size] do
      let cmdStart := starts[i]!
      let cmdEnd := if i + 1 < starts.size then starts[i + 1]! else state.pos
      if cmdStart ≤ targetPos && targetPos < cmdEnd then
        -- Walk backwards: merge with immediately preceding attributes (@[...]) or
        -- doc comments (/-- ... -/) that the parser may have split off.
        let mut mergedStart := cmdStart
        let mut j := i
        while j > 0 do
          j := j - 1
          let prevStart := starts[j]!
          let prevEnd := if j + 1 < starts.size then starts[j + 1]! else cmdEnd
          -- Only merge if contiguous (no gap)
          if prevEnd != mergedStart then break
          -- Only merge if the previous command looks like an attribute or doc comment
          let prevContent := (contents.toUTF8.extract prevStart.byteIdx prevEnd.byteIdx |> String.fromUTF8!)
          let prevTrimmed := prevContent.trimAsciiStart.toString
          if prevTrimmed.startsWith "@[" || prevTrimmed.startsWith "/--" ||
             prevTrimmed.startsWith "#adaptation_note" then
            mergedStart := prevStart
          else
            break
        IO.println s!"{mergedStart} {cmdEnd}"
        return 0
    IO.eprintln s!"no command found at {targetLine}:{targetCol}"
    return 1
  | _ =>
    IO.eprintln "usage: find_command_range <file> <line> <col>"
    return 1

def main (args : List String) : IO UInt32 := findRange args
