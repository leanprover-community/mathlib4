/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command

import Batteries.Util.LibraryNote
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header  -- shake: keep

/-! -/

meta section

open Lean Elab Command

namespace Mathlib.Linter

-- Copied from `Batteries.Util.LibraryNote`
def encodeNameForExport (n : Name) : Name :=
  n.componentsRev.foldl (init := .anonymous) fun acc c =>
    match c with
    | .str _ s => .str acc (s.replace " " "_")
    | .num _ k => .num acc k
    | .anonymous => acc

def libraryNoteInteractive : Linter where
  run cmd := do
    unless ← Elab.inServer.getM do return
    let some { start, stop } := cmd.getRangeWithTrailing? | return
    let src := (← getFileMap).source
    let some start := src.pos? start | return
    let some stop := src.pos? stop | return
    let cmdSrc := src.slice! start stop
    -- TODO: better way to find matches; better syntax?; capitalization + linebreaks
    let notes := cmdSrc.split "library note "
    for note in notes do
      -- TODO: better way to ignore first element? or better way to find matches, more generally
      if note.startInclusive.offset == cmdSrc.startInclusive.offset then continue
      let some rest := note.dropPrefix? "[" | continue
      -- For now, don't worry about escaping `]` with `\]`
      let noteName := rest.takeWhile (· !=  ']')
      let ref := .ofRange {
          start := noteName.startInclusive.offset
          stop := noteName.endExclusive.offset }
      -- option to allow non-imported cross-refs that rely on ileans and skip this check?
      let noteName := if noteName.toName.isAnonymous then
        Name.mkSimple noteName.copy else noteName.toName
      let noteDecl := `LibraryNote ++ encodeNameForExport noteName
      unless (← getEnv).find? noteDecl |>.isSome do
        logWarningAt ref m!"Could not find `{noteDecl}` in the environment."
        continue
      liftTermElabM <|
        Term.addTermInfo' ref (mkConst noteDecl) (mkConst ``Batteries.Util.LibraryNote)

initialize addLinter libraryNoteInteractive
