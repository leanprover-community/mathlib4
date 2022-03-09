/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Xubai Wang
-/
import Lean

namespace Mathlib.Util

open Lean System IO Lean.Elab.Term FS

/--
  Traverse all subdirectories fo `f` to find if one satisfies `p`.
-/
partial def traverseDir (f : FilePath) (p : FilePath → IO Bool) : IO (Option FilePath) := do
  if ← p f then
    return f
  for d in ← FilePath.readDir f do
    let subDir := d.path
    let metadata ← subDir.metadata
    if metadata.type == FileType.dir then
      if let some p ← traverseDir subDir p then
        return p
  return none

elab (name := includeStr) "include_str " str:str : term => do
  let some str := str.isStrLit? | Elab.throwUnsupportedSyntax
  let srcPath := FilePath.mk (← read).fileName
  let currentDir ← IO.currentDir
  -- HACK: Currently we cannot get current file path in VSCode, we have to traversely find the matched subdirectory in the current directory.
  if let some path ← match srcPath.parent with
  | some p => pure $ some $ p / str
  | none => do
    let foundDir ← traverseDir currentDir λ p => p / str |>.pathExists
    pure $ foundDir.map (· / str)
  then
    if ← path.pathExists then
      if ← path.isDir then
        throwError s!"{str} is a directory"
      else
        let content ← FS.readFile path
        pure $ mkStrLit content
    else
      throwError s!"{path} does not exist as a file"
  else
    throwError s!"No such file in whole directory: {str}"
