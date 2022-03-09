/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Xubai Wang
-/
import Lean

namespace Mathlib.Util

elab (name := includeStr) "include_str " str:str : term => do
  let some str := str.isStrLit? | Lean.Elab.throwUnsupportedSyntax
  let srcPath := System.FilePath.mk (← read).fileName
  let currentDir ← IO.currentDir
  let some srcDir := srcPath.parent | throwError "{srcPath} not in a valid directory"
  let path := srcDir / str
  unless ← path.pathExists do throwError "{path} does not exist as a file"
  if ← path.isDir then throwError "{str} is a directory"
  Lean.mkStrLit <$> IO.FS.readFile path
