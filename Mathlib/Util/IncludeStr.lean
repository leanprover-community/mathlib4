/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Xubai Wang
-/
import Mathlib.Init
import Lean

/-!
# Defines the `include_str` macro.
-/

namespace Mathlib.Util

/-- A term macro that includes the content of a file, as a string. -/
elab (name := includeStr) "include_str " str:str : term => do
  let some str := str.1.isStrLit? | Lean.Elab.throwUnsupportedSyntax
  let srcPath := System.FilePath.mk (← Lean.MonadLog.getFileName)
  let some srcDir := srcPath.parent | throwError "{srcPath} not in a valid directory"
  let path := srcDir / str
  Lean.mkStrLit <$> IO.FS.readFile path

end Mathlib.Util
