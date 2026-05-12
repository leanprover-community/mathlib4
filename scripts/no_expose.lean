/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import NoExpose.Cli
import NoExpose.Collect
import NoExpose.Edit
import NoExpose.Paths
import NoExpose.Report

/-!
# `lake exe no_expose` — entry point

Tiny dispatcher. All work lives in `NoExpose.*` modules.
-/

open NoExpose

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg => do
    IO.eprintln s!"no_expose: {msg}"
    IO.eprintln ""
    IO.eprintln helpText
    return 2
  | .ok .help => do
    IO.println helpText
    return 0
  | .ok .clean => do
    if ← System.FilePath.pathExists dataDir then
      IO.FS.removeDirAll dataDir
      IO.println s!"removed {dataDir}"
    else
      IO.println s!"{dataDir} does not exist; nothing to clean"
    return 0
  | .ok (.collect a) => runCollect a
  | .ok (.report a) => runReport a
  | .ok (.edit a) => runEdit a
