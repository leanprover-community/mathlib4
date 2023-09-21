/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathlib
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Find

/-!
# Saving the `#find` cache.

After importing of mathlib, we build a `#find` cache and pickle it to disk.
This file will be distributed via our Azure storage.
-/

open Lean.Elab.Command
open Mathlib.Tactic.Find

run_cmd liftTermElabM do
  let path ← cachePath
  _ ← path.parent.mapM fun p => IO.FS.createDirAll p
  pickle path (← (← Index.mk).getImported) `Find
