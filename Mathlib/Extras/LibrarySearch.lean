/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.All

/-!
# Saving the `library_search` cache.

After importing of mathlib, we build a `library_search` cache and pickle it to disk.
This file will be distributed alongside the `.olean` for this file via our Azure storage.
-/

open Lean Elab Command
open System (FilePath)
open Mathlib.Tactic.LibrarySearch

elab "#library_search_cache" : command => liftTermElabM do
  _ ← cachePath.parent.mapM fun p => IO.FS.createDirAll p
  pickle cachePath (← librarySearchLemmas.get)

#library_search_cache
