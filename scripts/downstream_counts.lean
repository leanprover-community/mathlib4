/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib

/-!
# Count the number of files that import a given file

This file is part of the `latest_import.yml` workflow.  More precisely, `scripts/late_importers.sh`
uses it to determine the number of downstream imports for the report that it prints to Zulip.
-/

open Lean

def downstreamCount (importGraph : NameMap (Array Name)) (fileNames : Array Name) : Array Nat :=
  fileNames.map fun fileName ↦
    let ds := importGraph.downstreamOf {fileName}
    let downDeps : NameSet := ds.fold (init := {}) fun a b _c => a.insert b
    (downDeps.erase fileName).size

abbrev fils : Array Name := #[
  -- insert module names here
]

run_cmd
  let ig := (← getEnv).importGraph
  for f in fils do
    dbg_trace (downstreamCount ig #[f]).getD 0 0
