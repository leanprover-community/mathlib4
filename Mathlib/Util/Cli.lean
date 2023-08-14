/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Cli

/-!
# Helper functions for the Cli library.
-/

open Cli Lean System

/-- A custom command-line argument parser that allows either relative paths to Lean files,
(e.g. `Mathlib/Topology/Basic.lean`) or the module name (e.g. `Mathlib.Topology.Basic`). -/
instance : ParseableType Name where
  name     := "Name"
  parse? s :=
    if s.endsWith ".lean" then
      some <| (s : FilePath).withExtension "" |>.components.foldl Name.mkStr Name.anonymous
    else
      String.toName s
