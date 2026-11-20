/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Init

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Attribute grouping the `field_simp` simprocs
-/

public meta section

open Lean Meta

/-- Initialize the attribute `field` grouping the simprocs associated to the `field_simp` tactic. -/
initialize fieldSimpExt : Simp.SimprocExtension
  ← Simp.registerSimprocAttr `field
      "Attribute grouping the simprocs associated to the field_simp tactic" none
