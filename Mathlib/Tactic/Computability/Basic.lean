/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Init
public import Lean.LabelAttribute

/-! # Tactics/macros for computability arguments -/

register_label_attr cp

open Lean

macro "apply_cp":tactic =>
  `(tactic|
    apply_rules
      (maxDepth := 30) (symm := false) (exfalso := false) (transparency := .reducible)
      only [*] using $(mkIdent `cp)
  )

macro "apply_cp" n:num:tactic =>
  `(tactic|
    apply_rules
      (maxDepth := $n) (symm := false) (exfalso := false) (transparency := .reducible)
      only [*] using $(mkIdent `cp)
  )
