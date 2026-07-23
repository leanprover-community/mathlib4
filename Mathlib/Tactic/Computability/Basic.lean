/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Lean
register_label_attr cp

/-! # Tactics/macros for computability arguments -/

open Lean

macro "apply_cp":tactic =>
  `(tactic|
    apply_rules
      (config := { maxDepth := 30
                 , symm := false
                 , exfalso := false
                 , transparency := .reducible })
      only [*] using $(mkIdent `cp)
  )

macro "apply_cp" n:num:tactic =>
  `(tactic|
    apply_rules
      (config := { maxDepth := $n
                 , symm := false
                 , exfalso := false
                 , transparency := .reducible })
      only [*] using $(mkIdent `cp)
  )
