/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public meta import Lean.LabelAttribute
public import Mathlib.Init

/-! # Tactics/macros for computability arguments -/

public meta section

/-- The `cp` attribute labels the lemmas used by `apply_cp`, mainly those showing that codes satisfy
`IsPrim`. -/
register_label_attr cp

open Lean

/-- `apply_cp` proves goals such as `IsPrim c` by repeatedly applying the hypotheses and the lemmas
tagged `@[cp]`, up to depth 30. `apply_cp n` uses maximum depth `n` instead. -/
macro (name := applyCp) "apply_cp" : tactic =>
  `(tactic|
    apply_rules
      (maxDepth := 30) (symm := false) (exfalso := false) (transparency := .reducible)
      only [*] using $(mkIdent `cp)
  )

/-- `apply_cp n` is `apply_cp` with maximum search depth `n`. -/
@[tactic_alt applyCp]
macro (name := applyCpDepth) "apply_cp" n:num : tactic =>
  `(tactic|
    apply_rules
      (maxDepth := $n) (symm := false) (exfalso := false) (transparency := .reducible)
      only [*] using $(mkIdent `cp)
  )
