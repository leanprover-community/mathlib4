/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.ElabRules

/-! # `classical` and `classical!` tactics -/

namespace Mathlib.Tactic
open Lean Meta

/--
`classical!` adds a proof of `Classical.propDecidable` as a local variable, which makes it
available for instance search and effectively makes all propositions decidable.
```
noncomputable def foo : Bool := by
  classical!
  have := ∀ p, decide p -- uses the classical instance
  exact decide (0 < 1) -- uses the classical instance even though `0 < 1` is decidable
```
Consider using `classical` instead if you want to use the decidable instance when available.
-/
macro (name := classical!) "classical!" : tactic =>
  `(tactic| have em := Classical.propDecidable)

/--
`classical tacs` runs `tacs` in a scope where `Classical.propDecidable` is a low priority
local instance. It differs from `classical!` in that `classical!` uses a local variable,
which has high priority:
```
noncomputable def foo : Bool := by
  classical!
  have := ∀ p, decide p -- uses the classical instance
  exact decide (0 < 1) -- uses the classical instance even though `0 < 1` is decidable

def bar : Bool := by
  classical
  have := ∀ p, decide p -- uses the classical instance
  exact decide (0 < 1) -- uses the decidable instance
```
Note that (unlike lean 3) `classical` is a scoping tactic - it adds the instance only within the
scope of the tactic.
-/
-- FIXME: using ppDedent looks good in the common case, but produces the incorrect result when
-- the `classical` does not scope over the rest of the block.
elab "classical" tacs:ppDedent(tacticSeq) : tactic => do
  modifyEnv Meta.instanceExtension.pushScope
  Meta.addInstance ``Classical.propDecidable .local 10
  try Elab.Tactic.evalTactic tacs
  finally modifyEnv Meta.instanceExtension.popScope
