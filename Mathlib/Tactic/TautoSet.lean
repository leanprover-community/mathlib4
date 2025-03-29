/-
Copyright (c) 2025 Lenny Taelman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lenny Taelman
-/

import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Set.Disjoint

/-!
# The `tauto_set` tactic
-/

assert_not_exists RelIso

namespace Mathlib.Tactic.TautoSet

open Lean Elab.Tactic

/--
`specialize_all x` runs `specialize h x` for all hypotheses `h` where this tactic succeeds.
-/
elab (name := specialize_all) "specialize_all" x:term : tactic => withMainContext do
  for h in ← getLCtx do
    evalTactic (← `(tactic|specialize $(mkIdent h.userName) $x)) <|> pure ()


/--
`tauto_set` attempts to prove tautologies involving hypotheses and goals of the form `X ⊆ Y`
or `X = Y`, where `X`, `Y` are expressions built using ∪, ∩, \, and ᶜ from finitely many
variables of type `Set α`. It also unfolds expressions of the form `Disjoint A B` and
`symmDiff A B`.

Examples:
```lean
example {α} (A B C D : Set α) (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by
  tauto_set

example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by
  tauto_set
```
-/
macro "tauto_set" : tactic => `(tactic|
  · simp_all -failIfUnchanged only [
      Set.ext_iff, Set.subset_def,
      Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
      Set.symmDiff_def, Set.diff_eq, Set.disjoint_iff
    ]
    try intro x
    try specialize_all x
    <;> tauto
)


end Mathlib.Tactic.TautoSet
