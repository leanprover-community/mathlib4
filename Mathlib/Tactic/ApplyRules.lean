/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Std.Util.TermUnsafe
import Std.Lean.Meta

/-!
# The `apply_rules` tactic

The `apply_rules` tactic calls `apply` (with a specified set of lemmas) and `assumption`
repeatedly, until no more applications are possible.
-/

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term Parser.Tactic

/--
Implementation of the `apply_rules` tactic.
-/
def applyRules (cfg : ApplyConfig) (maxIters : Nat) (L : List Expr) :
  MVarId → MetaM (List MVarId) :=
fun h => repeat' (maxIters := maxIters)
  (fun g => (do g.assumption; pure []) <|> L.firstM (g.apply · cfg)) [h]

-- This should be moved higher in the import hierarchy when others need it.
/-- An elaborator for translating a `Syntax` to an `ApplyConfig`. -/
declare_config_elab elabApplyConfig ApplyConfig

/--
`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by calling `assumption`.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.

You may include attributes amongst the lemmas:
`apply_rules` will include all lemmas marked with these attributes.

You can bound the iteration depth using the syntax `apply_rules lemmas n`.
The default bound is 50.

You can pass a further configuration `cfg : ApplyConfig` via the syntax `apply_rules cfg lemmas`.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.

TODO: add support for attributes
TODO: copy the other tests/examples from Lean 3
-/
elab (name := applyRulesElab)
    "apply_rules" cfg:(config ?) " [" lemmas:term,* "]" n:(ppSpace num)? : tactic => do
  let cfg ← elabApplyConfig cfg
  let lemmas ← lemmas.getElems.toList.mapM (elabTermForApply ·.raw)
  liftMetaTactic $ applyRules cfg (n.map (·.getNat) |>.getD 50) lemmas
