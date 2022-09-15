/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Util.TermUnsafe
import Mathlib.Tactic.Repeat

/-!
# The `apply_rules` tactic

The `apply_rules` tactic calls `apply` (with a specified set of lemmas) and `assumption`
repeatedly, until no more applications are possible.
-/


namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term Parser.Tactic

/--
`applyFirst cfg l`, for `L : List Expr`,
tries to apply one of the lemmas in `L` to the goal (using `cfg : ApplyConfig`), and
fails if none succeeds.
-/
def applyFirst (cfg : ApplyConfig) (L : List Expr) : MVarId → MetaM (List MVarId) :=
fun g => L.firstM (g.apply · cfg)

/--
Implementation of the `apply_rules` tactic.
-/
def applyRules (cfg : ApplyConfig) (L : List Expr) : MVarId → MetaM (List MVarId) :=
repeat' (fun g => (do g.assumption; pure []) <|> applyFirst cfg L g)

/--
`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by calling `assumption`.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.

You may include attributes amongst the lemmas:
`apply_rules` will include all lemmas marked with these attributes.

You can pass a further configuration `cfg : ApplyConfig` via the syntax `apply_rules cfg lemmas`.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.

TODO: add support for attributes
TODO: copy the other tests/examples from Lean 3
-/
elab (name := applyRulesElab)
  "apply_rules" cfg:(config)? " [" lemmas:term,* "]" : tactic =>
do
  let cfg ← cfg.mapM (unsafe evalTerm ApplyConfig (mkConst ``ApplyConfig) ·)
  let lemmas ← lemmas.getElems.toList.mapM (elabTermForApply ·.raw)
  liftMetaTactic $ applyRules (cfg.getD {}) lemmas
