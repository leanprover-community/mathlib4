/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Positivity.Core

/-!
# Finiteness tactic

This file implements a basic `finiteness` tactic, designed to solve goals of the form `*** < ∞` and
(equivalently) `*** ≠ ∞` in the extended nonnegative reals (`ENNReal`, aka `ℝ≥0∞`).

It works recursively according to the syntax of the expression. It is implemented as an `aesop` rule
set.

## Syntax

Standard `aesop` syntax applies. Namely one can write
* `finiteness (add unfold [def1, def2])` to make `finiteness` unfold `def1`, `def2`
* `finiteness?` for the tactic to show what proof it found
* etc
* Note that `finiteness` disables `simp`, so `finiteness (add simp [lemma1, lemma2])` does not do
  anything more than a bare `finiteness`.

We also provide `finiteness_nonterminal` as a version of `finiteness` that doesn't have to close the
goal.

Note to users: when tagging a lemma for finiteness, prefer tagging a lemma with `≠ ⊤`.
Aesop can deduce `< ∞` from `≠ ∞` safely (`Ne.lt_top` is a safe rule), but not conversely
(`ne_top_of_lt` is an unsafe rule): in simpler words, aesop tries to use `≠` as its intermediate
representation that things are finite, so we do so as well.

## TODO

Improve `finiteness` to also deal with other situations, such as balls in proper spaces with
a locally finite measure.
-/

open Aesop.BuiltinRules in
attribute [aesop (rule_sets := [finiteness]) safe -50] assumption intros

set_option linter.unusedTactic false in
add_aesop_rules safe tactic (rule_sets := [finiteness]) (by positivity)

/-- Tactic to solve goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). -/
macro (name := finiteness) "finiteness" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { introsTransparency? := some .reducible, terminal := true, enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `finiteness):ident, -default, -builtin]))

/-- Tactic to solve goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). -/
macro (name := finiteness?) "finiteness?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { introsTransparency? := some .reducible, terminal := true, enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `finiteness):ident, -default, -builtin]))

/-- Tactic to solve goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). -/
macro (name := finiteness_nonterminal) "finiteness_nonterminal" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { introsTransparency? := some .reducible, terminal := false, enableSimp := false,
                 warnOnNonterminal := false  })
    (rule_sets := [$(Lean.mkIdent `finiteness):ident, -default, -builtin]))

/-!
 We register `finiteness` with the `hint` tactic.
 -/
register_hint finiteness
