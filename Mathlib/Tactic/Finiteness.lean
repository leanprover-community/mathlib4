/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.MeasureTheory.Constructions.Prod.Basic

/-! # Finiteness tactic

This file implements a basic `finiteness` tactic, designed to solve goals of the form `*** < ∞` and
(equivalently) `*** ≠ ∞` in the extended nonnegative reals (`ENNReal`, aka `ℝ≥0∞`).

It works recursively according to the syntax of the expression. It is implemented as an `aesop` rule
set.

[TODO]: improve `finiteness` to also deal with other situations, such as balls in proper spaces with
a locally finite measure.
-/

open ENNReal

/-! ## Lemmas -/

private theorem ENNReal.ofNat_ne_top (n : ℕ) [Nat.AtLeastTwo n] : no_index (OfNat.ofNat n) ≠ ∞ :=
  ENNReal.natCast_ne_top n

private theorem ENNReal.inv_ne_top' {a} (h : a ≠ 0) : a⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 h

private theorem ENNReal.add_ne_top' {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a + b ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ha, hb⟩

/-! ## Tactic implementation -/

attribute [aesop (rule_sets := [Finiteness]) unsafe 20%] ne_top_of_lt
-- would have been better to implement this as a "safe" "forward" rule, why doesn't this work?
-- attribute [aesop (rule_sets [Finiteness]) safe forward] ne_top_of_lt

attribute [aesop (rule_sets := [Finiteness]) safe apply]
  Ne.lt_top
  ENNReal.ofReal_ne_top ENNReal.coe_ne_top ENNReal.natCast_ne_top
  ENNReal.zero_ne_top ENNReal.one_ne_top ENNReal.ofNat_ne_top
  ENNReal.mul_ne_top ENNReal.add_ne_top' ENNReal.sub_ne_top ENNReal.inv_ne_top'
  MeasureTheory.measure_ne_top

open Aesop.BuiltinRules in
attribute [aesop (rule_sets := [Finiteness]) safe -50] assumption intros

open Lean Elab Tactic in
/-- A version of the positivity tactic for use by `aesop`. -/
@[aesop safe tactic (rule_sets := [Finiteness])]
def PositivityForAesop : TacticM Unit :=
  liftMetaTactic fun g => do Mathlib.Meta.Positivity.positivity g; pure []

/-- Tactic to solve goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). -/
macro (name := finiteness) "finiteness" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { introsTransparency? := some .reducible, terminal := true, enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `Finiteness):ident, -default, -builtin]))
