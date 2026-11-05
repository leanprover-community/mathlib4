/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Init

import Mathlib.Data.Rat.Cast.Lemmas

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
Deprecated aliases can be dumped here if they are no longer used in Mathlib,
to avoid needing their imports if they are otherwise unnecessary.
-/

@[expose] public section

namespace Dyadic

/-- Interpret a dyadic rational as a real number. -/
@[deprecated "Use the coercion `(d : ℝ)` instead." (since := "2026-11-05")]
def toReal (d : Dyadic) : ℝ := d.toRat

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_natCast (n : ℕ) : toReal (n : Dyadic) = (n : ℝ) := by simp [toReal]

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    toReal (ofNat(n) : Dyadic) = (ofNat(n) : ℝ) := by simp [toReal]

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_intCast (z : ℤ) : toReal (z : Dyadic) = (z : ℝ) := by simp [toReal]

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_add (a b : Dyadic) : toReal (a + b) = toReal a + toReal b := by simp [toReal]

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_mul (a b : Dyadic) : toReal (a * b) = toReal a * toReal b := by simp [toReal]

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_pow (a : Dyadic) (n : ℕ) : toReal (a ^ n) = toReal a ^ n := by simp [toReal]

/-- `Dyadic.toReal` as an additive monoid homomorphism. -/
@[deprecated Inclusion.IntervalDyadicReal.castAddMonoidHom (since := "2026-11-05")]
def toRealAddMonoidHom : Dyadic →+ ℝ where
  toFun := toReal
  map_zero' := by simp [toReal]
  map_add' := toReal_add

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_le_toReal {a b : Dyadic} : toReal a ≤ toReal b ↔ a ≤ b := by simp [toReal]

@[simp, deprecated "Use the coercion to ℝ and `simp` instead." (since := "2026-11-05")]
lemma toReal_lt_toReal {a b : Dyadic} : toReal a < toReal b ↔ a < b := by simp [toReal]

/-- `Dyadic.toReal` as an order embedding. -/
@[deprecated Inclusion.IntervalDyadicReal.castOrderEmbedding (since := "2026-11-05")]
def toRealOrderEmbedding : Dyadic ↪o ℝ :=
  OrderEmbedding.ofStrictMono toReal fun _ _ h ↦ toReal_lt_toReal.mpr h

end Dyadic
