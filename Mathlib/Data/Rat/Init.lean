/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.ProjectionNotation
import Mathlib.Tactic.TypeStar
import Batteries.Classes.RatCast

#align_import data.rat.init from "leanprover-community/mathlib"@"f340f229b1f461aa1c8ee11e0a172d0a3b301a4a"

/-!
# Basic definitions around the rational numbers

This file declares `ℚ` notation for the rationals and defines the nonnegative rationals `ℚ≥0`.

This file is eligible to upstreaming to Batteries.
-/

@[inherit_doc] notation "ℚ" => Rat

#align rat.denom Rat.den

/-- Nonnegative rational numbers. -/
def NNRat := {q : ℚ // 0 ≤ q}
#align nnrat NNRat

@[inherit_doc] notation "ℚ≥0" => NNRat

/-!
### Cast from `NNRat`

This section sets up the typeclasses necessary to declare the canonical embedding `ℚ≥0` to any
semifield.
-/

/-- Typeclass for the canonical homomorphism `ℚ≥0 → K`.

This should be considered as a notation typeclass. The sole purpose of this typeclass is to be
extended by `DivisionSemiring`. -/
class NNRatCast (K : Type*) where
  /-- The canonical homomorphism `ℚ≥0 → K`.

  Do not use directly. Use the coercion instead. -/
  protected nnratCast : ℚ≥0 → K

instance NNRat.instNNRatCast : NNRatCast ℚ≥0 where nnratCast q := q

variable {K : Type*} [NNRatCast K]

/-- Canonical homomorphism from `ℚ≥0` to a division semiring `K`.

This is just the bare function in order to aid in creating instances of `DivisionSemiring`. -/
@[coe, reducible, match_pattern] protected def NNRat.cast : ℚ≥0 → K := NNRatCast.nnratCast

-- See note [coercion into rings]
instance NNRatCast.toCoeTail [NNRatCast K] : CoeTail ℚ≥0 K where coe := NNRat.cast

-- See note [coercion into rings]
instance NNRatCast.toCoeHTCT [NNRatCast K] : CoeHTCT ℚ≥0 K where coe := NNRat.cast

instance Rat.instNNRatCast : NNRatCast ℚ := ⟨Subtype.val⟩

/-! ### Numerator and denominator of a nonnegative rational -/

namespace NNRat

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs
#align nnrat.num NNRat.num

/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ := (q : ℚ).den
#align nnrat.denom NNRat.den

@[simp] lemma num_mk (q : ℚ) (hq : 0 ≤ q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
@[simp] lemma den_mk (q : ℚ) (hq : 0 ≤ q) : den ⟨q, hq⟩ = q.den := rfl

@[norm_cast] lemma cast_id (n : ℚ≥0) : NNRat.cast n = n := rfl
@[simp] lemma cast_eq_id : NNRat.cast = id := rfl

end NNRat

namespace Rat

@[norm_cast] lemma cast_id (n : ℚ) : Rat.cast n = n := rfl
@[simp] lemma cast_eq_id : Rat.cast = id := rfl
#align rat.cast_id Rat.cast_id
#align rat.cast_eq_id Rat.cast_eq_id

end Rat
