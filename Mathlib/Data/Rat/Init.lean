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
import Std.Classes.RatCast

#align_import data.rat.init from "leanprover-community/mathlib"@"f340f229b1f461aa1c8ee11e0a172d0a3b301a4a"

/-!
# Basic definitions around the rational numbers

This file declares `ℚ` notation for the rationals and defines the nonnegative rationals `ℚ≥0`.

This file is eligible to upstreaming to Std.
-/

@[inherit_doc] notation "ℚ" => Rat

#align rat.denom Rat.den

/-- Nonnegative rational numbers. -/
def NNRat := {q : ℚ // 0 ≤ q}
#align nnrat NNRat

@[inherit_doc] notation "ℚ≥0" => NNRat

/-! ### Numerator and denominator of a nonnegative rational -/

namespace NNRat

instance instCoe : Coe ℚ≥0 ℚ := ⟨Subtype.val⟩

/-- The numerator of a nonnegative rational. -/
@[pp_dot] def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs
#align nnrat.num NNRat.num

/-- The denominator of a nonnegative rational. -/
@[pp_dot] def den (q : ℚ≥0) : ℕ := (q : ℚ).den
#align nnrat.denom NNRat.den

@[simp] lemma num_mk (q : ℚ) (hq : 0 ≤ q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
@[simp] lemma den_mk (q : ℚ) (hq : 0 ≤ q) : den ⟨q, hq⟩ = q.den := rfl

end NNRat

namespace Rat

@[norm_cast] lemma cast_id (n : ℚ) : Rat.cast n = n := rfl
@[simp] lemma cast_eq_id : Rat.cast = id := rfl
#align rat.cast_id Rat.cast_id
#align rat.cast_eq_id Rat.cast_eq_id

end Rat
