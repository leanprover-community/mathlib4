/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module algebra.order.euclidean_absolute_value
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.EuclideanDomain.Instances

/-!
# Euclidean absolute values

This file defines a predicate `absolute_value.is_euclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

 * `absolute_value.is_euclidean abv` is a predicate on absolute values on `R` mapping to `S`
    that preserve the order on `R` arising from the Euclidean domain structure.
 * `absolute_value.abs_is_euclidean` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is euclidean.
-/


-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

section OrderedSemiring

variable {R S : Type _} [EuclideanDomain R] [OrderedSemiring S]

variable (abv : AbsoluteValue R S)

/-- An absolute value `abv : R → S` is Euclidean if it is compatible with the
`euclidean_domain` structure on `R`, namely `abv` is strictly monotone with respect to the well
founded relation `≺` on `R`. -/
structure IsEuclidean : Prop where
  map_lt_map_iff' : ∀ {x y}, abv x < abv y ↔ x ≺ y
#align absolute_value.is_euclidean AbsoluteValue.IsEuclidean

namespace IsEuclidean

variable {abv}

-- Rearrange the parameters to `map_lt_map_iff'` so it elaborates better.
theorem map_lt_map_iff {x y : R} (h : abv.IsEuclidean) : abv x < abv y ↔ x ≺ y :=
  map_lt_map_iff' h
#align absolute_value.is_euclidean.map_lt_map_iff AbsoluteValue.IsEuclidean.map_lt_map_iff

attribute [simp] map_lt_map_iff

theorem sub_mod_lt (h : abv.IsEuclidean) (a : R) {b : R} (hb : b ≠ 0) : abv (a % b) < abv b :=
  h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)
#align absolute_value.is_euclidean.sub_mod_lt AbsoluteValue.IsEuclidean.sub_mod_lt

end IsEuclidean

end OrderedSemiring

section Int

open Int

-- TODO: generalize to `linear_ordered_euclidean_domain`s if we ever get a definition of those
/-- `abs : ℤ → ℤ` is a Euclidean absolute value -/
protected theorem abs_is_euclidean : IsEuclidean (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) :=
  {
    map_lt_map_iff' := fun x y =>
      show abs x < abs y ↔ natAbs x < natAbs y by rw [abs_eq_nat_abs, abs_eq_nat_abs, coe_nat_lt] }
#align absolute_value.abs_is_euclidean AbsoluteValue.abs_is_euclidean

end Int

end AbsoluteValue

