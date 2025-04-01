/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

assert_not_exists MulAction OrderedAddCommMonoid Field

open Function
open scoped Pointwise

variable {α : Type*}

namespace Set

/-- `Set α` has distributive negation if `α` has. -/
protected noncomputable def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) where
  __ := Set.involutiveNeg
  neg_mul _ _ := by simp_rw [← image_neg_eq_neg]; exact image2_image_left_comm neg_mul
  mul_neg _ _ := by simp_rw [← image_neg_eq_neg]; exact image_image2_right_comm mul_neg

scoped[Pointwise] attribute [instance] Set.hasDistribNeg

section Distrib
variable [Distrib α] (s t u : Set α)

/-!
Note that `Set α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/

lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul

end Distrib
end Set
