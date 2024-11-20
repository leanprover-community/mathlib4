/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Set

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open scoped Pointwise

namespace Finset
variable {α β : Type*}

/-- `Finset α` has distributive negation if `α` has. -/
protected def distribNeg [DecidableEq α] [Mul α] [HasDistribNeg α] : HasDistribNeg (Finset α) :=
  coe_injective.hasDistribNeg _ coe_neg coe_mul

scoped[Pointwise] attribute [instance] Finset.distribNeg

section Distrib
variable [DecidableEq α] [Distrib α] (s t u : Finset α)

/-!
Note that `Finset α` is not a `Distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : Finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : Finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/

lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image₂_distrib_subset_left mul_add

lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image₂_distrib_subset_right add_mul

end Distrib

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] [DecidableEq β] {s : Finset α} {t : Finset β}
  {a : α}

@[simp]
lemma neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg, image_image, neg_smul, Function.comp_def]

@[simp]
protected lemma neg_smul [DecidableEq α] : -s • t = -(s • t) := by
  simp_rw [← image_neg]
  exact image₂_image_left_comm neg_smul

end Ring
end Finset
