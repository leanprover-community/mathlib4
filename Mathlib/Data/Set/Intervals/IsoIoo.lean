/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Monotone.Odd
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

#align_import data.set.intervals.iso_Ioo from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

/-!
# Order isomorphism between a linear ordered field and `(-1, 1)`

In this file we provide an order isomorphism `orderIsoIooNegOneOne` between the open interval
`(-1, 1)` in a linear ordered field and the whole field.
-/

/- Porting note: `Mathlib.Algebra.Order.Field.Basic` added to imports for `abs` -/


open Set

/- Porting note: Had to manually coerce `x : Ioo (-1 : k) 1` to `x : k`. -/
/-- In a linear ordered field, the whole field is order isomorphic to the open interval `(-1, 1)`.
We consider the actual implementation to be a "black box", so it is irreducible.
-/
@[irreducible]
def orderIsoIooNegOneOne (k : Type*) [LinearOrderedField k] : k ≃o Ioo (-1 : k) 1 := by
  refine' StrictMono.orderIsoOfRightInverse _ _ (fun x ↦ x / (1 - |↑x|)) _
  · refine' codRestrict (fun x ↦ x / (1 + |x|)) _ fun x ↦ abs_lt.1 _
    -- ⊢ |(fun x => x / (1 + |x|)) x| < 1
    have H : 0 < 1 + |x| := (abs_nonneg x).trans_lt (lt_one_add _)
    -- ⊢ |(fun x => x / (1 + |x|)) x| < 1
    calc
      |x / (1 + |x|)| = |x| / (1 + |x|) := by rw [abs_div, abs_of_pos H]
      _ < 1 := (div_lt_one H).2 (lt_one_add _)
  · refine' (strictMono_of_odd_strictMonoOn_nonneg _ _).codRestrict _
    -- ⊢ ∀ (x : k), -x / (1 + |(-x)|) = -(x / (1 + |x|))
    · intro x
      -- ⊢ -x / (1 + |(-x)|) = -(x / (1 + |x|))
      simp only [abs_neg, neg_div]
      -- 🎉 no goals
    · rintro x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy
      -- ⊢ (fun x => x / (1 + |x|)) x < (fun x => x / (1 + |x|)) y
      simp [abs_of_nonneg, mul_add, mul_comm x y, div_lt_div_iff, hx.trans_lt (lt_one_add _),
        hy.trans_lt (lt_one_add _), *]
  · refine' fun x ↦ Subtype.ext _
    -- ⊢ ↑(codRestrict (fun x => x / (1 + |x|)) (Ioo (-1) 1) (_ : ∀ (x : k), -1 < (fu …
    have : 0 < 1 - |(x : k)| := sub_pos.2 (abs_lt.2 x.2)
    -- ⊢ ↑(codRestrict (fun x => x / (1 + |x|)) (Ioo (-1) 1) (_ : ∀ (x : k), -1 < (fu …
    field_simp [abs_div, this.ne', abs_of_pos this]
    -- 🎉 no goals
#align order_iso_Ioo_neg_one_one orderIsoIooNegOneOne
