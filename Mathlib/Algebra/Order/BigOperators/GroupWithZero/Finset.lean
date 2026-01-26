import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs

/-!
# Big operators on a finset in groups with zero involving order

This file contains the results concerning the interaction of finset big operators with groups with
zero, where order is involved.
-/

@[expose] public section

/-- A version of `Finset.one_le_prod''` for `PosMulMono` in place of `MulLeftMono`. -/
lemma Finset.one_le_prod {α M : Type*} (s : Finset α) [CommMonoidWithZero M]
    [Preorder M] [ZeroLEOneClass M] [PosMulMono M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s h ih => simpa [h] using one_le_mul_of_one_le_of_one_le (hf a) ih
