/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.GroupTheory.Perm.Cycle.Basic

#align_import algebra.order.chebyshev from "leanprover-community/mathlib"@"b7399344324326918d65d0c74e9571e3a8cb9199"

/-!
# Chebyshev's sum inequality

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ s.card * ∑ i ∈ s, f i * g i`
when `f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.


## Main declarations

* `MonovaryOn.sum_mul_sum_le_card_mul_sum`: Chebyshev's inequality.
* `AntivaryOn.card_mul_sum_le_sum_mul_sum`: Chebyshev's inequality, dual version.
* `sq_sum_le_card_mul_sum_sq`: Special case of Chebyshev's inequality when `f = g`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `Monotone`/`Antitone` pairs of functions over a `LinearOrder` is not deduced in this
file because it is easily deducible from the `Monovary` API.
-/


open Equiv Equiv.Perm Finset Function OrderDual

variable {ι α β : Type*}

/-! ### Scalar multiplication versions -/


section SMul

variable [LinearOrderedRing α] [LinearOrderedAddCommGroup β] [Module α β] [OrderedSMul α β]
  {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem MonovaryOn.sum_smul_sum_le_card_smul_sum (hfg : MonovaryOn f g s) :
    ((∑ i ∈ s, f i) • ∑ i ∈ s, g i) ≤ s.card • ∑ i ∈ s, f i • g i := by
  classical
    obtain ⟨σ, hσ, hs⟩ := s.countable_toSet.exists_cycleOn
    rw [← card_range s.card, sum_smul_sum_eq_sum_perm hσ]
    exact
      sum_le_card_nsmul _ _ _ fun n _ =>
        hfg.sum_smul_comp_perm_le_sum_smul fun x hx => hs fun h => hx <| IsFixedPt.perm_pow h _
#align monovary_on.sum_smul_sum_le_card_smul_sum MonovaryOn.sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) :
    (s.card • ∑ i ∈ s, f i • g i) ≤ (∑ i ∈ s, f i) • ∑ i ∈ s, g i := by
  exact hfg.dual_right.sum_smul_sum_le_card_smul_sum
#align antivary_on.card_smul_sum_le_sum_smul_sum AntivaryOn.card_smul_sum_le_sum_smul_sum

variable [Fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) :
    ((∑ i, f i) • ∑ i, g i) ≤ Fintype.card ι • ∑ i, f i • g i :=
  (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum
#align monovary.sum_smul_sum_le_card_smul_sum Monovary.sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) :
    (Fintype.card ι • ∑ i, f i • g i) ≤ (∑ i, f i) • ∑ i, g i := by
  exact (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum
#align antivary.card_smul_sum_le_sum_smul_sum Antivary.card_smul_sum_le_sum_smul_sum

end SMul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul

variable [LinearOrderedRing α] {s : Finset ι} {σ : Perm ι} {f g : ι → α}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, g i) ≤ s.card * ∑ i ∈ s, f i * g i := by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum
#align monovary_on.sum_mul_sum_le_card_mul_sum MonovaryOn.sum_mul_sum_le_card_mul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the product of their sum is greater than the size of the set times their scalar
product. -/
theorem AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) :
    ((s.card : α) * ∑ i ∈ s, f i * g i) ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum
#align antivary_on.card_mul_sum_le_sum_mul_sum AntivaryOn.card_mul_sum_le_sum_mul_sum

/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz Inequality**: The square
of the sum is less than the size of the set times the sum of the squares. -/
theorem sq_sum_le_card_mul_sum_sq : (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum
#align sq_sum_le_card_mul_sum_sq sq_sum_le_card_mul_sum_sq

variable [Fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) :
    ((∑ i, f i) * ∑ i, g i) ≤ Fintype.card ι * ∑ i, f i * g i :=
  (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum
#align monovary.sum_mul_sum_le_card_mul_sum Monovary.sum_mul_sum_le_card_mul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) :
    ((Fintype.card ι : α) * ∑ i, f i * g i) ≤ (∑ i, f i) * ∑ i, g i :=
  (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum
#align antivary.card_mul_sum_le_sum_mul_sum Antivary.card_mul_sum_le_sum_mul_sum

end Mul

variable [LinearOrderedField α] {s : Finset ι} {f : ι → α}

theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i ∈ s, f i) / s.card) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) / s.card := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← card_pos, ← @Nat.cast_pos α] at hs
  rw [div_pow, div_le_div_iff (sq_pos_of_ne_zero hs.ne') hs, sq (s.card : α), mul_left_comm, ←
    mul_assoc]
  exact mul_le_mul_of_nonneg_right sq_sum_le_card_mul_sum_sq hs.le
#align sum_div_card_sq_le_sum_sq_div_card sum_div_card_sq_le_sum_sq_div_card
