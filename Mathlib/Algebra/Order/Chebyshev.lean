/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Monotone.Monovary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Module.Synonym
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.Monovary
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Finset.Attr
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Chebyshev's sum inequality

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ #s * ∑ i ∈ s, f i * g i`
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

public section


open Equiv Equiv.Perm Finset Function OrderDual

variable {ι α β : Type*}

/-! ### Scalar multiplication versions -/


section SMul
variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem MonovaryOn.sum_smul_sum_le_card_smul_sum (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) • ∑ i ∈ s, g i ≤ #s • ∑ i ∈ s, f i • g i := by
  classical
  obtain ⟨σ, hσ, hs⟩ := s.countable_toSet.exists_cycleOn
  rw [← card_range #s, sum_smul_sum_eq_sum_perm hσ]
  exact sum_le_card_nsmul _ _ _ fun n _ ↦
    hfg.sum_smul_comp_perm_le_sum_smul fun x hx ↦ hs fun h ↦ hx <| IsFixedPt.perm_pow h _

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) :
    #s • ∑ i ∈ s, f i • g i ≤ (∑ i ∈ s, f i) • ∑ i ∈ s, g i :=
  hfg.dual_right.sum_smul_sum_le_card_smul_sum

variable [Fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) :
    (∑ i, f i) • ∑ i, g i ≤ Fintype.card ι • ∑ i, f i • g i :=
  (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
theorem Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) :
    Fintype.card ι • ∑ i, f i • g i ≤ (∑ i, f i) • ∑ i, g i :=
  (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum

end SMul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul
variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * ∑ i ∈ s, g i ≤ #s * ∑ i ∈ s, f i * g i := by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the product of their sum is greater than the size of the set times their scalar
product. -/
theorem AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) :
    (#s : α) * ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum

/-- Special case of **Jensen's inequality** for sums of powers. -/
lemma pow_sum_le_card_mul_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∀ n, (∑ i ∈ s, f i) ^ (n + 1) ≤ (#s : α) ^ n * ∑ i ∈ s, f i ^ (n + 1)
  | 0 => by simp
  | n + 1 =>
    calc
      _ = (∑ i ∈ s, f i) ^ (n + 1) * ∑ i ∈ s, f i := by rw [pow_succ]
      _ ≤ (#s ^ n * ∑ i ∈ s, f i ^ (n + 1)) * ∑ i ∈ s, f i := by
        gcongr
        exacts [sum_nonneg hf, pow_sum_le_card_mul_sum_pow hf _]
      _ = #s ^ n * ((∑ i ∈ s, f i ^ (n + 1)) * ∑ i ∈ s, f i) := by rw [mul_assoc]
      _ ≤ #s ^ n * (#s * ∑ i ∈ s, f i ^ (n + 1) * f i) := by
        gcongr _ * ?_
        exact ((monovaryOn_self ..).pow_left₀ hf _).sum_mul_sum_le_card_mul_sum
      _ = _ := by simp_rw [← mul_assoc, ← pow_succ]

/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz Inequality**: The square
of the sum is less than the size of the set times the sum of the squares. -/
theorem sq_sum_le_card_mul_sum_sq : (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum

variable [Fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) :
    (∑ i, f i) * ∑ i, g i ≤ Fintype.card ι * ∑ i, f i * g i :=
  (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the product of their sum is less than the size of the set times their scalar
product. -/
theorem Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) :
    Fintype.card ι * ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i :=
  (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum

end Mul

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {f : ι → α}

/-- Special case of **Jensen's inequality** for sums of powers. -/
lemma pow_sum_div_card_le_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (n + 1) / #s ^ n ≤ ∑ i ∈ s, f i ^ (n + 1) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_le_iff₀' (by positivity)]
  exact pow_sum_le_card_mul_sum_pow hf _

theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i ∈ s, f i) / #s) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) / #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), sq (#s : α), mul_left_comm,
    ← mul_assoc]
  gcongr
  exact sq_sum_le_card_mul_sum_sq
