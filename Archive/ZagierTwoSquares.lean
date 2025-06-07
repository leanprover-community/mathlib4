/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Thomas Browning
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Linarith

/-!
# Zagier's "one-sentence proof" of Fermat's theorem on sums of two squares

"The involution on the finite set `S = {(x, y, z) : ℕ × ℕ × ℕ | x ^ 2 + 4 * y * z = p}` defined by
```
(x, y, z) ↦ (x + 2 * z, z, y - x - z) if x < y - z
            (2 * y - x, y, x - y + z) if y - z < x < 2 * y
            (x - 2 * y, x - y + z, y) if x > 2 * y
```
has exactly one fixed point, so `|S|` is odd and the involution defined by
`(x, y, z) ↦ (x, z, y)` also has a fixed point." — [Don Zagier](Zagier1990)

This elementary proof (`Nat.Prime.sq_add_sq'`) is independent of `Nat.Prime.sq_add_sq` in
`Mathlib/NumberTheory/SumTwoSquares.lean`, which uses the unique factorisation of `ℤ[i]`.
For a geometric interpretation of the piecewise involution (`Zagier.complexInvo`)
see [Moritz Firsching's MathOverflow answer](https://mathoverflow.net/a/299696).
-/


namespace Zagier

section Sets

open Set

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- The set of all triples of natural numbers `(x, y, z)` satisfying
`x * x + 4 * y * z = 4 * k + 1`. -/
def zagierSet : Set (ℕ × ℕ × ℕ) := {t | t.1 * t.1 + 4 * t.2.1 * t.2.2 = 4 * k + 1}

lemma zagierSet_lower_bound {x y z : ℕ} (h : (x, y, z) ∈ zagierSet k) : 0 < x ∧ 0 < y ∧ 0 < z := by
  rw [zagierSet, mem_setOf_eq] at h
  refine ⟨?_, ?_, ?_⟩
  all_goals
    by_contra q
    rw [not_lt, nonpos_iff_eq_zero] at q
    simp only [q, mul_zero, zero_mul, zero_add, add_zero] at h
  · apply_fun (· % 4) at h
    simp [mul_assoc, Nat.add_mod] at h
  all_goals
    rcases (Nat.dvd_prime hk.out).1 (dvd_of_mul_left_eq _ h) with e | e
    all_goals
      simp only [e, right_eq_add, ne_eq, add_eq_zero, and_false, not_false_eq_true,
        mul_eq_left₀, reduceCtorEq] at h
      simp only [h, zero_add] at hk
      exact Nat.not_prime_one hk.out

lemma zagierSet_upper_bound {x y z : ℕ} (h : (x, y, z) ∈ zagierSet k) :
    x ≤ k + 1 ∧ y ≤ k ∧ z ≤ k := by
  obtain ⟨_, _, _⟩ := zagierSet_lower_bound k h
  rw [zagierSet, mem_setOf_eq] at h
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

lemma zagierSet_subset : zagierSet k ⊆ Ioc 0 (k + 1) ×ˢ Ioc 0 k ×ˢ Ioc 0 k := by
  intro x h
  have lb := zagierSet_lower_bound k h
  have ub := zagierSet_upper_bound k h
  exact ⟨⟨lb.1, ub.1⟩, ⟨lb.2.1, ub.2.1⟩, ⟨lb.2.2, ub.2.2⟩⟩

noncomputable instance : Fintype (zagierSet k) :=
  (((finite_Ioc 0 (k + 1)).prod ((finite_Ioc 0 k).prod (finite_Ioc 0 k))).subset
    (zagierSet_subset k)).fintype

end Sets

section Involutions

open Function

variable (k : ℕ)

/-- The obvious involution `(x, y, z) ↦ (x, z, y)`. -/
def obvInvo : Function.End (zagierSet k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨x, z, y⟩, by
  simp only [zagierSet, Set.mem_setOf_eq] at h ⊢
  linarith [h]⟩

theorem obvInvo_sq : obvInvo k ^ 2 = 1 := rfl

/-- If `obvInvo k` has a fixed point, a representation of `4 * k + 1` as a sum of two squares
can be extracted from it. -/
theorem sq_add_sq_of_nonempty_fixedPoints (hn : (fixedPoints (obvInvo k)).Nonempty) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  simp only [sq]
  obtain ⟨⟨⟨x, y, z⟩, he⟩, hf⟩ := hn
  have := mem_fixedPoints_iff.mp hf
  simp only [obvInvo, Subtype.mk.injEq, Prod.mk.injEq, true_and] at this
  simp only [zagierSet, Set.mem_setOf_eq] at he
  use x, (2 * y)
  rw [show 2 * y * (2 * y) = 4 * y * y by linarith, ← he, this.1]

/-- The complicated involution, defined piecewise according to how `x` compares with
`y - z` and `2 * y`. -/
def complexInvo : Function.End (zagierSet k) := fun ⟨⟨x, y, z⟩, h⟩ =>
  ⟨if x + z < y then ⟨x + 2 * z, z, y - x - z⟩ else
   if 2 * y < x then ⟨x - 2 * y, x + z - y, y⟩ else
                     ⟨2 * y - x, y, x + z - y⟩, by
  split_ifs with less more <;> simp only [zagierSet, Set.mem_setOf_eq] at h ⊢
  · -- less: `x + z < y` (`x < y - z` as stated by Zagier)
    rw [Nat.sub_sub]; zify [less.le] at h ⊢; linarith [h]
  · -- more: `2 * y < x`
    push_neg at less; zify [less, more.le] at h ⊢; linarith [h]
  · -- middle: `x` is neither less than `y - z` or more than `2 * y`
    push_neg at less more; zify [less, more] at h ⊢; linarith [h]⟩

variable [hk : Fact (4 * k + 1).Prime]

/-- `complexInvo k` is indeed an involution. -/
theorem complexInvo_sq : complexInvo k ^ 2 = 1 := by
  change complexInvo k ∘ complexInvo k = id
  funext ⟨⟨x, y, z⟩, h⟩
  rw [comp_apply]
  obtain ⟨xb, _, _⟩ := zagierSet_lower_bound k h
  conv_lhs => arg 2; simp only [complexInvo]
  split_ifs with less more <;> rw [complexInvo, Subtype.mk.injEq, id_eq]
  · -- less
    simp only [show ¬(x + 2 * z + (y - x - z) < z) by linarith [less], ite_false,
      lt_add_iff_pos_left, xb, add_tsub_cancel_right, ite_true]
    rw [Nat.sub_sub, two_mul, ← tsub_add_eq_add_tsub (by linarith), ← add_assoc,
      Nat.add_sub_cancel, add_comm (x + z), Nat.sub_add_cancel less.le]
  · -- more
    push_neg at less
    simp only [show x - 2 * y + y < x + z - y by zify [less, more.le]; linarith, ite_true]
    rw [Nat.sub_add_cancel more.le, Nat.sub_right_comm, Nat.sub_sub _ _ y, ← two_mul, add_comm,
      Nat.add_sub_assoc more.le, Nat.add_sub_cancel]
  · -- middle
    push_neg at less more
    simp only [show ¬(2 * y - x + (x + z - y) < y) by zify [less, more]; linarith,
      show ¬(2 * y < 2 * y - x) by zify [more]; linarith, ite_false]
    rw [tsub_tsub_assoc (2 * y).le_refl more, tsub_self, zero_add,
      ← Nat.add_sub_assoc less, ← add_assoc, Nat.sub_add_cancel more, Nat.sub_sub _ _ y,
      ← two_mul, add_comm, Nat.add_sub_cancel]

/-- Any fixed point of `complexInvo k` must be `(1, 1, k)`. -/
theorem eq_of_mem_fixedPoints {t : zagierSet k} (mem : t ∈ fixedPoints (complexInvo k)) :
    t.val = (1, 1, k) := by
  obtain ⟨⟨x, y, z⟩, h⟩ := t
  obtain ⟨_, _, _⟩ := zagierSet_lower_bound k h
  rw [mem_fixedPoints_iff, complexInvo, Subtype.mk.injEq] at mem
  split_ifs at mem with less more <;>
    -- less (completely handled by the pre-applied `simp_all only`)
    simp_all only [not_lt, Prod.mk.injEq, add_eq_left, mul_eq_zero, false_or,
      lt_self_iff_false, reduceCtorEq]
  · -- more
    obtain ⟨_, _, _⟩ := mem; simp_all
  · -- middle (the one fixed point falls under this case)
    simp only [zagierSet, Set.mem_setOf_eq] at h
    replace mem := mem.1
    rw [tsub_eq_iff_eq_add_of_le more, ← two_mul] at mem
    replace mem := (mul_left_cancel₀ two_ne_zero mem).symm
    subst mem
    rw [show x * x + 4 * x * z = x * (x + 4 * z) by linarith] at h
    rcases (Nat.dvd_prime hk.out).1 (dvd_of_mul_left_eq _ h) with e | e
    · rw [e, mul_one] at h
      simp_all [h, show z = 0 by linarith [e]]
    · simp only [e, mul_left_eq_self₀, add_eq_zero, and_false, or_false, reduceCtorEq] at h
      simp only [h, true_and]
      linarith [e]

/-- The singleton containing `(1, 1, k)`. -/
def singletonFixedPoint : Finset (zagierSet k) :=
  {⟨(1, 1, k), (by simp only [zagierSet, Set.mem_setOf_eq]; linarith)⟩}

/-- `complexInvo k` has exactly one fixed point. -/
theorem card_fixedPoints_eq_one : Fintype.card (fixedPoints (complexInvo k)) = 1 := by
  rw [show 1 = Finset.card (singletonFixedPoint k) by rfl, ← Set.toFinset_card]
  congr
  rw [singletonFixedPoint, Finset.eq_singleton_iff_unique_mem]
  constructor
  · simp [IsFixedPt, complexInvo]
  · intro _ mem
    simp only [Set.mem_toFinset] at mem
    replace mem := eq_of_mem_fixedPoints k mem
    congr!

end Involutions

end Zagier

open Zagier

/-- **Fermat's theorem on sums of two squares** (Wiedijk #20).
Every prime congruent to 1 mod 4 is the sum of two squares, proved using Zagier's involutions. -/
theorem Nat.Prime.sq_add_sq' {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  rw [← div_add_mod p 4, hp] at h ⊢
  let k := p / 4
  apply sq_add_sq_of_nonempty_fixedPoints
  have key := (Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (obvInvo_sq k)).symm.trans
    (Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) (complexInvo_sq k))
  contrapose key
  rw [Set.not_nonempty_iff_eq_empty] at key
  simp_rw [k, key, Fintype.card_eq_zero, card_fixedPoints_eq_one]
  decide
