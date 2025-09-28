/-
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dylan MacKenzie
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Abel

/-!
# Summation by parts
-/

namespace Finset
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

-- The partial sum of `g`, starting from zero
local notation "G " n:80 => ∑ i ∈ range n, g i

/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
theorem sum_Ico_by_parts (hmn : m < n) :
    ∑ i ∈ Ico m n, f i • g i =
      f (n - 1) • G n - f m • G m - ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  have h₁ : (∑ i ∈ Ico (m + 1) n, f i • G i) = ∑ i ∈ Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn), ← sum_Ico_add']
    simp only [add_tsub_cancel_right]
  have h₂ :
    (∑ i ∈ Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i ∈ Ico m (n - 1), f i • G (i + 1)) + f (n - 1) • G n - f m • G (m + 1) := by
    rw [← sum_Ico_sub_bot _ hmn, ← sum_Ico_succ_sub_top _ (Nat.le_sub_one_of_lt hmn),
      Nat.sub_add_cancel (pos_of_gt hmn), sub_add_cancel]
  rw [sum_eq_sum_Ico_succ_bot hmn]
  conv in (occs := 3) (f _ • g _) => rw [← sum_range_succ_sub_sum g]
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁]
  conv_lhs => congr; rfl; rw [← add_sub, add_comm, ← add_sub, ← sum_sub_distrib]
  have : ∀ i, f i • G (i + 1) - f (i + 1) • G (i + 1) = -((f (i + 1) - f i) • G (i + 1)) := by
    intro i
    rw [sub_smul]
    abel
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add]
  abel

theorem sum_Ioc_by_parts (hmn : m < n) :
    ∑ i ∈ Ioc m n, f i • g i =
      f n • G (n + 1) - f (m + 1) • G (m + 1)
        - ∑ i ∈ Ioc m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  simpa only [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_of_lt hmn),
    add_tsub_cancel_right] using sum_Ico_by_parts f g (Nat.succ_lt_succ hmn)

variable (n)

/-- **Summation by parts** for ranges -/
theorem sum_range_by_parts :
    ∑ i ∈ range n, f i • g i =
      f (n - 1) • G n - ∑ i ∈ range (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [range_eq_Ico, sum_Ico_by_parts f g (Nat.pos_of_ne_zero hn), sum_range_zero, smul_zero,
      sub_zero, range_eq_Ico]

end Finset
