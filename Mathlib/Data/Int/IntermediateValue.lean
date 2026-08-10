/-
Copyright (c) 2026 Alper FERUDUN. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alper FERUDUN
-/
module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic

/-! # A discrete intermediate value theorem

An integer-valued sequence whose consecutive terms differ by at most `1` attains every integer
value lying between two of its terms. This is the discrete analogue of the intermediate value
theorem for a unit-step walk on `ℤ`, the continuous version of which is
`intermediate_value_Icc` in `Mathlib/Topology/Order/IntermediateValue.lean`.

## Main results

* `Int.exists_eq_of_natAbs_sub_le_one`: the discrete intermediate value theorem.

The statement and proof are due to Alper FERUDUN, who wrote them for
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/pull/4218).
-/

@[expose] public section

/-- **Discrete intermediate value theorem.** If an integer-valued sequence `f : ℕ → ℤ` has
consecutive terms differing by at most `1`, then it attains every value between `f a` and `f b`:
for `a ≤ b` and `f a ≤ t ≤ f b` there is some index `c ∈ [a, b]` with `f c = t`. -/
theorem Int.exists_eq_of_natAbs_sub_le_one (f : ℕ → ℤ)
    (hf : ∀ n, (f (n + 1) - f n).natAbs ≤ 1) {a b : ℕ} (hab : a ≤ b) {t : ℤ}
    (hta : f a ≤ t) (htb : t ≤ f b) : ∃ c, a ≤ c ∧ c ≤ b ∧ f c = t := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, le_refl a, le_refl a, le_antisymm hta htb⟩
  | succ b hb ih =>
    by_cases h : t ≤ f b
    · obtain ⟨c, hac, hcb, hfc⟩ := ih h
      exact ⟨c, hac, by omega, hfc⟩
    · have hstep := hf b
      exact ⟨b + 1, by omega, le_refl _, by omega⟩
