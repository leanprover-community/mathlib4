/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Convergence to ±infinity in linear ordered (semi)fields
-/

namespace Filter

variable {α β : Type*}

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  {l : Filter β} {f : β → α} {r c : α} {n : ℕ}

/-!
### Multiplication by constant: iff lemmas
-/

/-- If `r` is a positive constant, `fun x ↦ r * f x` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter. -/
theorem tendsto_const_mul_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop :=
  ⟨fun h => h.atTop_of_const_mul₀ hr, fun h =>
    Tendsto.atTop_of_const_mul₀ (inv_pos.2 hr) <| by simpa only [inv_mul_cancel_left₀ hr.ne'] ⟩

/-- If `r` is a positive constant, `fun x ↦ f x * r` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter. -/
theorem tendsto_mul_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_pos hr

/-- If `r` is a positive constant, `x ↦ f x / r` tends to infinity along a filter
if and only if `f` tends to infinity along the same filter. -/
lemma tendsto_div_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ Tendsto f l atTop := by
  simpa only [div_eq_mul_inv] using tendsto_mul_const_atTop_of_pos (inv_pos.2 hr)

/-- If `f` tends to infinity along a nontrivial filter `l`, then
`fun x ↦ r * f x` tends to infinity if and only if `0 < r`. -/
theorem tendsto_const_mul_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r := by
  refine ⟨fun hrf => not_le.mp fun hr => ?_, fun hr => (tendsto_const_mul_atTop_of_pos hr).mpr h⟩
  rcases ((h.eventually_ge_atTop 0).and (hrf.eventually_gt_atTop 0)).exists with ⟨x, hx, hrx⟩
  exact (mul_nonpos_of_nonpos_of_nonneg hr hx).not_gt hrx

/-- If `f` tends to infinity along a nontrivial filter `l`, then
`fun x ↦ f x * r` tends to infinity if and only if `0 < r`. -/
theorem tendsto_mul_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_pos h]

/-- If `f` tends to infinity along a nontrivial filter `l`, then
`x ↦ f x * r` tends to infinity if and only if `0 < r`. -/
lemma tendsto_div_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ 0 < r := by
  simp only [div_eq_mul_inv, tendsto_mul_const_atTop_iff_pos h, inv_pos]

/-- If `f` tends to infinity along a filter, then `f` multiplied by a positive
constant (on the left) also tends to infinity. For a version working in `ℕ` or `ℤ`, use
`Filter.Tendsto.const_mul_atTop'` instead. -/
theorem Tendsto.const_mul_atTop (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_pos hr).2 hf

/-- If a function `f` tends to infinity along a filter, then `f` multiplied by a positive
constant (on the right) also tends to infinity. For a version working in `ℕ` or `ℤ`, use
`Filter.Tendsto.atTop_mul_const'` instead. -/
theorem Tendsto.atTop_mul_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_pos hr).2 hf

/-- If a function `f` tends to infinity along a filter, then `f` divided by a positive
constant also tends to infinity. -/
theorem Tendsto.atTop_div_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atTop := by
  simpa only [div_eq_mul_inv] using hf.atTop_mul_const (inv_pos.2 hr)

theorem tendsto_const_mul_pow_atTop (hn : n ≠ 0) (hc : 0 < c) :
    Tendsto (fun x => c * x ^ n) atTop atTop :=
  Tendsto.const_mul_atTop hc (tendsto_pow_atTop hn)

theorem tendsto_const_mul_pow_atTop_iff :
    Tendsto (fun x => c * x ^ n) atTop atTop ↔ n ≠ 0 ∧ 0 < c := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => tendsto_const_mul_pow_atTop h.1 h.2⟩
  · rintro rfl
    simp only [pow_zero, not_tendsto_const_atTop] at h
  · rcases ((h.eventually_gt_atTop 0).and (eventually_ge_atTop 0)).exists with ⟨k, hck, hk⟩
    exact pos_of_mul_pos_left hck (pow_nonneg hk _)

lemma tendsto_zpow_atTop_atTop {n : ℤ} (hn : 0 < n) : Tendsto (fun x : α ↦ x ^ n) atTop atTop := by
  lift n to ℕ using hn.le; simp [(Int.natCast_pos.mp hn).ne']

end LinearOrderedSemifield


section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {l : Filter β} {f : β → α} {r : α}

/-- If `r` is a positive constant, `fun x ↦ r * f x` tends to negative infinity along a filter
if and only if `f` tends to negative infinity along the same filter. -/
theorem tendsto_const_mul_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot := by
  simpa only [← mul_neg, ← tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos hr

/-- If `r` is a positive constant, `fun x ↦ f x * r` tends to negative infinity along a filter
if and only if `f` tends to negative infinity along the same filter. -/
theorem tendsto_mul_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_pos hr

/-- If `r` is a positive constant, `fun x ↦ f x / r` tends to negative infinity along a filter
if and only if `f` tends to negative infinity along the same filter. -/
lemma tendsto_div_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_pos, hr]

/-- If `r` is a negative constant, `fun x ↦ r * f x` tends to infinity along a filter `l`
if and only if `f` tends to negative infinity along `l`. -/
theorem tendsto_const_mul_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atBot := by
  simpa only [neg_mul, tendsto_neg_atBot_iff] using tendsto_const_mul_atBot_of_pos (neg_pos.2 hr)

/-- If `r` is a negative constant, `fun x ↦ f x * r` tends to infinity along a filter `l`
if and only if `f` tends to negative infinity along `l`. -/
theorem tendsto_mul_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_neg hr

/-- If `r` is a negative constant, `fun x ↦ f x / r` tends to infinity along a filter `l`
if and only if `f` tends to negative infinity along `l`. -/
lemma tendsto_div_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_of_neg, hr]

/-- If `r` is a negative constant, `fun x ↦ r * f x` tends to negative infinity along a filter `l`
if and only if `f` tends to infinity along `l`. -/
theorem tendsto_const_mul_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop := by
  simpa only [neg_mul, tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos (neg_pos.2 hr)

/-- If `r` is a negative constant, `fun x ↦ f x * r` tends to negative infinity along a filter `l`
if and only if `f` tends to infinity along `l`. -/
theorem tendsto_mul_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_neg hr

/-- If `r` is a negative constant, `fun x ↦ f x / r` tends to negative infinity along a filter `l`
if and only if `f` tends to infinity along `l`. -/
lemma tendsto_div_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_neg, hr]

/-- The function `fun x ↦ r * f x` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to negative infinity. -/
theorem tendsto_const_mul_atTop_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_neg]
  · simp [not_tendsto_const_atTop]
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_pos]

/-- The function `fun x ↦ f x * r` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to negative infinity. -/
theorem tendsto_mul_const_atTop_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff]

/-- The function `fun x ↦ f x / r` tends to infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to infinity or `r < 0` and `f` tends to negative infinity. -/
lemma tendsto_div_const_atTop_iff [NeBot l] :
    Tendsto (fun x ↦ f x / r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff]

/-- The function `fun x ↦ r * f x` tends to negative infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` tends to infinity. -/
theorem tendsto_const_mul_atBot_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [← tendsto_neg_atTop_iff, ← mul_neg, tendsto_const_mul_atTop_iff, neg_neg]

/-- The function `fun x ↦ f x * r` tends to negative infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` tends to infinity. -/
theorem tendsto_mul_const_atBot_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff]

/-- The function `fun x ↦ f x / r` tends to negative infinity along a nontrivial filter
if and only if `r > 0` and `f` tends to negative infinity or `r < 0` and `f` tends to infinity. -/
lemma tendsto_div_const_atBot_iff [NeBot l] :
    Tendsto (fun x ↦ f x / r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff]

/-- If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ r * f x` tends to infinity if and only if `r < 0`. -/
theorem tendsto_const_mul_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop ↔ r < 0 := by
  simp [tendsto_const_mul_atTop_iff, h, h.not_tendsto disjoint_atBot_atTop]

/-- If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ f x * r` tends to infinity if and only if `r < 0`. -/
theorem tendsto_mul_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_neg h]

/-- If `f` tends to negative infinity along a nontrivial filter `l`,
then `fun x ↦ f x / r` tends to infinity if and only if `r < 0`. -/
lemma tendsto_div_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ f x / r) l atTop ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg h]

/-- If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ r * f x` tends to negative infinity if and only if `0 < r`. -/
theorem tendsto_const_mul_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atBot_atTop]

/-- If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ f x * r` tends to negative infinity if and only if `0 < r`. -/
theorem tendsto_mul_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_pos h]

/-- If `f` tends to negative infinity along a nontrivial filter `l`, then
`fun x ↦ f x / r` tends to negative infinity if and only if `0 < r`. -/
lemma tendsto_div_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ 0 < r := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos h]

/-- If `f` tends to infinity along a nontrivial filter,
`fun x ↦ r * f x` tends to negative infinity if and only if `r < 0`. -/
theorem tendsto_const_mul_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot ↔ r < 0 := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atTop_atBot]

/-- If `f` tends to infinity along a nontrivial filter,
`fun x ↦ f x * r` tends to negative infinity if and only if `r < 0`. -/
theorem tendsto_mul_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_neg h]

/-- If `f` tends to infinity along a nontrivial filter,
`fun x ↦ f x / r` tends to negative infinity if and only if `r < 0`. -/
lemma tendsto_div_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atBot ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg h]

/-- If a function `f` tends to infinity along a filter,
then `f` multiplied by a negative constant (on the left) tends to negative infinity. -/
theorem Tendsto.const_mul_atTop_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_neg hr).2 hf

/-- If a function `f` tends to infinity along a filter,
then `f` multiplied by a negative constant (on the right) tends to negative infinity. -/
theorem Tendsto.atTop_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_neg hr).2 hf

/-- If a function `f` tends to infinity along a filter,
then `f` divided by a negative constant tends to negative infinity. -/
lemma Tendsto.atTop_div_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x ↦ f x / r) l atBot := (tendsto_div_const_atBot_of_neg hr).2 hf

/-- If a function `f` tends to negative infinity along a filter, then `f` multiplied by
a positive constant (on the left) also tends to negative infinity. -/
theorem Tendsto.const_mul_atBot (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_pos hr).2 hf

/-- If a function `f` tends to negative infinity along a filter, then `f` multiplied by
a positive constant (on the right) also tends to negative infinity. -/
theorem Tendsto.atBot_mul_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_pos hr).2 hf

/-- If a function `f` tends to negative infinity along a filter, then `f` divided by
a positive constant also tends to negative infinity. -/
theorem Tendsto.atBot_div_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x / r) l atBot := (tendsto_div_const_atBot_of_pos hr).2 hf

/-- If a function `f` tends to negative infinity along a filter,
then `f` multiplied by a negative constant (on the left) tends to positive infinity. -/
theorem Tendsto.const_mul_atBot_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_neg hr).2 hf

/-- If a function tends to negative infinity along a filter,
then `f` multiplied by a negative constant (on the right) tends to positive infinity. -/
theorem Tendsto.atBot_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_neg hr).2 hf

theorem tendsto_neg_const_mul_pow_atTop {c : α} {n : ℕ} (hn : n ≠ 0) (hc : c < 0) :
    Tendsto (fun x => c * x ^ n) atTop atBot :=
  (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc

theorem tendsto_const_mul_pow_atBot_iff {c : α} {n : ℕ} :
    Tendsto (fun x => c * x ^ n) atTop atBot ↔ n ≠ 0 ∧ c < 0 := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul, tendsto_const_mul_pow_atTop_iff, neg_pos]

end LinearOrderedField
end Filter
