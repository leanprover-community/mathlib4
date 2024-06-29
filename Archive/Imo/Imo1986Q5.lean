/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Real.NNReal

/-!
# IMO 1986 Q5

Find all functions `f`, defined on the non-negative real numbers and taking nonnegative real values,
such that:

- $f(xf(y))f(y) = f(x + y)$ for all $x, y \ge 0$,
- $f(2) = 0$,
- $f(x) \ne 0$ for $0 \le x < 2$.

We formalize the assumptions on `f` in `Imo1986Q5.IsGood` predicate,
then prove `Imo1986Q5.IsGood f ↔ f = fun x ↦ 2 / (2 - x)`.

Note that this formalization relies on the fact that Mathlib uses 0 as the "garbage value",
namely for `2 ≤ x` we have `2 - x = 0` and `2 / (2 - x) = 0`.

Formalization is based on
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1986_IMO_Problems/Problem_5)
with minor modifications.
-/

open Set NNReal Classical

namespace Imo1986Q5

structure IsGood (f : ℝ≥0 → ℝ≥0) : Prop where
  map_add_rev x y : f (x * f y) * f y = f (x + y)
  map_two : f 2 = 0
  map_ne_zero : ∀ x < 2, f x ≠ 0

namespace IsGood

variable {f : ℝ≥0 → ℝ≥0} (hf : IsGood f) {x y : ℝ≥0}

theorem map_add (x y : ℝ≥0) : f (x + y) = f (x * f y) * f y :=
  (hf.map_add_rev x y).symm

theorem map_eq_zero : f x = 0 ↔ 2 ≤ x := by
  refine ⟨fun hx₀ ↦ not_lt.1 fun hlt ↦ hf.map_ne_zero x hlt hx₀, fun hle ↦ ?_⟩
  rcases exists_add_of_le hle with ⟨x, rfl⟩
  rw [add_comm, hf.map_add, hf.map_two, mul_zero]

theorem map_ne_zero_iff : f x ≠ 0 ↔ x < 2 := by simp [hf.map_eq_zero]

theorem map_of_lt_two (hx : x < 2) : f x = 2 / (2 - x) := by
  have hx' : 2 - x ≠ 0 := (tsub_pos_of_lt hx).ne'
  have hfx : f x ≠ 0 := hf.map_ne_zero_iff.2 hx
  apply le_antisymm
  · rw [NNReal.le_div_iff hx', ← NNReal.le_div_iff' hfx, tsub_le_iff_right, ← hf.map_eq_zero,
     hf.map_add, div_mul_cancel₀ _ hfx, hf.map_two, zero_mul]
  · rw [NNReal.div_le_iff' hx', ← hf.map_eq_zero]
    refine (mul_eq_zero.1 ?_).resolve_right hfx
    rw [hf.map_add_rev, hf.map_eq_zero, tsub_add_cancel_of_le hx.le]

theorem map_eq (x : ℝ≥0) : f x = 2 / (2 - x) :=
  match lt_or_le x 2 with
  | .inl hx => hf.map_of_lt_two hx
  | .inr hx => by rwa [tsub_eq_zero_of_le hx, div_zero, hf.map_eq_zero]

end IsGood

theorem isGood_iff {f : ℝ≥0 → ℝ≥0} : IsGood f ↔ f = fun x ↦ 2 / (2 - x) := by
  refine ⟨fun hf ↦ funext hf.map_eq, ?_⟩
  rintro rfl
  constructor
  case map_two => simp
  case map_ne_zero => intro x hx; simpa [tsub_eq_zero_iff_le]
  case map_add_rev =>
    intro x y
    cases lt_or_le y 2 with
    | inl hy =>
      have hy' : 2 - y ≠ 0 := (tsub_pos_of_lt hy).ne'
      rw [div_mul_div_comm, tsub_mul, mul_assoc, div_mul_cancel₀ _ hy', mul_comm x,
        ← mul_tsub, tsub_add_eq_tsub_tsub_swap, mul_div_mul_left _ _ two_ne_zero]
    | inr hy =>
      have : 2 ≤ x + y := le_add_left hy
      simp [tsub_eq_zero_of_le, *]
