/-
Copyright (c) 2024 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt, Violeta Hernández
-/

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.PNat.Basic

/-!
# IMO 1982 Q1

The function `f` is defined for all positive integers `n` and takes on
non-negative integer values. Also, for all `m`, `n`

`f (m + n) - f(m) - f(n) = 0` or `1`
`f 2 = 0`, `f 3 > 0`, and `f 9999 = 3333`.

Determine `f 1982`.

The solution is based on the one at the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_1)
website.

We prove the helper lemmas:
1. `f m + f n ≤ f(m + n)` `superadditive`.
2. `n * f(m) ≤ f(m * n)` `superhomogeneous`.
3. `a * f a  + c * f d ≤ f (a * b + c * d)` `superlinear`, (derived from 1. and 2.).

So we can establish on the one hand that `f 1980 ≤ 660`,
by observing that `660 * 1 = 660 * f3 ≤ f 1980 = f (660 * 3)`.

On the other hand, we establish that `f 1980 ≥ 660`
from `5 * f 1980 + 33 * f 3 ≤ f (5 * 1980 + 33 * 1) = f 9999 = 3333`.

We then conclude `f 1980 = 660` and then eventually determine that either
`f 1982 = 660` or `f 1982 = 661`.

In the latter case we derive a contradiction, because if `f 1982 = 661` then
`3334 = 5 * f 1982 + 29 * f(3) + f(2) ≤ f (5 * 1982 + 29 * 3 + 2) = f 9999 = 3333`.
-/

namespace Imo1982Q1

structure IsGood (f : ℕ+ → ℕ) : Prop where
  /-- The function satisfies the functional relation. -/
  rel: ∀ m n : ℕ+, f (m + n) = f m + f n ∨ f (m + n) = f m + f n + 1
  f₂ : f 2 = 0
  hf₃ : 0 < f 3
  f_9999 : f 9999 = 3333

namespace IsGood

variable {f : ℕ+ → ℕ} (hf : IsGood f)
include hf

lemma f₁ : f 1 = 0 := by
  have h : f 2 = 2 * f 1 ∨ f 2 = 2 * f 1 + 1 := by rw [two_mul]; exact hf.rel 1 1
  obtain h₁ | h₂ := hf.f₂ ▸ h
  · rw [eq_comm, mul_eq_zero] at h₁
    apply h₁.resolve_left
    norm_num
  · cases Nat.succ_ne_zero _ h₂.symm

lemma f₃ : f 3 = 1 := by
  have h : f 3 = f 2 + f 1 ∨ f 3 = f 2 + f 1 + 1 := hf.rel 2 1
  rw [hf.f₁, hf.f₂, add_zero, zero_add] at h
  exact h.resolve_left hf.hf₃.ne'

lemma superadditive {m n : ℕ+} : f m + f n ≤ f (m + n) := by have h := hf.rel m n; grind

lemma superhomogeneous {m n : ℕ+} : ↑n * f m ≤ f (n * m) := by
  induction n with
  | one => simp
  | succ n' ih =>
    calc
    ↑(n' + 1) * f m = ↑n' * f m + f m := by rw [PNat.add_coe, add_mul, PNat.val_ofNat, one_mul]
    _ ≤ f (n' * m) + f m := by gcongr
    _ ≤ f (n' * m + m) := hf.superadditive
    _ = f ((n' + 1) * m) := by congr; rw [add_mul, one_mul]

lemma superlinear {a b c d : ℕ+} : a * f b + c * f d ≤ f (a * b + c * d) :=
  (add_le_add hf.superhomogeneous hf.superhomogeneous).trans hf.superadditive

lemma le_mul_three_apply (n : ℕ+) : n ≤ f (3 * n) := by
  rw [← mul_one (n : ℕ), ← hf.f₃, mul_comm 3]
  exact hf.superhomogeneous

lemma part_1 : 660 ≤ f (1980) := by
  exact hf.le_mul_three_apply 660

lemma part_2 : f 1980 ≤ 660 := by
  have h : 5 * f 1980 + 33 * f 3 ≤ 5 * 660 + 33 := by
    calc (5 : ℕ+) * f 1980 + (33 : ℕ+) * f 3 ≤ f (5 * 1980 + 33 * 3) := by apply hf.superlinear
    _ = f 9999 := by rfl
    _ = 5 * 660 + 33 := by rw [hf.f_9999]
  rw [hf.f₃, mul_one] at h
  -- from 5 * f 1980 + 33 ≤ 5 * 660 + 33 we show f 1980 ≤ 660
  linarith

end IsGood

end Imo1982Q1

open Imo1982Q1

lemma imo1982_q1 {f : ℕ+ → ℕ} (hf : IsGood f) : f 1982 = 660 := by
  have f_1980 := hf.part_2.antisymm hf.part_1
  have h : f 1982 = f 1980 + f 2 ∨ f 1982 = f 1980 + f 2 + 1 := hf.rel 1980 2
  rw [f_1980, hf.f₂, add_zero] at h
  apply h.resolve_right
  intro hr
  suffices h : 3334 ≤ 3333 by simp at h
  calc
    3334 = 5 * f 1982 + 29 * f 3 + f 2 := by rw [hf.f₃, hf.f₂, hr, add_zero, mul_one]
    (5 : ℕ+) * f 1982 + (29 : ℕ+) * f 3 + f 2 ≤ f (5 * 1982 + 29 * 3) + f 2 :=
      add_le_add_right hf.superlinear _
    _ ≤ f (5 * 1982 + 29 * 3 + 2) := hf.superadditive
    _ = 3333 := hf.f_9999
