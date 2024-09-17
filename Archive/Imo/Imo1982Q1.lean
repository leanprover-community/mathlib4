/-
Copyright (c) 2024 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt, Violeta Hernández
-/

import Mathlib.Tactic.NormNum
import Mathlib.Data.PNat.Basic

/-!
# IMO 1982 Q1

The function $f(n)$ is defined for all postive integers $n$ and takes on
non-negative integer values. Also, for all $m$, $n$

$f (m + n) - f(m) - f(n) = 0 \text{ or } 1$
$f(2) = 0, f(3) > 0, and f(9999) = 3333.$

Determine $f(1982)$.

The solution is based on the one at the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_1)
website.

We prove that $f(mn) \geq nf(m)$ and $f(m) + f(n) ≤ f(m + n)$
to establish both that $f(1980) ≤ 660$ and that these properties added with $f(9999) = 3333$
to establish that $f(1980) ≥ 660$.
Both these together allow to conclude $f(1980) = 660$ and then eventually determine $f(1982) = 660$.
-/

namespace Imo1982Q1

structure IsGood (f : ℕ+ → ℕ) : Prop where
  /-- Satisfies the functional relation-/
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
    have h : f 3 = f 2 + f 1 ∨ f 3  = f 2 + f 1 + 1 := by apply hf.rel 2 1
    rw [hf.f₁, hf.f₂, add_zero, zero_add] at h
    have not_left : ¬ f 3 = 0 := by apply ne_of_gt hf.hf₃
    rw [or_iff_right (not_left)] at h
    exact h

lemma superhomogeneity {m n : ℕ+} : ↑n * f m ≤ f (n * m) := by
  induction n using PNat.recOn
  case p1 => simp
  case hp n' ih =>
    have rel : f (n' * m + m) = f (n' * m) + f (m) ∨
               f (n' * m + m) = f (n' * m) + f (m) + 1 := hf.rel (n' * m) m
    calc
    ↑(n' + 1) * f m = ↑n' * f m + f m := by rw [PNat.add_coe, add_mul, PNat.val_ofNat, one_mul];
    _ ≤ f (n' * m) + f m := add_le_add_right ih (f m)
    _ ≤ f (n' * m + m) := by
      rcases rel with ( hl | hr)
      · rw [hl]
      · rw [hr]; nth_rewrite 1 [← add_zero (f m), ← add_assoc]; apply add_le_add_left (by norm_num)
    _ = f ((n' + 1) * m) := by congr; rw [add_mul, one_mul]

lemma superadditive {m n : ℕ+} : f m + f n ≤ f (m + n) := by
  have h := hf.rel m n
  rcases h with ( hl | hr )
  · rw [hl]
  · rw [hr]; nth_rewrite 1 [← add_zero (f n), ← add_assoc]; apply add_le_add_right (by norm_num)

lemma superlinear {a b c d : ℕ+} : a * f b + c * f d ≤ f (a * b + c * d) :=
  (add_le_add hf.superhomogeneity hf.superhomogeneity).trans hf.superadditive

lemma part_1 : 660 ≤ f (1980) := by
  rw [← mul_one (660), ← PNat.val_ofNat 660, ← hf.f₃]; apply hf.superhomogeneity

lemma part_2 : f 1980 ≤ 660 := by
  have h : 5 * f 1980 + 33 * f 3 ≤ 5 * 660 + 33 := by
    calc (5 : ℕ+) * f 1980 + (33 : ℕ+) * f 3 ≤  f (5 * 1980 + 33 * 3) := by apply hf.superlinear
    _ = f 9999 := by rfl
    _ = 5 * 660 + 33 := by rw [hf.f_9999]
  rw [hf.f₃, mul_one] at h
  -- from 5 * f 1980 + 33 ≤ 5 * 660 + 33 we show f 1980 ≤ 660
  exact le_of_mul_le_mul_left (le_of_add_le_add_right h) (Nat.succ_pos 4)

end IsGood

lemma imo1982_q1 {f : ℕ+ → ℕ} (hf : IsGood f) : f 1982 = 660 := by
  have f_1980 := hf.part_2.antisymm hf.part_1
  have h : f 1982 = f 1980 + f 2 ∨ f 1982 = f 1980 + f 2 + 1 := hf.rel 1980 2
  rw [f_1980, hf.f₂, add_zero] at h
  apply h.resolve_right
  intro hr
  have h : 3334 ≤ 3333 := by -- a contradiction
    calc
      3334 = 5 * f 1982 + 29 * f 3 + f 2 := by rw [hf.f₃, hf.f₂, hr, add_zero, mul_one]
      (5 : ℕ+) * f 1982 + (29 : ℕ+) * f 3 + f 2 ≤ f (5 * 1982 + 29 * 3) + f 2 :=
        add_le_add_right hf.superlinear _
      _ ≤ f (5 * 1982 + 29 * 3 + 2) := hf.superadditive
      _ = 3333 := hf.f_9999
  norm_num at h

end Imo1982Q1
