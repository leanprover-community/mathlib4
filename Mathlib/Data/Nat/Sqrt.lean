/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.sqrt
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.ForSqrtEssential

/-!
# Square root of natural numbers

This file defines an efficient implementation of the square root function that returns the
unique `r` such that `r * r ≤ n < (r + 1) * (r + 1)`.

## Reference

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/


namespace Nat

theorem sqrtAux_dec {b} (h : b ≠ 0) : shiftr b 2 < b := by
  simp only [shiftr_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul' (by decide : 0 < 4)).2
  have := Nat.mul_lt_mul_of_pos_left (by decide : 1 < 4) (Nat.pos_of_ne_zero h)
  rwa [mul_one] at this
#align nat.sqrt_aux_dec Nat.sqrtAux_dec

/-- Auxiliary function for `Nat.sqrt`. See e.g.
<https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)> -/
def sqrtAux : ℕ → ℕ → ℕ → ℕ
  | b, r, n =>
    if b0 : b = 0 then r
    else
      let b' := shiftr b 2
      have : b' < b := sqrtAux_dec b0
      match (n - (r + b : ℕ) : ℤ) with
      | (n' : ℕ) => sqrtAux b' (div2 r + b) n'
      | _ => sqrtAux b' (div2 r) n
#align nat.sqrt_aux Nat.sqrtAux

-- porting note: this is the binary implementation of the square root algorithm, which is not used
-- porting note: the lemmas in the rest of this file are about the `Nat.sqrt` function
/-
/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/
@[pp_nodot]
def sqrt (n : ℕ) : ℕ :=
  match size n with
  | 0 => 0
  | succ s => sqrtAux (shiftl 1 (bit0 (div2 s))) 0 n
#align nat.sqrt Nat.sqrt
-/

theorem sqrtAux_0 (r n) : sqrtAux 0 r n = r := rfl
#align nat.sqrt_aux_0 Nat.sqrtAux_0

attribute [local simp] sqrtAux_0

-- porting note: this linting issue could be fixed if one wrote equation lemmas for sqrtAux
-- but this seems tricky
@[nolint unusedHavesSuffices]
theorem sqrtAux_1 {r n b} (h : b ≠ 0) {n'} (h₂ : r + b + n' = n) :
    sqrtAux b r n = sqrtAux (shiftr b 2) (div2 r + b) n' := by
  rw [sqrtAux]; simp only [h, h₂.symm, Int.ofNat_add, if_false];
    (rw [add_comm _ (n' : ℤ), add_sub_cancel, sqrtAux]; rfl)
#align nat.sqrt_aux_1 Nat.sqrtAux_1

-- porting note: this linting issue could be fixed if one wrote equation lemmas for sqrtAux
-- but this seems tricky
@[nolint unusedHavesSuffices]
theorem sqrtAux_2 {r n b} (h : b ≠ 0) (h₂ : n < r + b) :
    sqrtAux b r n = sqrtAux (shiftr b 2) (div2 r) n := by
  rw [sqrtAux]; simp only [h, h₂, if_false]
  cases' Int.eq_negSucc_of_lt_zero (sub_lt_zero.2 (Int.ofNat_lt_ofNat_of_lt h₂)) with k e
  rw [e, sqrtAux]
  rfl
#align nat.sqrt_aux_2 Nat.sqrtAux_2

private def IsSqrt (n q : ℕ) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)
-- #align nat.is_sqrt Nat.IsSqrt

attribute [-simp] mul_eq_mul_left_iff mul_eq_mul_right_iff

private theorem sqrtAux_IsSqrt_lemma (m r n : ℕ) (h₁ : r * r ≤ n) (m')
    (hm : shiftr (2 ^ m * 2 ^ m) 2 = m')
    (H1 : n < (r + 2 ^ m) * (r + 2 ^ m) → IsSqrt n (sqrtAux m' (r * 2 ^ m) (n - r * r)))
    (H2 :
      (r + 2 ^ m) * (r + 2 ^ m) ≤ n →
        IsSqrt n (sqrtAux m' ((r + 2 ^ m) * 2 ^ m) (n - (r + 2 ^ m) * (r + 2 ^ m)))) :
    IsSqrt n (sqrtAux (2 ^ m * 2 ^ m) (2 * r * 2 ^ m) (n - r * r)) := by
  have b0 : 2 ^ m * 2 ^ m ≠ 0 := mul_self_ne_zero.2 (pow_ne_zero m two_ne_zero)
  have lb : n - r * r < 2 * r * 2 ^ m + 2 ^ m * 2 ^ m ↔ n < (r + 2 ^ m) * (r + 2 ^ m) := by
    rw [tsub_lt_iff_right h₁]
    simp [left_distrib, right_distrib, two_mul, mul_comm, mul_assoc, add_comm, add_assoc,
      add_left_comm]
  have re : div2 (2 * r * 2 ^ m) = r * 2 ^ m := by
    rw [div2_val, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 2 > 0)]
  cases' lt_or_ge n ((r + 2 ^ m) * (r + 2 ^ m)) with hl hl
  · rw [sqrtAux_2 b0 (lb.2 hl), hm, re]
    apply H1 hl
  · cases' le.dest hl with n' e
    rw [@sqrtAux_1 (2 * r * 2 ^ m) (n - r * r) (2 ^ m * 2 ^ m) b0 (n - (r + 2 ^ m) * (r + 2 ^ m)),
      hm, re, ← right_distrib]
    · apply H2 hl
    apply Eq.symm
    apply tsub_eq_of_eq_add_rev
    rw [← add_assoc, (_ : r * r + _ = _)]
    exact (add_tsub_cancel_of_le hl).symm
    simp [left_distrib, right_distrib, two_mul, mul_comm, mul_assoc, add_assoc]
-- #align nat.sqrt_aux_is_sqrt_lemma Nat.sqrtAux_IsSqrt_lemma

private theorem sqrtAux_IsSqrt (n) :
    ∀ m r,
      r * r ≤ n →
        n < (r + 2 ^ (m + 1)) * (r + 2 ^ (m + 1)) →
          IsSqrt n (sqrtAux (2 ^ m * 2 ^ m) (2 * r * 2 ^ m) (n - r * r))
  | 0, r, h₁, h₂ => by
    apply sqrtAux_IsSqrt_lemma 0 r n h₁ 0 rfl <;> intro h <;> simp <;> [exact ⟨h₁, h⟩,
      exact ⟨h, h₂⟩]
  | m + 1, r, h₁, h₂ => by
    apply
        sqrtAux_IsSqrt_lemma (m + 1) r n h₁ (2 ^ m * 2 ^ m)
          (by simp [shiftr, pow_succ, div2_val, mul_comm, mul_left_comm]) <;>
      intro h
    · have := sqrtAux_IsSqrt _ m r h₁ h
      rw [mul_comm 2, mul_assoc, mul_comm 2] at this
      exact this
    · rw [pow_succ, mul_two, ← add_assoc] at h₂
      have := sqrtAux_IsSqrt _ m (r + 2 ^ (m + 1)) h h₂
      rw [mul_comm 2, mul_assoc, mul_comm 2] at this
      exact this
-- #align nat.sqrt_aux_is_sqrt nat.sqrtAux_IsSqrt

-- Porting note: as the definition of square root has changed,
-- the proof of `sqrt_IsSqrt` is attempted from scratch.
/-
Sketch of proof:
Up to rounding, in terms of the definition of `sqrt.iter`,

* By AM-GM inequality, `next² ≥ n` giving one of the bounds.
* When we terminated, we have `guess ≥ next` from which we deduce the other bound `n ≥ next²`.

To turn this into a lean proof we need to manipulate, use properties of natural number division etc.
-/
private theorem sqrt_IsSqrt (n : ℕ) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp [IsSqrt]
  | 1 => simp [IsSqrt]
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le _ _, sqrt.lt_iter_succ_sq _ _ ?_⟩
    simp only [mul_add, add_mul, one_mul, mul_one, ← add_assoc]
    rw [lt_add_one_iff, add_assoc, ← mul_two]
    refine le_trans (div_add_mod' (n + 2) 2).ge ?_
    rw [add_comm, add_le_add_iff_right, add_mod_right]
    simp only [zero_lt_two, add_div_right, succ_mul_succ_eq]
    refine le_trans (b := 1) ?_ ?_
    · exact (lt_succ.1 $ mod_lt n zero_lt_two)
    · simp only [le_add_iff_nonneg_left]; exact zero_le _
-- #align nat.sqrt_is_sqrt Nat.sqrt_IsSqrt

theorem sqrt_le (n : ℕ) : sqrt n * sqrt n ≤ n :=
  (sqrt_IsSqrt n).left
#align nat.sqrt_le Nat.sqrt_le

theorem sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n :=
  Eq.trans_le (sq (sqrt n)) (sqrt_le n)
#align nat.sqrt_le' Nat.sqrt_le'

theorem lt_succ_sqrt (n : ℕ) : n < succ (sqrt n) * succ (sqrt n) :=
  (sqrt_IsSqrt n).right
#align nat.lt_succ_sqrt Nat.lt_succ_sqrt

theorem lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 :=
  (sq (succ (sqrt n))).symm ▸ (lt_succ_sqrt n)
#align nat.lt_succ_sqrt' Nat.lt_succ_sqrt'

theorem sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)
#align nat.sqrt_le_add Nat.sqrt_le_add

theorem le_sqrt {m n : ℕ} : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h => le_trans (mul_self_le_mul_self h) (sqrt_le n), fun h =>
    le_of_lt_succ <| mul_self_lt_mul_self_iff.2 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩
#align nat.le_sqrt Nat.le_sqrt

theorem le_sqrt' {m n : ℕ} : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [pow_two] using le_sqrt
#align nat.le_sqrt' Nat.le_sqrt'

theorem sqrt_lt {m n : ℕ} : sqrt m < n ↔ m < n * n :=
  lt_iff_lt_of_le_iff_le le_sqrt
#align nat.sqrt_lt Nat.sqrt_lt

theorem sqrt_lt' {m n : ℕ} : sqrt m < n ↔ m < n ^ 2 :=
  lt_iff_lt_of_le_iff_le le_sqrt'
#align nat.sqrt_lt' Nat.sqrt_lt'

theorem sqrt_le_self (n : ℕ) : sqrt n ≤ n :=
  le_trans (le_mul_self _) (sqrt_le n)
#align nat.sqrt_le_self Nat.sqrt_le_self

theorem sqrt_le_sqrt {m n : ℕ} (h : m ≤ n) : sqrt m ≤ sqrt n :=
  le_sqrt.2 (le_trans (sqrt_le _) h)
#align nat.sqrt_le_sqrt Nat.sqrt_le_sqrt

@[simp]
theorem sqrt_zero : sqrt 0 = 0 := rfl
#align nat.sqrt_zero Nat.sqrt_zero

theorem sqrt_eq_zero {n : ℕ} : sqrt n = 0 ↔ n = 0 :=
  ⟨fun h =>
    Nat.eq_zero_of_le_zero <| le_of_lt_succ <| (@sqrt_lt n 1).1 <| by rw [h]; exact by decide, by
    rintro rfl
    simp⟩
#align nat.sqrt_eq_zero Nat.sqrt_eq_zero

theorem eq_sqrt {n q} : q = sqrt n ↔ q * q ≤ n ∧ n < (q + 1) * (q + 1) :=
  ⟨fun e => e.symm ▸ sqrt_IsSqrt n, fun ⟨h₁, h₂⟩ =>
    le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩
#align nat.eq_sqrt Nat.eq_sqrt

theorem eq_sqrt' {n q} : q = sqrt n ↔ q ^ 2 ≤ n ∧ n < (q + 1) ^ 2 := by
  simpa only [pow_two] using eq_sqrt
#align nat.eq_sqrt' Nat.eq_sqrt'

theorem le_three_of_sqrt_eq_one {n : ℕ} (h : sqrt n = 1) : n ≤ 3 :=
  le_of_lt_succ <| (@sqrt_lt n 2).1 <| by rw [h]; exact by decide
#align nat.le_three_of_sqrt_eq_one Nat.le_three_of_sqrt_eq_one

theorem sqrt_lt_self {n : ℕ} (h : 1 < n) : sqrt n < n :=
  sqrt_lt.2 <| by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); rwa [mul_one] at this
#align nat.sqrt_lt_self Nat.sqrt_lt_self

theorem sqrt_pos {n : ℕ} : 0 < sqrt n ↔ 0 < n :=
  le_sqrt
#align nat.sqrt_pos Nat.sqrt_pos

theorem sqrt_add_eq (n : ℕ) {a : ℕ} (h : a ≤ n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <|
      sqrt_lt.2 <| by
        rw [succ_mul, mul_succ, add_succ, add_assoc];
          exact lt_succ_of_le (Nat.add_le_add_left h _))
    (le_sqrt.2 <| Nat.le_add_right _ _)
#align nat.sqrt_add_eq Nat.sqrt_add_eq

theorem sqrt_add_eq' (n : ℕ) {a : ℕ} (h : a ≤ n + n) : sqrt (n ^ 2 + a) = n :=
  (congr_arg (fun i => sqrt (i + a)) (sq n)).trans (sqrt_add_eq n h)
#align nat.sqrt_add_eq' Nat.sqrt_add_eq'

theorem sqrt_eq (n : ℕ) : sqrt (n * n) = n :=
  sqrt_add_eq n (zero_le _)
#align nat.sqrt_eq Nat.sqrt_eq

theorem sqrt_eq' (n : ℕ) : sqrt (n ^ 2) = n :=
  sqrt_add_eq' n (zero_le _)
#align nat.sqrt_eq' Nat.sqrt_eq'

@[simp]
theorem sqrt_one : sqrt 1 = 1 :=
  sqrt_eq 1
#align nat.sqrt_one Nat.sqrt_one

theorem sqrt_succ_le_succ_sqrt (n : ℕ) : sqrt n.succ ≤ n.sqrt.succ :=
  le_of_lt_succ <|
    sqrt_lt.2 <|
      lt_succ_of_le <|
        succ_le_succ <|
          le_trans (sqrt_le_add n) <|
            add_le_add_right
              (by refine' add_le_add (Nat.mul_le_mul_right _ _) _ <;> exact Nat.le_add_right _ 2) _
#align nat.sqrt_succ_le_succ_sqrt Nat.sqrt_succ_le_succ_sqrt

theorem exists_mul_self (x : ℕ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq], fun h => ⟨sqrt x, h⟩⟩
#align nat.exists_mul_self Nat.exists_mul_self

theorem exists_mul_self' (x : ℕ) : (∃ n, n ^ 2 = x) ↔ sqrt x ^ 2 = x := by
  simpa only [pow_two] using exists_mul_self x
#align nat.exists_mul_self' Nat.exists_mul_self'

theorem sqrt_mul_sqrt_lt_succ (n : ℕ) : sqrt n * sqrt n < n + 1 :=
  lt_succ_iff.mpr (sqrt_le _)
#align nat.sqrt_mul_sqrt_lt_succ Nat.sqrt_mul_sqrt_lt_succ

theorem sqrt_mul_sqrt_lt_succ' (n : ℕ) : sqrt n ^ 2 < n + 1 :=
  lt_succ_iff.mpr (sqrt_le' _)
#align nat.sqrt_mul_sqrt_lt_succ' Nat.sqrt_mul_sqrt_lt_succ'

theorem succ_le_succ_sqrt (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt _)
#align nat.succ_le_succ_sqrt Nat.succ_le_succ_sqrt

theorem succ_le_succ_sqrt' (n : ℕ) : n + 1 ≤ (sqrt n + 1) ^ 2 :=
  le_of_pred_lt (lt_succ_sqrt' _)
#align nat.succ_le_succ_sqrt' Nat.succ_le_succ_sqrt'

/-- There are no perfect squares strictly between m² and (m+1)² -/
theorem not_exists_sq {n m : ℕ} (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ t, t * t = n :=
  by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.mpr hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.mpr hr
  exact (not_lt_of_ge <| le_of_lt_succ h2) h1
#align nat.not_exists_sq Nat.not_exists_sq

theorem not_exists_sq' {n m : ℕ} (hl : m ^ 2 < n) (hr : n < (m + 1) ^ 2) : ¬∃ t, t ^ 2 = n := by
  simpa only [pow_two] using
    not_exists_sq (by simpa only [pow_two] using hl) (by simpa only [pow_two] using hr)
#align nat.not_exists_sq' Nat.not_exists_sq'

end Nat
