/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # Lemmas for the `algebra` tactic.

-/

open Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Algebra

section ring

variable {R A : Type*} [sR : CommRing R] [sA : CommRing A] [sAlg : Algebra R A]

theorem neg_smul_one {r s : R} (h : -r = s) :
    -(r • (1 : A)) = s • 1 := by
  simp [← h]

theorem neg_pow_mul (x : A) (e : ℕ) {b c : A} (h : -b = c) :
    -(x ^ e * b) = x ^ e * c := by
  simp [← h]

theorem neg_add {a b c d : A} (ha : -a = c) (hb : -b = d) :
    -(a + b) = c + d := by
  simp [← ha, hb, add_comm]

theorem sub_eq_add_neg' {a b c d : A} (hc : -b = c) (hd : a + c = d) :
    a - b = d := by
  subst_vars
  exact sub_eq_add_neg a b

theorem isInt_negOfNat_eq {a : A} {lit : ℕ} (h : IsInt a (Int.negOfNat lit)) :
    a = (Int.rawCast (Int.negOfNat lit) + 0 : R) • (1 : A) + 0 := by
  simp [h.out, ← Algebra.algebraMap_eq_smul_one]

theorem eval_neg {a a' b : A} (ha : a = a') (hb : -a' = b) :
    -a = b := by
  grind

theorem eval_sub {a b a' b' c : A} (ha : a = a') (hb : b = b') (hc : a' - b' = c) :
    a - b = c := by
  grind

end ring

section semifield

variable {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]

theorem isNNRat_eq_rawCast {a : A} {n d : ℕ} (h : IsNNRat a n d) :
    a = (NNRat.rawCast n d + 0 : R) • 1 + 0 := by
  simp [Mathlib.Tactic.Ring.cast_nnrat h, ← Algebra.algebraMap_eq_smul_one]

end semifield

section field

variable {R A : Type*} [Field R] [Field A] [Algebra R A]

theorem isRat_eq_rawCast {a : A} {n d : ℕ} (h : IsRat a (.negOfNat n) d) :
    a = (Rat.rawCast (.negOfNat n) d + 0 : R) • 1 + 0 := by
  simp [Mathlib.Tactic.Ring.cast_rat h, ← Algebra.algebraMap_eq_smul_one]

end field

variable {R A : Type*} [sR : CommSemiring R] [sA : CommSemiring A] [sAlg : Algebra R A]

theorem add_overlap_nonzero {a₁ a₂ b₁ b₂ c₁ c₂ : R} (h₁ : a₁ + b₁ = c₁) (h₂ : a₂ + b₂ = c₂) :
    a₁ + a₂ + (b₁ + b₂) = c₁ + c₂ := by
  rw [← h₁, ← h₂, add_assoc, add_assoc, add_left_comm a₂]

theorem add_overlap_zero {a₁ a₂ b₁ b₂ c₂ : R}
    (h₁ : IsNat (a₁ + b₁) 0) (h₂ : a₂ + b₂ = c₂) :
    a₁ + a₂ + (b₁ + b₂) = c₂ := by
  rw [add_comm a₁, add_assoc, ← add_assoc a₁, h₁.out]
  simp [h₂]

theorem add_eq_of_eq_eq {a₁ a₂ b₁ b₂ : A}
    (ha : a₁ = b₁) (hb : a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  rfl

omit sA in
theorem eq_trans_trans {e₁ e₂ a b : A}
    (ha : e₁ = a) (hb : e₂ = b) (hab : a = b) :
    e₁ = e₂ := by
  subst_vars
  rfl

theorem mul_eq_mul_of_eq {c a b : A}
    (h : a = b) :
    c * a = c * b := by
  simp [h]

section Nat

variable {n d : ℕ}

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp
end Nat

theorem mul_pow_add_overlap_zero {b₁ b₂ x : A} {e : ℕ}
    (h : IsNat (b₁ + b₂) 0) :
    IsNat (x ^ e * b₁ + x ^ e * b₂) 0 := by
  refine ⟨?_⟩
  simp [← mul_add, h.out]

theorem smul_add_left_zero {r s : R} (h : r + s = 0) :
    IsNat (r • 1 + s • 1 : A) 0 := by
  refine ⟨?_⟩
  simp [← add_smul, h]

theorem smul_add_smul_same {r s t : R} {a b : A} (ha : a = b) (ht : r + s = t) :
    r • a + s • b = t • a := by
  rw [ha, ← add_smul, ht]

theorem smul_congr {r r' : R} {a a' : A} {ef : A} (hr : r = r') (ha : a = a') (hf : r' • a' = ef) :
    r • a = ef := by
  rw [hr, ha, hf]

theorem eval_smul_eq {e : A} {r : R} {a : A} {ef : A}
    (he : e = r • a) (hf : r • a = ef) :
    e = ef := by
  rw [he, hf]

theorem mul_pow_add_overlap_nonzero {x : A} {e : ℕ} {b₁ b₂ c : A}
    (h : b₁ + b₂ = c) :
    x ^ e * b₁ + x ^ e * b₂ = x ^ e * c := by
  rw [← mul_add, h]

theorem add_add_add_comm {a₁ a₂ b₁ b₂ c : A}
    (h : a₂ + (b₁ + b₂) = c) :
    a₁ + a₂ + (b₁ + b₂) = a₁ + c := by
  rw [add_assoc, h]

theorem add_add_add_comm' {a₁ a₂ b₁ b₂ c : A}
    (h : (a₁ + a₂) + b₂ = c) :
    a₁ + a₂ + (b₁ + b₂) = b₁ + c := by
  subst_vars
  ring

theorem isNat_zero_eq {a : A} (h : IsNat a 0) : a = 0 := by
  have := h.out
  simp [this]

theorem pow_eq_pow_mul_smul_one {a : A} {b : ℕ} :
    a ^ b = (a + 0) ^ b * (Nat.rawCast 1 + 0 : R) • (1 : A) := by
  simp

theorem pow_eq_pow_mul_smul_one_add_zero {a : A} {b : ℕ} :
    a ^ b = a ^ b * (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  simp

theorem smul_one_pow {r r' : R} {b : ℕ}
    (h : r ^ (b + 0) = r') :
    (r • (1 : A)) ^ b = r' • 1 := by
  simp [smul_pow, ← h]

theorem pow_mul_pow {x : A} {e e' : ℕ} {b c : A} {n : ℕ}
    (he : e * n = e') (hb : b ^ n = c) :
    (x ^ e * b) ^ n = x ^ e' * c := by
  subst_vars
  simp [mul_pow, ← pow_mul]

theorem pow_even {a b c : A} {m : ℕ}
    (hb : a ^ m = b) (hc : b * b = c) :
    a ^ (m+m) = c := by
  subst_vars
  exact pow_add a m m

theorem pow_odd {a b c d : A} {m : ℕ}
    (hb : a ^ m = b) (hc : b * b = c) (hd : c * a = d) :
    a ^ (m+m+1) = d := by
  subst_vars
  simp [pow_add]

theorem pow_rawCast_one {a : A} :
    a ^ Nat.rawCast (nat_lit 1) = a := by
  simp

theorem zero_pow_pos {b : ℕ} (h : 0 < b) :
    (0 : A) ^ b = 0 := by
  rw [zero_pow]
  exact Nat.ne_zero_of_lt h

theorem pow_add_zero {a c : A} {b : ℕ}
    (h : a ^ b = c) :
    (a + 0) ^ b = c + 0 := by
  subst_vars
  simp

theorem pow_factored {a d e : A} {b e' k : ℕ}
    (hb : b = e' * k) (hd : a ^ e' = d) (he : d ^ k = e) :
    a ^ b = e := by
  subst_vars
  rw [pow_mul]

theorem pow_zero_eq {a : A} :
    a ^ 0 = (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  simp

theorem pow_add {a c₁ c₂ d : A} {b₁ b₂ : ℕ}
    (hc₁ : a ^ b₁ = c₁) (hc₂ : a ^ b₂ = c₂) (hd : c₁ * c₂ = d) :
    a ^ (b₁ + b₂) = d := by
  subst_vars
  rw [_root_.pow_add]

theorem atom_eq_pow_one_mul_smul_one_add_zero {a : A} :
    a = a ^ Nat.rawCast 1 * (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  simp

theorem atom_eq_pow_one_mul_smul_one_add_zero' {a e : A}
    (h : a = e) :
    a = e ^ Nat.rawCast 1 * (Nat.rawCast 1 + 0 : R) • (1 : A) + 0 := by
  subst_vars
  simp

theorem eval_add {a b a' b' c : A}
    (ha : a = a') (hb : b = b') (hc : a' + b' = c) :
    a + b = c := by
  subst_vars
  rfl

theorem eval_mul {a b a' b' c : A}
    (ha : a = a') (hb : b = b') (hc : a' * b' = c) :
    a * b = c := by
  subst_vars
  rfl

theorem eval_pow {a a' c : A} {b b' : ℕ}
    (ha : a = a') (hb : b = b') (hc : a' ^ b' = c) :
    a ^ b = c := by
  subst_vars
  rfl

theorem smul_one_eq_zero {r : R} (h : r = 0) :
    r • (1 : A) = 0 := by
  simp [h]

theorem add_eq_zero {a b : A} (ha : a = 0) (hb : b = 0) :
    a + b = 0 := by
  simp [ha, hb]

theorem smul_one_eq_smul_one' {r s : R} (h : r = s) :
    r • (1 : A) = s • 1 := by
  simp [h]

theorem add_eq_of_zero_add {a₁ a₂ b₁ b₂ : A}
    (ha₁ : a₁ = 0) (ha₂ : a₂ = b₁ + b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

theorem add_eq_of_add_zero {a₁ a₂ b₁ b₂ : A}
    (hb₁ : b₁ = 0) (ha : a₁ + a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

theorem smul_smul_one {r s t : R}
    (h : r * s = t) :
    r • s • (1 : A) = t • 1 := by
  subst_vars
  rw [mul_smul]

theorem smul_mul_assoc {r : R} {x : A} {e : ℕ} {b c : A}
    (h : r • b = c) :
    r • (x ^ e * b) = x ^ e * c := by
  subst_vars
  rw [mul_smul_comm]

theorem smul_add {r : R} {a b c d : A}
    (ha : r • a = c) (hb : r • b = d) :
    r • (a + b) = c + d := by
  subst_vars
  rw [_root_.smul_add]

theorem smul_one_mul_smul_one {r s t : R}
    (h : r * s = t) :
    r • (1 : A) * s • 1 = t • 1 := by
  subst_vars
  rw [smul_mul_smul, mul_one]

theorem pow_mul_mul_smul_one {x : A} {e : ℕ} {b d : A} {r : R}
    (h : b * (r • 1) = d) :
    x ^ e * b * r • 1 = x ^ e * d := by
  subst_vars
  ring

theorem smul_one_mul_pow_mul {r : R} {x : A} {e : ℕ} {b c : A}
    (h : r • 1 * b = c) :
    r • 1 * (x ^ e * b) = x ^ e * c := by
  subst_vars
  ring

theorem pow_mul_mul_pow_mul {x : A} {ea eb e : ℕ} {b₁ b₂ c : A}
    (pe : ea + eb = e) (pc : b₁ * b₂ = c) :
    x ^ ea * b₁ * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars
  ring

theorem pow_mul_mul_assoc {x xb : A} {ea eb : ℕ} {b₁ b c : A}
    (pc : b₁ * (xb ^ eb * b) = c) :
    x ^ ea * b₁ * (xb ^ eb * b) = x ^ ea * c := by
  subst_vars
  ring

theorem mul_pow_mul_assoc {xa xb : A} {ea eb : ℕ} {b₁ b c : A}
    (pc : xa ^ ea * b₁ * b = c) :
    xa ^ ea * b₁ * (xb ^ eb * b) = xb ^ eb * c := by
  subst_vars
  ring

theorem mul_add_of_add {a a₁ b c₁ c₂ c : A}
    (pb₁' : a * a₁ = c₁) (pt : a * b = c₂) (pd : c₁ + 0 + c₂ = c) :
    a * (a₁ + b) = c := by
  subst_vars
  ring

theorem add_mul_of_add {a₁ a₂ b c₁ c₂ c : A}
    (pc₁ : a₁ * b = c₁) (pc₂ : a₂ * b = c₂) (pd : c₁ + c₂ = c) :
    (a₁ + a₂) * b = c := by
  subst_vars
  ring

end Mathlib.Tactic.Algebra
