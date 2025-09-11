/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Integer powers of square matrices

In this file, we define integer power of matrices, relying on
the nonsingular inverse definition for negative powers.

## Implementation details

The main definition is a direct recursive call on the integer inductive type,
as provided by the `DivInvMonoid.Pow` default implementation.
The lemma names are taken from `Algebra.GroupWithZero.Power`.

## Tags

matrix inverse, matrix powers
-/


open Matrix

namespace Matrix

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

local notation "M" => Matrix n' n' R

noncomputable instance : DivInvMonoid M :=
  { show Monoid M by infer_instance, show Inv M by infer_instance with }

section NatPow

@[simp]
theorem inv_pow' (A : M) (n : ℕ) : A⁻¹ ^ n = (A ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']

theorem pow_sub' (A : M) {m n : ℕ} (ha : IsUnit A.det) (h : n ≤ m) :
    A ^ (m - n) = A ^ m * (A ^ n)⁻¹ := by
  rw [← tsub_add_cancel_of_le h, pow_add, Matrix.mul_assoc, mul_nonsing_inv,
    tsub_add_cancel_of_le h, Matrix.mul_one]
  simpa using ha.pow n

theorem pow_inv_comm' (A : M) (m n : ℕ) : A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m := by
  induction n generalizing m with
  | zero => simp
  | succ n IH =>
    rcases m with m | m
    · simp
    rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h
    · calc
        A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
          simp only [pow_succ A⁻¹, pow_succ' A, Matrix.mul_assoc]
        _ = A ^ n * A⁻¹ ^ m := by simp only [h, Matrix.mul_one, IH m]
        _ = A ^ n * (A * A⁻¹) * A⁻¹ ^ m := by simp only [h', Matrix.mul_one]
        _ = A ^ (n + 1) * A⁻¹ ^ (m + 1) := by
          simp only [pow_succ A, pow_succ' A⁻¹, Matrix.mul_assoc]
    · simp [h]

end NatPow

section ZPow

open Int

@[simp]
theorem one_zpow : ∀ n : ℤ, (1 : M) ^ n = 1
  | (n : ℕ) => by rw [zpow_natCast, one_pow]
  | -[n+1] => by rw [zpow_negSucc, one_pow, inv_one]

theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : M) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_natCast, zero_pow]
    exact mod_cast h
  | -[n+1], _ => by simp [zero_pow n.succ_ne_zero]

theorem zero_zpow_eq (n : ℤ) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, zpow_zero]
  · rw [zero_zpow _ h]

theorem inv_zpow (A : M) : ∀ n : ℤ, A⁻¹ ^ n = (A ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, inv_pow']
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, inv_pow']

@[simp]
theorem zpow_neg_one (A : M) : A ^ (-1 : ℤ) = A⁻¹ := by
  convert DivInvMonoid.zpow_neg' 0 A
  simp only [zpow_one, Int.ofNat_zero, Int.natCast_succ, zpow_eq_pow, zero_add]

@[simp]
theorem zpow_neg_natCast (A : M) (n : ℕ) : A ^ (-n : ℤ) = (A ^ n)⁻¹ := by
  cases n
  · simp
  · exact DivInvMonoid.zpow_neg' _ _

theorem _root_.IsUnit.det_zpow {A : M} (h : IsUnit A.det) (n : ℤ) : IsUnit (A ^ n).det := by
  rcases n with n | n
  · simpa using h.pow n
  · simpa using h.pow n.succ

theorem isUnit_det_zpow_iff {A : M} {z : ℤ} : IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0 := by
  induction z with
  | zero => simp
  | succ z =>
    rw [← Int.natCast_succ, zpow_natCast, det_pow, isUnit_pow_succ_iff, ← Int.ofNat_zero,
      Int.ofNat_inj]
    simp
  | pred z =>
    rw [← neg_add', ← Int.natCast_succ, zpow_neg_natCast, isUnit_nonsing_inv_det_iff, det_pow,
      isUnit_pow_succ_iff, neg_eq_zero, ← Int.ofNat_zero, Int.ofNat_inj]
    simp

theorem zpow_neg {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (-n) = (A ^ n)⁻¹
  | (n : ℕ) => zpow_neg_natCast _ _
  | -[n+1] => by
    rw [zpow_negSucc, neg_negSucc, zpow_natCast, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _

theorem inv_zpow' {A : M} (h : IsUnit A.det) (n : ℤ) : A⁻¹ ^ n = A ^ (-n) := by
  rw [zpow_neg h, inv_zpow]

theorem zpow_add_one {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (n + 1) = A ^ n * A
  | (n : ℕ) => by simp only [← Nat.cast_succ, pow_succ, zpow_natCast]
  | -[n+1] =>
    calc
      A ^ (-(n + 1) + 1 : ℤ) = (A ^ n)⁻¹ := by
        rw [neg_add, neg_add_cancel_right, zpow_neg h, zpow_natCast]
      _ = (A * A ^ n)⁻¹ * A := by
        rw [mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]
      _ = A ^ (-(n + 1 : ℤ)) * A := by
        rw [zpow_neg h, ← Int.natCast_succ, zpow_natCast, pow_succ']

theorem zpow_sub_one {A : M} (h : IsUnit A.det) (n : ℤ) : A ^ (n - 1) = A ^ n * A⁻¹ :=
  calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc, mul_nonsing_inv _ h, mul_one]
    _ = A ^ n * A⁻¹ := by rw [← zpow_add_one h, sub_add_cancel]

theorem zpow_add {A : M} (ha : IsUnit A.det) (m n : ℤ) : A ^ (m + n) = A ^ m * A ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← add_assoc, zpow_add_one ha, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]

theorem zpow_add_of_nonpos {A : M} {m n : ℤ} (hm : m ≤ 0) (hn : n ≤ 0) :
    A ^ (m + n) = A ^ m * A ^ n := by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
  · exact zpow_add (isUnit_det_of_left_inverse h) m n
  · obtain ⟨k, rfl⟩ := exists_eq_neg_ofNat hm
    obtain ⟨l, rfl⟩ := exists_eq_neg_ofNat hn
    simp_rw [← neg_add, ← Int.natCast_add, zpow_neg_natCast, ← inv_pow', h, pow_add]

theorem zpow_add_of_nonneg {A : M} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    A ^ (m + n) = A ^ m * A ^ n := by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  rw [← Int.natCast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

theorem zpow_one_add {A : M} (h : IsUnit A.det) (i : ℤ) : A ^ (1 + i) = A * A ^ i := by
  rw [zpow_add h, zpow_one]

theorem SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det)
    (h : SemiconjBy A X Y) : ∀ m : ℤ, SemiconjBy A (X ^ m) (Y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
  | -[n+1] => by
    have hx' : IsUnit (X ^ n.succ).det := by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_negSucc, zpow_negSucc, nonsing_inv_apply _ hx', nonsing_inv_apply _ hy', SemiconjBy]
    refine (isRegular_of_isLeftRegular_det hy'.isRegular.left).left ?_
    dsimp only
    rw [← mul_assoc, ← (h.pow_right n.succ).eq, mul_assoc, mul_smul,
      mul_adjugate, ← Matrix.mul_assoc,
      mul_smul (Y ^ _) (↑hy'.unit⁻¹ : R), mul_adjugate, smul_smul, smul_smul, hx'.val_inv_mul,
      hy'.val_inv_mul, one_smul, Matrix.mul_one, Matrix.one_mul]

theorem Commute.zpow_right {A B : M} (h : Commute A B) (m : ℤ) : Commute A (B ^ m) := by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, _⟩ | hB)
  · refine SemiconjBy.zpow_right ?_ ?_ h _ <;> exact isUnit_det_of_left_inverse hB
  · cases m
    · simpa using h.pow_right _
    · simp [← inv_pow', hB]

theorem Commute.zpow_left {A B : M} (h : Commute A B) (m : ℤ) : Commute (A ^ m) B :=
  (Commute.zpow_right h.symm m).symm

theorem Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : ℤ) : Commute (A ^ m) (B ^ n) :=
  Commute.zpow_right (Commute.zpow_left h _) _

theorem Commute.zpow_self (A : M) (n : ℤ) : Commute (A ^ n) A :=
  Commute.zpow_left (Commute.refl A) _

theorem Commute.self_zpow (A : M) (n : ℤ) : Commute A (A ^ n) :=
  Commute.zpow_right (Commute.refl A) _

theorem Commute.zpow_zpow_self (A : M) (m n : ℤ) : Commute (A ^ m) (A ^ n) :=
  Commute.zpow_zpow (Commute.refl A) _ _

theorem zpow_add_one_of_ne_neg_one {A : M} : ∀ n : ℤ, n ≠ -1 → A ^ (n + 1) = A ^ n * A
  | (n : ℕ), _ => by simp only [pow_succ, ← Nat.cast_succ, zpow_natCast]
  | -1, h => absurd rfl h
  | -((n : ℕ) + 2), _ => by
    rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
    · apply zpow_add_one (isUnit_det_of_left_inverse h)
    · change A ^ (-((n + 1 : ℕ) : ℤ)) = A ^ (-((n + 2 : ℕ) : ℤ)) * A
      simp_rw [zpow_neg_natCast, ← inv_pow', h, zero_pow <| Nat.succ_ne_zero _, zero_mul]

theorem zpow_mul (A : M) (h : IsUnit A.det) : ∀ m n : ℤ, A ^ (m * n) = (A ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_natCast, zpow_natCast, ← pow_mul, ← zpow_natCast, Int.natCast_mul]
  | (m : ℕ), -[n+1] => by
    rw [zpow_natCast, zpow_negSucc, ← pow_mul, ofNat_mul_negSucc, zpow_neg_natCast]
  | -[m+1], (n : ℕ) => by
    rw [zpow_natCast, zpow_negSucc, ← inv_pow', ← pow_mul, negSucc_mul_ofNat, zpow_neg_natCast,
        inv_pow']
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, negSucc_mul_negSucc, ← Int.natCast_mul, zpow_natCast, inv_pow',
      ← pow_mul, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _

theorem zpow_mul' (A : M) (h : IsUnit A.det) (m n : ℤ) : A ^ (m * n) = (A ^ n) ^ m := by
  rw [mul_comm, zpow_mul _ h]


@[simp, norm_cast]
theorem coe_units_zpow (u : Mˣ) : ∀ n : ℤ, ((u ^ n : Mˣ) : M) = (u : M) ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
  | -[k+1] => by
    rw [zpow_negSucc, zpow_negSucc, ← inv_pow, u⁻¹.val_pow_eq_pow_val, ← inv_pow', coe_units_inv]

theorem zpow_ne_zero_of_isUnit_det [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det)
    (z : ℤ) : A ^ z ≠ 0 := by
  have := ha.det_zpow z
  contrapose! this
  rw [this, det_zero ‹_›]
  exact not_isUnit_zero

theorem zpow_sub {A : M} (ha : IsUnit A.det) (z1 z2 : ℤ) : A ^ (z1 - z2) = A ^ z1 / A ^ z2 := by
  rw [sub_eq_add_neg, zpow_add ha, zpow_neg ha, div_eq_mul_inv]

theorem Commute.mul_zpow {A B : M} (h : Commute A B) : ∀ i : ℤ, (A * B) ^ i = A ^ i * B ^ i
  | (n : ℕ) => by simp [h.mul_pow n]
  | -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, zpow_negSucc, ← mul_inv_rev,
      h.mul_pow n.succ, (h.pow_pow _ _).eq]

theorem zpow_neg_mul_zpow_self (n : ℤ) {A : M} (h : IsUnit A.det) : A ^ (-n) * A ^ n = 1 := by
  rw [zpow_neg h, nonsing_inv_mul _ (h.det_zpow _)]

theorem one_div_pow {A : M} (n : ℕ) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_pow']

theorem one_div_zpow {A : M} (n : ℤ) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_zpow]

@[simp]
theorem transpose_zpow (A : M) : ∀ n : ℤ, (A ^ n)ᵀ = Aᵀ ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, transpose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, transpose_nonsing_inv, transpose_pow]

@[simp]
theorem conjTranspose_zpow [StarRing R] (A : M) : ∀ n : ℤ, (A ^ n)ᴴ = Aᴴ ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, conjTranspose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, conjTranspose_nonsing_inv, conjTranspose_pow]

theorem IsSymm.zpow {A : M} (h : A.IsSymm) (k : ℤ) :
    (A ^ k).IsSymm := by
  rw [IsSymm, transpose_zpow, h]

end ZPow

end Matrix
