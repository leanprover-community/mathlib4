/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

#align_import linear_algebra.matrix.zpow from "leanprover-community/mathlib"@"03fda9112aa6708947da13944a19310684bfdfcb"

/-!
# Integer powers of square matrices

In this file, we define integer power of matrices, relying on
the nonsingular inverse definition for negative powers.

## Implementation details

The main definition is a direct recursive call on the integer inductive type,
as provided by the `DivInvMonoid.Pow` default implementation.
The lemma names are taken from `Algebra.group_with_zero.power`.

## Tags

matrix inverse, matrix powers
-/


open Matrix

namespace Matrix

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

local notation "M" => Matrix n' n' R

noncomputable instance : DivInvMonoid M :=
  { show Monoid M by infer_instance, show Inv M by infer_instance with }
                     -- 🎉 no goals
                                                   -- 🎉 no goals

section NatPow

@[simp]
theorem inv_pow' (A : M) (n : ℕ) : A⁻¹ ^ n = (A ^ n)⁻¹ := by
  induction' n with n ih
  -- ⊢ A⁻¹ ^ Nat.zero = (A ^ Nat.zero)⁻¹
  · simp
    -- 🎉 no goals
  · rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']
    -- 🎉 no goals
#align matrix.inv_pow' Matrix.inv_pow'

theorem pow_sub' (A : M) {m n : ℕ} (ha : IsUnit A.det) (h : n ≤ m) :
    A ^ (m - n) = A ^ m * (A ^ n)⁻¹ := by
  rw [← tsub_add_cancel_of_le h, pow_add, Matrix.mul_assoc, mul_nonsing_inv,
    tsub_add_cancel_of_le h, Matrix.mul_one]
  simpa using ha.pow n
  -- 🎉 no goals
#align matrix.pow_sub' Matrix.pow_sub'

theorem pow_inv_comm' (A : M) (m n : ℕ) : A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m := by
  induction' n with n IH generalizing m
  -- ⊢ A⁻¹ ^ m * A ^ Nat.zero = A ^ Nat.zero * A⁻¹ ^ m
  · simp
    -- 🎉 no goals
  cases' m with m m
  -- ⊢ A⁻¹ ^ Nat.zero * A ^ Nat.succ n = A ^ Nat.succ n * A⁻¹ ^ Nat.zero
  · simp
    -- 🎉 no goals
  rcases nonsing_inv_cancel_or_zero A with (⟨h, h'⟩ | h)
  -- ⊢ A⁻¹ ^ Nat.succ m * A ^ Nat.succ n = A ^ Nat.succ n * A⁻¹ ^ Nat.succ m
  · simp only [Nat.succ_eq_add_one]
    -- ⊢ A⁻¹ ^ (m + 1) * A ^ (n + 1) = A ^ (n + 1) * A⁻¹ ^ (m + 1)
    calc
       A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
        simp only [pow_succ' A⁻¹, pow_succ A, Matrix.mul_assoc]
      _ = A ^ n * A⁻¹ ^ m := by simp only [h, Matrix.mul_one, Matrix.one_mul, IH m]
      _ = A ^ n * (A * A⁻¹) * A⁻¹ ^ m := by simp only [h', Matrix.mul_one, Matrix.one_mul]
      _ = A ^ (n + 1) * A⁻¹ ^ (m + 1) := by
        simp only [pow_succ' A, pow_succ A⁻¹, Matrix.mul_assoc]
  · simp [h]
    -- 🎉 no goals
#align matrix.pow_inv_comm' Matrix.pow_inv_comm'

end NatPow

section ZPow

open Int

@[simp]
theorem one_zpow : ∀ n : ℤ, (1 : M) ^ n = 1
  | (n : ℕ) => by rw [zpow_ofNat, one_pow]
                  -- 🎉 no goals
  | -[n+1] => by rw [zpow_negSucc, one_pow, inv_one]
                 -- 🎉 no goals
#align matrix.one_zpow Matrix.one_zpow

theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : M) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_ofNat, zero_pow]
    -- ⊢ 0 < n
    refine' lt_of_le_of_ne n.zero_le (Ne.symm _)
    -- ⊢ n ≠ 0
    simpa using h
    -- 🎉 no goals
  | -[n+1], _ => by simp [zero_pow n.zero_lt_succ]
                    -- 🎉 no goals
#align matrix.zero_zpow Matrix.zero_zpow

theorem zero_zpow_eq (n : ℤ) : (0 : M) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  -- ⊢ 0 ^ n = 1
  · rw [h, zpow_zero]
    -- 🎉 no goals
  · rw [zero_zpow _ h]
    -- 🎉 no goals
#align matrix.zero_zpow_eq Matrix.zero_zpow_eq

theorem inv_zpow (A : M) : ∀ n : ℤ, A⁻¹ ^ n = (A ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_ofNat, zpow_ofNat, inv_pow']
                  -- 🎉 no goals
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, inv_pow']
                 -- 🎉 no goals
#align matrix.inv_zpow Matrix.inv_zpow

@[simp]
theorem zpow_neg_one (A : M) : A ^ (-1 : ℤ) = A⁻¹ := by
  convert DivInvMonoid.zpow_neg' 0 A
  -- ⊢ A = DivInvMonoid.zpow (↑(Nat.succ 0)) A
  simp only [zpow_one, Int.ofNat_zero, Int.ofNat_succ, zpow_eq_pow, zero_add]
  -- 🎉 no goals
#align matrix.zpow_neg_one Matrix.zpow_neg_one

theorem zpow_coe_nat (A : M) (n : ℕ) : A ^ (n : ℤ) = A ^ n :=
  zpow_ofNat _ _
#align matrix.zpow_coe_nat Matrix.zpow_coe_nat

@[simp]
theorem zpow_neg_coe_nat (A : M) (n : ℕ) : A ^ (-n : ℤ) = (A ^ n)⁻¹ := by
  cases n
  -- ⊢ A ^ (-↑Nat.zero) = (A ^ Nat.zero)⁻¹
  · simp
    -- 🎉 no goals
  · exact DivInvMonoid.zpow_neg' _ _
    -- 🎉 no goals
#align matrix.zpow_neg_coe_nat Matrix.zpow_neg_coe_nat

theorem _root_.IsUnit.det_zpow {A : M} (h : IsUnit A.det) (n : ℤ) : IsUnit (A ^ n).det := by
  cases' n with n n
  -- ⊢ IsUnit (det (A ^ ofNat n))
  · simpa using h.pow n
    -- 🎉 no goals
  · simpa using h.pow n.succ
    -- 🎉 no goals
#align is_unit.det_zpow IsUnit.det_zpow

theorem isUnit_det_zpow_iff {A : M} {z : ℤ} : IsUnit (A ^ z).det ↔ IsUnit A.det ∨ z = 0 := by
  induction' z using Int.induction_on with z _ z _
  · simp
    -- 🎉 no goals
  · rw [← Int.ofNat_succ, zpow_ofNat, det_pow, isUnit_pow_succ_iff, ← Int.ofNat_zero, Int.ofNat_inj]
    -- ⊢ IsUnit (det A) ↔ IsUnit (det A) ∨ Nat.succ z = 0
    simp
    -- 🎉 no goals
  · rw [← neg_add', ← Int.ofNat_succ, zpow_neg_coe_nat, isUnit_nonsing_inv_det_iff, det_pow,
      isUnit_pow_succ_iff, neg_eq_zero, ← Int.ofNat_zero, Int.ofNat_inj]
    simp
    -- 🎉 no goals
#align matrix.is_unit_det_zpow_iff Matrix.isUnit_det_zpow_iff

theorem zpow_neg {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (-n) = (A ^ n)⁻¹
  | (n : ℕ) => zpow_neg_coe_nat _ _
  | -[n+1] => by
    rw [zpow_negSucc, neg_negSucc, zpow_ofNat, nonsing_inv_nonsing_inv]
    -- ⊢ IsUnit (det (A ^ (n + 1)))
    rw [det_pow]
    -- ⊢ IsUnit (det A ^ (n + 1))
    exact h.pow _
    -- 🎉 no goals
#align matrix.zpow_neg Matrix.zpow_neg

theorem inv_zpow' {A : M} (h : IsUnit A.det) (n : ℤ) : A⁻¹ ^ n = A ^ (-n) := by
  rw [zpow_neg h, inv_zpow]
  -- 🎉 no goals
#align matrix.inv_zpow' Matrix.inv_zpow'

theorem zpow_add_one {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (n + 1) = A ^ n * A
  | (n : ℕ) => by simp only [← Nat.cast_succ, pow_succ', zpow_ofNat]
                  -- 🎉 no goals
  | -[n+1] =>
    calc
      A ^ (-(n + 1) + 1 : ℤ) = (A ^ n)⁻¹ := by
        rw [neg_add, neg_add_cancel_right, zpow_neg h, zpow_ofNat]
        -- 🎉 no goals
      _ = (A * A ^ n)⁻¹ * A := by
        rw [mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ h, Matrix.mul_one]
        -- 🎉 no goals
      _ = A ^ (-(n + 1 : ℤ)) * A := by
        rw [zpow_neg h, ← Int.ofNat_succ, zpow_ofNat, pow_succ]
        -- 🎉 no goals
#align matrix.zpow_add_one Matrix.zpow_add_one

theorem zpow_sub_one {A : M} (h : IsUnit A.det) (n : ℤ) : A ^ (n - 1) = A ^ n * A⁻¹ :=
  calc
    A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ := by
      rw [mul_assoc, mul_nonsing_inv _ h, mul_one]
      -- 🎉 no goals
    _ = A ^ n * A⁻¹ := by rw [← zpow_add_one h, sub_add_cancel]
                          -- 🎉 no goals
#align matrix.zpow_sub_one Matrix.zpow_sub_one

theorem zpow_add {A : M} (ha : IsUnit A.det) (m n : ℤ) : A ^ (m + n) = A ^ m * A ^ n := by
  induction n using Int.induction_on with
  | hz => simp
  | hp n ihn => simp only [← add_assoc, zpow_add_one ha, ihn, mul_assoc]
  | hn n ihn => rw [zpow_sub_one ha, ← mul_assoc, ← ihn, ← zpow_sub_one ha, add_sub_assoc]
#align matrix.zpow_add Matrix.zpow_add

theorem zpow_add_of_nonpos {A : M} {m n : ℤ} (hm : m ≤ 0) (hn : n ≤ 0) :
    A ^ (m + n) = A ^ m * A ^ n := by
  rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
  -- ⊢ A ^ (m + n) = A ^ m * A ^ n
  · exact zpow_add (isUnit_det_of_left_inverse h) m n
    -- 🎉 no goals
  · obtain ⟨k, rfl⟩ := exists_eq_neg_ofNat hm
    -- ⊢ A ^ (-↑k + n) = A ^ (-↑k) * A ^ n
    obtain ⟨l, rfl⟩ := exists_eq_neg_ofNat hn
    -- ⊢ A ^ (-↑k + -↑l) = A ^ (-↑k) * A ^ (-↑l)
    simp_rw [← neg_add, ← Int.ofNat_add, zpow_neg_coe_nat, ← inv_pow', h, pow_add]
    -- 🎉 no goals
#align matrix.zpow_add_of_nonpos Matrix.zpow_add_of_nonpos

theorem zpow_add_of_nonneg {A : M} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    A ^ (m + n) = A ^ m * A ^ n := by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  -- ⊢ A ^ (↑k + n) = A ^ ↑k * A ^ n
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  -- ⊢ A ^ (↑k + ↑l) = A ^ ↑k * A ^ ↑l
  rw [← Int.ofNat_add, zpow_ofNat, zpow_ofNat, zpow_ofNat, pow_add]
  -- 🎉 no goals
#align matrix.zpow_add_of_nonneg Matrix.zpow_add_of_nonneg

theorem zpow_one_add {A : M} (h : IsUnit A.det) (i : ℤ) : A ^ (1 + i) = A * A ^ i := by
  rw [zpow_add h, zpow_one]
  -- 🎉 no goals
#align matrix.zpow_one_add Matrix.zpow_one_add

theorem SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det)
    (h : SemiconjBy A X Y) : ∀ m : ℤ, SemiconjBy A (X ^ m) (Y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
                  -- 🎉 no goals
  | -[n+1] => by
    have hx' : IsUnit (X ^ n.succ).det := by
      rw [det_pow]
      exact hx.pow n.succ
    have hy' : IsUnit (Y ^ n.succ).det := by
      rw [det_pow]
      exact hy.pow n.succ
    rw [zpow_negSucc, zpow_negSucc, nonsing_inv_apply _ hx', nonsing_inv_apply _ hy', SemiconjBy]
    -- ⊢ A * ↑(IsUnit.unit hx')⁻¹ • adjugate (X ^ Nat.succ n) = ↑(IsUnit.unit hy')⁻¹  …
    refine' (isRegular_of_isLeftRegular_det hy'.isRegular.left).left _
    -- ⊢ (fun x => Y ^ Nat.succ n * x) (A * ↑(IsUnit.unit hx')⁻¹ • adjugate (X ^ Nat. …
    dsimp only
    -- ⊢ Y ^ Nat.succ n * (A * ↑(IsUnit.unit hx')⁻¹ • adjugate (X ^ Nat.succ n)) = Y  …
    rw [← mul_assoc, ← (h.pow_right n.succ).eq, mul_assoc, mul_smul,
      mul_adjugate, ← Matrix.mul_assoc,
      mul_smul (Y ^ _) (↑hy'.unit⁻¹ : R), mul_adjugate, smul_smul, smul_smul, hx'.val_inv_mul,
      hy'.val_inv_mul, one_smul, Matrix.mul_one, Matrix.one_mul]
#align matrix.semiconj_by.zpow_right Matrix.SemiconjBy.zpow_right

theorem Commute.zpow_right {A B : M} (h : Commute A B) (m : ℤ) : Commute A (B ^ m) := by
  rcases nonsing_inv_cancel_or_zero B with (⟨hB, _⟩ | hB)
  -- ⊢ Commute A (B ^ m)
  · refine' SemiconjBy.zpow_right _ _ h _ <;> exact isUnit_det_of_left_inverse hB
    -- ⊢ IsUnit (det B)
                                              -- 🎉 no goals
                                              -- 🎉 no goals
  · cases m
    -- ⊢ Commute A (B ^ ofNat a✝)
    · simpa using h.pow_right _
      -- 🎉 no goals
    · simp [← inv_pow', hB]
      -- 🎉 no goals
#align matrix.commute.zpow_right Matrix.Commute.zpow_right

theorem Commute.zpow_left {A B : M} (h : Commute A B) (m : ℤ) : Commute (A ^ m) B :=
  (Commute.zpow_right h.symm m).symm
#align matrix.commute.zpow_left Matrix.Commute.zpow_left

theorem Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : ℤ) : Commute (A ^ m) (B ^ n) :=
  Commute.zpow_right (Commute.zpow_left h _) _
#align matrix.commute.zpow_zpow Matrix.Commute.zpow_zpow

theorem Commute.zpow_self (A : M) (n : ℤ) : Commute (A ^ n) A :=
  Commute.zpow_left (Commute.refl A) _
#align matrix.commute.zpow_self Matrix.Commute.zpow_self

theorem Commute.self_zpow (A : M) (n : ℤ) : Commute A (A ^ n) :=
  Commute.zpow_right (Commute.refl A) _
#align matrix.commute.self_zpow Matrix.Commute.self_zpow

theorem Commute.zpow_zpow_self (A : M) (m n : ℤ) : Commute (A ^ m) (A ^ n) :=
  Commute.zpow_zpow (Commute.refl A) _ _
#align matrix.commute.zpow_zpow_self Matrix.Commute.zpow_zpow_self

set_option linter.deprecated false in
theorem zpow_bit0 (A : M) (n : ℤ) : A ^ bit0 n = A ^ n * A ^ n := by
  cases' le_total 0 n with nonneg nonpos
  -- ⊢ A ^ bit0 n = A ^ n * A ^ n
  · exact zpow_add_of_nonneg nonneg nonneg
    -- 🎉 no goals
  · exact zpow_add_of_nonpos nonpos nonpos
    -- 🎉 no goals
#align matrix.zpow_bit0 Matrix.zpow_bit0

theorem zpow_add_one_of_ne_neg_one {A : M} : ∀ n : ℤ, n ≠ -1 → A ^ (n + 1) = A ^ n * A
  | (n : ℕ), _ => by simp only [pow_succ', ← Nat.cast_succ, zpow_ofNat]
                     -- 🎉 no goals
  | -1, h => absurd rfl h
  | -((n : ℕ) + 2), _ => by
    rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
    -- ⊢ A ^ (-(↑n + 2) + 1) = A ^ (-(↑n + 2)) * A
    · apply zpow_add_one (isUnit_det_of_left_inverse h)
      -- 🎉 no goals
    · show A ^ (-((n + 1 : ℕ) : ℤ)) = A ^ (-((n + 2 : ℕ) : ℤ)) * A
      -- ⊢ A ^ (-↑(n + 1)) = A ^ (-↑(n + 2)) * A
      simp_rw [zpow_neg_coe_nat, ← inv_pow', h, zero_pow Nat.succ_pos', zero_mul]
      -- 🎉 no goals
#align matrix.zpow_add_one_of_ne_neg_one Matrix.zpow_add_one_of_ne_neg_one

set_option linter.deprecated false in
theorem zpow_bit1 (A : M) (n : ℤ) : A ^ bit1 n = A ^ n * A ^ n * A := by
  rw [bit1, zpow_add_one_of_ne_neg_one, zpow_bit0]
  -- ⊢ bit0 n ≠ -1
  intro h
  -- ⊢ False
  simpa using congr_arg bodd h
  -- 🎉 no goals
#align matrix.zpow_bit1 Matrix.zpow_bit1

theorem zpow_mul (A : M) (h : IsUnit A.det) : ∀ m n : ℤ, A ^ (m * n) = (A ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by rw [zpow_ofNat, zpow_ofNat, ← pow_mul, ← zpow_ofNat, Int.ofNat_mul]
                           -- 🎉 no goals
  | (m : ℕ), -[n+1] => by
    rw [zpow_ofNat, zpow_negSucc, ← pow_mul, ofNat_mul_negSucc, zpow_neg_coe_nat]
    -- 🎉 no goals
  | -[m+1], (n : ℕ) => by
    rw [zpow_ofNat, zpow_negSucc, ← inv_pow', ← pow_mul, negSucc_mul_ofNat, zpow_neg_coe_nat,
        inv_pow']
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, negSucc_mul_negSucc, ← Int.ofNat_mul, zpow_ofNat, inv_pow', ←
      pow_mul, nonsing_inv_nonsing_inv]
    rw [det_pow]
    -- ⊢ IsUnit (det A ^ ((m + 1) * (n + 1)))
    exact h.pow _
    -- 🎉 no goals
#align matrix.zpow_mul Matrix.zpow_mul

theorem zpow_mul' (A : M) (h : IsUnit A.det) (m n : ℤ) : A ^ (m * n) = (A ^ n) ^ m := by
  rw [mul_comm, zpow_mul _ h]
  -- 🎉 no goals
#align matrix.zpow_mul' Matrix.zpow_mul'


@[simp, norm_cast]
theorem coe_units_zpow (u : Mˣ) : ∀ n : ℤ, ((u ^ n : Mˣ) : M) = (u : M) ^ n
  | (n : ℕ) => by rw [_root_.zpow_coe_nat, zpow_ofNat, Units.val_pow_eq_pow_val]
                  -- 🎉 no goals
  | -[k+1] => by
    rw [zpow_negSucc, zpow_negSucc, ← inv_pow, u⁻¹.val_pow_eq_pow_val, ← inv_pow', coe_units_inv]
    -- 🎉 no goals
#align matrix.coe_units_zpow Matrix.coe_units_zpow

theorem zpow_ne_zero_of_isUnit_det [Nonempty n'] [Nontrivial R] {A : M} (ha : IsUnit A.det)
    (z : ℤ) : A ^ z ≠ 0 := by
  have := ha.det_zpow z
  -- ⊢ A ^ z ≠ 0
  contrapose! this
  -- ⊢ ¬IsUnit (det (A ^ z))
  rw [this, det_zero ‹_›]
  -- ⊢ ¬IsUnit 0
  exact not_isUnit_zero
  -- 🎉 no goals
#align matrix.zpow_ne_zero_of_is_unit_det Matrix.zpow_ne_zero_of_isUnit_det

theorem zpow_sub {A : M} (ha : IsUnit A.det) (z1 z2 : ℤ) : A ^ (z1 - z2) = A ^ z1 / A ^ z2 := by
  rw [sub_eq_add_neg, zpow_add ha, zpow_neg ha, div_eq_mul_inv]
  -- 🎉 no goals
#align matrix.zpow_sub Matrix.zpow_sub

theorem Commute.mul_zpow {A B : M} (h : Commute A B) : ∀ i : ℤ, (A * B) ^ i = A ^ i * B ^ i
  | (n : ℕ) => by simp [h.mul_pow n]
                  -- 🎉 no goals
  | -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, zpow_negSucc, ← mul_inv_rev,
      h.mul_pow n.succ, (h.pow_pow _ _).eq]
#align matrix.commute.mul_zpow Matrix.Commute.mul_zpow

set_option linter.deprecated false in
theorem zpow_bit0' (A : M) (n : ℤ) : A ^ bit0 n = (A * A) ^ n :=
  (zpow_bit0 A n).trans (Commute.mul_zpow (Commute.refl A) n).symm
#align matrix.zpow_bit0' Matrix.zpow_bit0'

set_option linter.deprecated false in
theorem zpow_bit1' (A : M) (n : ℤ) : A ^ bit1 n = (A * A) ^ n * A := by
  rw [zpow_bit1, Commute.mul_zpow (Commute.refl A)]
  -- 🎉 no goals
#align matrix.zpow_bit1' Matrix.zpow_bit1'

theorem zpow_neg_mul_zpow_self (n : ℤ) {A : M} (h : IsUnit A.det) : A ^ (-n) * A ^ n = 1 := by
  rw [zpow_neg h, nonsing_inv_mul _ (h.det_zpow _)]
  -- 🎉 no goals
#align matrix.zpow_neg_mul_zpow_self Matrix.zpow_neg_mul_zpow_self

theorem one_div_pow {A : M} (n : ℕ) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_pow']
                                                                    -- 🎉 no goals
#align matrix.one_div_pow Matrix.one_div_pow

theorem one_div_zpow {A : M} (n : ℤ) : (1 / A) ^ n = 1 / A ^ n := by simp only [one_div, inv_zpow]
                                                                     -- 🎉 no goals
#align matrix.one_div_zpow Matrix.one_div_zpow

@[simp]
theorem transpose_zpow (A : M) : ∀ n : ℤ, (A ^ n)ᵀ = Aᵀ ^ n
  | (n : ℕ) => by rw [zpow_ofNat, zpow_ofNat, transpose_pow]
                  -- 🎉 no goals
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, transpose_nonsing_inv, transpose_pow]
                 -- 🎉 no goals
#align matrix.transpose_zpow Matrix.transpose_zpow

@[simp]
theorem conjTranspose_zpow [StarRing R] (A : M) : ∀ n : ℤ, (A ^ n)ᴴ = Aᴴ ^ n
  | (n : ℕ) => by rw [zpow_ofNat, zpow_ofNat, conjTranspose_pow]
                  -- 🎉 no goals
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, conjTranspose_nonsing_inv, conjTranspose_pow]
                 -- 🎉 no goals
#align matrix.conj_transpose_zpow Matrix.conjTranspose_zpow

end ZPow

end Matrix
