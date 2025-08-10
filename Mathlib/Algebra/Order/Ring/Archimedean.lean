/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# Archimedean classes of a linearly ordered ring

Archimedean classes over a strictly linearly ordered ring form an abelian monoid itself.
Moreover, we show it is a valuation of the ring.
-/

variable {M : Type*} [LinearOrder M]

namespace ArchimedeanClass
section Ring

variable [CommRing M] [IsStrictOrderedRing M]

instance : Zero (ArchimedeanClass M) where
  zero := mk 1

@[simp] theorem mk_one : mk (1 : M) = 0 := rfl

private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : M} (hx : mk x₁ ≤ mk x₂) (hy : mk y₁ ≤ mk y₂) :
    mk (x₁ * y₁) ≤ mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) using 1 <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

/-- Multipilication in `M` transfers to Addition in `ArchimedeanClass M`.
We denote this as an addition instead of multiplication for the following reasons:

* In the ring version of Hahn embedding theorem, `ArchimedeanClassₒ M` naturally becomes
  the additive abelian group for the ring `HahnSeries (ArchimedeanClassₒ M) ℝ`.
* The order we defined on `ArchimedeanClass M` matches the order on `AddValuation`, instead
  of the one on `Valuation`. -/
instance : Add (ArchimedeanClass M) where
  add := Quotient.lift₂ (fun x y ↦ .mk <| x.val * y.val) fun _ _ _ _ hx hy ↦
    (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

@[simp] theorem mk_mul (x y : M) : mk (x * y) = mk x + mk y := rfl

instance : SMul ℕ (ArchimedeanClass M) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

@[simp] theorem mk_pow (n : ℕ) (x : M) : mk (x ^ n) = n • mk x := rfl

instance : AddCommMagma (ArchimedeanClass M) where
  add_comm x y := by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul, mul_comm, mk_mul]

private theorem zero_add' (x : ArchimedeanClass M) : 0 + x = x := by
  induction x with | mk x
  rw [← mk_one, ← mk_mul, one_mul]

private theorem add_assoc' (x y z : ArchimedeanClass M) : x + y + z = x + (y + z) := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]

instance : AddCommMonoid (ArchimedeanClass M) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero x := add_comm x _ ▸ zero_add' x
  nsmul n x := n • x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

instance : IsOrderedAddMonoid (ArchimedeanClass M) where
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul, ← mk_mul]
    exact mk_mul_le_of_le le_rfl h

noncomputable instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass M) where
  top_add' x := by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]

theorem add_left_cancel_of_ne_top {x y z : ArchimedeanClass M} (hx : x ≠ ⊤) (h : x + y = x + z) :
    y = z := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mk_eq_mk] at h
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h
  simp_rw [abs_mul, mul_comm |x|, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul] at hm hn
  refine mk_eq_mk.2 ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩ <;> exact le_of_mul_le_mul_right ‹_› (by simpa using hx)

theorem add_right_cancel_of_ne_top {x y z : ArchimedeanClass M} (hx : x ≠ ⊤) (h : y + x = z + x) :
    y = z := by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h

end Ring

section Field

variable [Field M] [IsStrictOrderedRing M]

instance : Neg (ArchimedeanClass M) where
  neg x := x.lift (fun x ↦ mk x⁻¹) fun x y h ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp_all
    obtain rfl | hy := eq_or_ne y 0
    · simp_all
    have hx' : mk x ≠ ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    simp [← mk_mul, hx, hy]

@[simp] theorem mk_inv (x : M) : mk x⁻¹ = -mk x := rfl

instance : SMul ℤ (ArchimedeanClass M) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [h]

@[simp] theorem mk_zpow (n : ℤ) (x : M) : mk (x ^ n) = n • mk x := rfl

private theorem zsmul_succ' (n : ℕ) (x : ArchimedeanClass M) :
    (n.succ : ℤ) • x = (n : ℤ) • x + x := by
  induction x with | mk x
  rw [← mk_zpow, Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]

noncomputable instance : LinearOrderedAddCommGroupWithTop (ArchimedeanClass M) where
  neg_top := by simp [← mk_zero, ← mk_inv]
  add_neg_cancel x h := by
    induction x with | mk x
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (show x ≠ 0 by simpa using h)]
  zsmul n x := n • x
  zsmul_zero' x := by induction x with | mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := zsmul_succ'
  zsmul_neg' n x := by
    induction x with | mk x
    rw [← mk_zpow, zpow_negSucc, pow_succ, zsmul_succ', mk_inv, mk_mul, ← zpow_natCast, mk_zpow]

end Field
end ArchimedeanClass
