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

The archimedean classes of a linearly ordered ring can be given the structure of an `AddCommMonoid`,
by defining

* `0 = mk 1`
* `mk x + mk y = mk (x * y)`

For a linearly ordered field, we can define a negative as

* `-mk x = mk x⁻¹`

which turns them into a `LinearOrderedAddCommGroupWithTop`.

## Implementation notes

We give Archimedean class an additive structure, rather than a multiplicative one, for the following
reasons:

* In the ring version of Hahn embedding theorem, the subtype `FiniteArchimedeanClass M` of non-top
  elements in `ArchimedeanClass M` naturally becomes the additive abelian group for the ring
  `HahnSeries (FiniteArchimedeanClass M) ℝ`.
* The order we defined on `ArchimedeanClass M` matches the order on `AddValuation`, rather than the
  one on `Valuation`.
-/

variable {M : Type*} [LinearOrder M]

namespace ArchimedeanClass
section Ring
variable [CommRing M]

section IsOrderedRing
variable [IsOrderedRing M]

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

/-- Multipilication in `M` transfers to Addition in `ArchimedeanClass M`. -/
instance : Add (ArchimedeanClass M) where
  add := lift₂ (fun x y ↦ .mk <| x * y) fun _ _ _ _ hx hy ↦
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

variable (M) in
/-- `ArchimedeanClass.mk` defines an `AddValuation` on the ring `M`. -/
noncomputable def addValuation : AddValuation M (ArchimedeanClass M) := AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul

@[simp] theorem addValuation_apply (a : M) : addValuation M a = mk a := rfl

variable {R : Type*} [LinearOrder R] [CommRing R] [IsOrderedRing R]

@[simp]
theorem orderHom_zero (f : M →+o R) : orderHom f 0 = mk (f 1) := by
  rw [← mk_one, orderHom_mk]

variable [NeZero (1 : M)]

@[simp]
theorem mk_eq_zero_of_archimedean [Archimedean M] {x : M} (h : x ≠ 0) : mk x = 0 :=
  mk_eq_mk_of_archimedean h one_ne_zero

theorem eq_zero_or_top_of_archimedean [Archimedean M] (x : ArchimedeanClass M) : x = 0 ∨ x = ⊤ := by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

theorem mk_map_of_archimedean [Archimedean M] (f : M →+o R) {x : M} (h : x ≠ 0) :
    mk (f x) = mk (f 1) := by
  rw [← orderHom_mk, mk_eq_zero_of_archimedean h, orderHom_zero]

@[simp]
theorem mk_intCast {n : ℤ} (h : n ≠ 0) : mk (n : M) = 0 := by
  simpa using mk_map_of_archimedean ⟨Int.castAddHom M, fun _ ↦ by simp⟩ h

@[simp]
theorem mk_natCast {n : ℕ} (h : n ≠ 0) : mk (n : M) = 0 := by
  rw [← Int.cast_natCast]
  exact mk_intCast (mod_cast h)

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing M]

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

end IsStrictOrderedRing
end Ring

section Field
variable [Field M] [IsOrderedRing M]

attribute [local instance] IsOrderedRing.toIsStrictOrderedRing

instance : Neg (ArchimedeanClass M) where
  neg := lift (fun x ↦ mk x⁻¹) fun x y h ↦ by
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
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (mk_eq_top_iff.not.1 h)]
  zsmul n x := n • x
  zsmul_zero' x := by induction x with | mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := zsmul_succ'
  zsmul_neg' n x := by
    induction x with | mk x
    rw [← mk_zpow, zpow_negSucc, pow_succ, zsmul_succ', mk_inv, mk_mul, ← zpow_natCast, mk_zpow]

@[simp]
theorem mk_ratCast {q : ℚ} (h : q ≠ 0) : mk (q : M) = 0 := by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom M : ℚ →+ M), fun _ ↦ by simp⟩ h

theorem mk_le_mk_iff_ratCast {x y : M} : mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  constructor
  · rintro ⟨n, hn⟩
    obtain rfl | hn₀ := n.eq_zero_or_pos
    · have := exists_gt (0 : ℚ)
      simp_all
    · use (n : ℚ)⁻¹
      aesop (add simp [inv_mul_le_iff₀])
  · rintro ⟨q, hq₀, hq⟩
    obtain ⟨n, hn⟩ := exists_nat_gt q⁻¹
    use n
    simp_rw [ArchimedeanOrder.val_of, nsmul_eq_mul]
    rw [← le_inv_mul_iff₀ (mod_cast hq₀)] at hq
    exact hq.trans (mul_le_mul_of_nonneg_right (mod_cast hn.le) (abs_nonneg x))

theorem mk_lt_mk_iff_ratCast {x y : M} : mk x < mk y ↔ ∀ q : ℚ, q * |y| < |x| := by
  refine ⟨fun H q ↦ ?_, fun H n ↦ by simpa using H n⟩
  obtain ⟨n, hn⟩ := exists_nat_gt q
  apply (H n).trans_le'
  simpa using mul_le_mul_of_nonneg_right (mod_cast hn.le) (abs_nonneg y)

end Field
end ArchimedeanClass
