/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Dyadic.OrderedRing
public import Mathlib.RingTheory.Localization.Defs

/-!
# Dyadic rationals as a localization

We prove `Dyadic` is the localization of `ℤ` at `Submonoid.powers 2`.
-/

public section
namespace Dyadic

/-- The dyadic number ½. -/
@[expose]
def half : Units Dyadic where
  val := (1 : Dyadic) >>> 1
  inv := 2
  val_inv := rfl
  inv_val := rfl

-- `@[simps]` for `Units` is broken, see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60.40.5Bsimps.5D.60.20for.20.60Units.60.20is.20broken/near/618107577
@[simp] theorem val_inv_half : ↑(half⁻¹) = (2 : Dyadic) := rfl

instance : Invertible (2 : Dyadic) where
  invOf := half
  invOf_mul_self := rfl
  mul_invOf_self := rfl

theorem invOf_two_eq_half : (⅟2 : Dyadic) = half := rfl

theorem val_half_eq_ofOdd : half = ofOdd 1 1 rfl := rfl

theorem val_half_zpow_eq_ofOdd (n : ℤ) : ↑(half ^ n) = ofOdd 1 n rfl := by
  rw [← neg_neg n]
  induction -n using Int.negInduction with
  | nat n =>
    rw [zpow_neg, ← inv_zpow, zpow_natCast, Units.val_pow_eq_pow_val, val_inv_half,
      ← Int.cast_ofNat (nat_lit 2), ← Int.cast_pow,
      ← toRat_inj, toRat_intCast, toRat_ofOdd_eq_mul_two_pow, Int.cast_one, neg_neg,
      zpow_natCast, Int.cast_pow, Int.cast_ofNat, Rat.one_mul]
  | neg ih n =>
    rw [← Units.mul_left_inj (half ^ (-n : ℤ)), ← Units.val_mul, ← zpow_add,
      Int.add_left_neg, zpow_zero, Units.val_one, ih]
    change ofOdd 1 0 rfl = ofOdd ..
    simp

instance : IsLocalization (Submonoid.powers (2 : ℤ)) Dyadic where
  map_units := by
    simp_rw [Subtype.forall, Submonoid.mem_powers_iff, ← Set.mem_range, Set.forall_mem_range,
      algebraMap_int_eq, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]
    intro i
    rw [← val_inv_half, ← Units.val_pow_eq_pow_val]
    exact (half⁻¹ ^ i).isUnit
  exists_of_eq := by simp [← SetLike.mem_coe, ← Set.nonempty_def]
  surj := by
    intro z
    cases z with | zero => exact ⟨(0, 1), by simp⟩ | ofOdd n k hn
    cases k with
    | ofNat k =>
      refine ⟨(n, ⟨2 ^ k, (Submonoid.mem_powers_iff (2 ^ k) 2).2 ⟨k, rfl⟩⟩), ?_⟩
      rw [← toRat_inj, algebraMap_int_eq, Int.coe_castRingHom, toRat_intCast,
        toRat_mul, toRat_intCast, Int.cast_pow, Int.cast_ofNat,
        toRat_ofOdd_eq_mul_two_pow, Int.ofNat_eq_natCast, Rat.mul_assoc,
        ← zpow_natCast, ← zpow_add₀ two_ne_zero, Int.add_left_neg, zpow_zero, Rat.mul_one]
    | negSucc k =>
      refine ⟨(n * 2 ^ (k + 1), 1), ?_⟩
      rw [← toRat_inj, algebraMap_int_eq, Int.coe_castRingHom, toRat_intCast,
        toRat_mul, toRat_intCast, Submonoid.coe_one, Int.cast_one,
        toRat_ofOdd_eq_mul_two_pow, Int.neg_negSucc, zpow_natCast, Rat.mul_one,
        Int.cast_mul, Int.cast_pow, Int.cast_ofNat]

theorem isUnit_iff_exists_half_pow {x : Dyadic} :
    IsUnit x ↔ ∃ n : ℤ, ↑(half ^ n) = x ∨ -↑(half ^ n) = x := by
  refine ⟨fun hx => ?_, by rintro ⟨n, rfl | rfl⟩ <;> simp only [IsUnit.neg_iff, Units.isUnit]⟩
  rw [isUnit_iff_exists] at hx
  obtain ⟨b, hxb, hbx⟩ := hx
  cases x with | zero => simp at hxb | ofOdd nx kx hnx
  cases b with | zero => simp at hxb | ofOdd nb kb hnb
  refine ⟨kx, ?_⟩
  change ofOdd .. = ofOdd 1 0 rfl at hxb
  injection hxb with hn hk
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rw [val_half_zpow_eq_ofOdd]
  · right
    rw [val_half_zpow_eq_ofOdd, neg_ofOdd]

end Dyadic
