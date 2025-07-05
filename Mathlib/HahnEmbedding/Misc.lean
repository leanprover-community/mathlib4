import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

@[to_additive]
theorem pow_le_self {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] {a : M} {n : ℕ} (ha : a ≤ 1) (hn : n ≠ 0) :
  a ^ n ≤ a := by
  simpa using pow_le_pow_right_of_le_one' ha (Nat.one_le_iff_ne_zero.2 hn)

@[to_additive]
theorem pow_le_pow_iff_left' {M : Type*} [Monoid M] [LinearOrder M] [h : MulLeftStrictMono M] [MulRightStrictMono M] {a b : M} {n : ℕ} (hn : n ≠ 0) :
  a ^ n ≤ b ^ n ↔ a ≤ b := by
  constructor
  · apply le_of_pow_le_pow_left' hn
  · intro h
    have : MulLeftMono M := mulLeftMono_of_mulLeftStrictMono M
    have : MulRightMono M := mulRightMono_of_mulRightStrictMono M
    apply pow_le_pow_left' h

@[to_additive]
theorem pow_lt_pow_iff_left' {M : Type*} [Monoid M] [LinearOrder M] [h : MulLeftStrictMono M] [MulRightStrictMono M] {a b : M} {n : ℕ} (hn : n ≠ 0) :
  a ^ n < b ^ n ↔ a < b := by
  constructor
  · have : MulLeftMono M := mulLeftMono_of_mulLeftStrictMono M
    have : MulRightMono M := mulRightMono_of_mulRightStrictMono M
    apply lt_of_pow_lt_pow_left' n
  · apply pow_lt_pow_left' hn

theorem map_max {α β F: Type*} [LinearOrder α] [LinearOrder β] [FunLike F α β]
      [OrderHomClass F α β] (f : F) (a b : α):
    f (max a b) = max (f a) (f b) := by
  obtain hab|hab := le_total a b
  all_goals
  · obtain hf := OrderHomClass.monotone f hab
    simp [hf, hab]

@[to_additive]
theorem map_mabs {α β F : Type*} [Group α] [Group β] [LinearOrder α] [LinearOrder β] [FunLike F α β]
    [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α):
    f |a|ₘ = |f a|ₘ := by
  unfold mabs
  rw [map_max]
  simp
