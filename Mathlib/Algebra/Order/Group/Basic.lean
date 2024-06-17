/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

#align_import algebra.group_power.order from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Lemmas about the interaction of power operations with order
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α M R : Type*}

section OrderedCommGroup
variable [OrderedCommGroup α] {m n : ℤ} {a b : α}

@[to_additive zsmul_pos] lemma one_lt_zpow' (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  rw [zpow_natCast]
  refine one_lt_pow' ha ?_
  rintro rfl
  simp at hn
#align one_lt_zpow' one_lt_zpow'
#align zsmul_pos zsmul_pos

@[to_additive zsmul_strictMono_left]
lemma zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := fun m n h ↦
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ < a ^ m * a ^ (n - m) := mul_lt_mul_left' (one_lt_zpow' ha <| Int.sub_pos_of_lt h) _
    _ = a ^ n := by simp [← zpow_add, m.add_comm]
#align zpow_strict_mono_right zpow_right_strictMono
#align zsmul_strict_mono_left zsmul_strictMono_left

@[to_additive zsmul_mono_left]
lemma zpow_mono_right (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := fun m n h ↦
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ ≤ a ^ m * a ^ (n - m) := mul_le_mul_left' (one_le_zpow ha <| Int.sub_nonneg_of_le h) _
    _ = a ^ n := by simp [← zpow_add, m.add_comm]
#align zpow_mono_right zpow_mono_right
#align zsmul_mono_left zsmul_mono_left

@[to_additive (attr := gcongr)]
lemma zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_mono_right ha h
#align zpow_le_zpow zpow_le_zpow
#align zsmul_le_zsmul zsmul_le_zsmul

@[to_additive (attr := gcongr)]
lemma zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h
#align zpow_lt_zpow zpow_lt_zpow
#align zsmul_lt_zsmul zsmul_lt_zsmul

@[to_additive]
lemma zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (zpow_right_strictMono ha).le_iff_le
#align zpow_le_zpow_iff zpow_le_zpow_iff
#align zsmul_le_zsmul_iff zsmul_le_zsmul_iff

@[to_additive]
lemma zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_right_strictMono ha).lt_iff_lt
#align zpow_lt_zpow_iff zpow_lt_zpow_iff
#align zsmul_lt_zsmul_iff zsmul_lt_zsmul_iff

variable (α)

@[to_additive zsmul_strictMono_right]
lemma zpow_strictMono_left (hn : 0 < n) : StrictMono ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_lt_div', ← div_zpow]; exact one_lt_zpow' (one_lt_div'.2 hab) hn
#align zpow_strict_mono_left zpow_strictMono_left
#align zsmul_strict_mono_right zsmul_strictMono_right

@[to_additive zsmul_mono_right]
lemma zpow_mono_left (hn : 0 ≤ n) : Monotone ((· ^ n) : α → α) := fun a b hab => by
  rw [← one_le_div', ← div_zpow]; exact one_le_zpow (one_le_div'.2 hab) hn
#align zpow_mono_left zpow_mono_left
#align zsmul_mono_right zsmul_mono_right

variable {α}

@[to_additive (attr := gcongr)]
lemma zpow_le_zpow' (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_mono_left α hn h
#align zpow_le_zpow' zpow_le_zpow'
#align zsmul_le_zsmul' zsmul_le_zsmul'

@[to_additive (attr := gcongr)]
lemma zpow_lt_zpow' (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_strictMono_left α hn h
#align zpow_lt_zpow' zpow_lt_zpow'
#align zsmul_lt_zsmul' zsmul_lt_zsmul'

end OrderedCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {n : ℤ} {a b : α}

@[to_additive] lemma zpow_le_zpow_iff' (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_strictMono_left α hn).le_iff_le
#align zpow_le_zpow_iff' zpow_le_zpow_iff'
#align zsmul_le_zsmul_iff' zsmul_le_zsmul_iff'

@[to_additive] lemma zpow_lt_zpow_iff' (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_strictMono_left α hn).lt_iff_lt
#align zpow_lt_zpow_iff' zpow_lt_zpow_iff'
#align zsmul_lt_zsmul_iff' zsmul_lt_zsmul_iff'

@[to_additive zsmul_right_injective
"See also `smul_right_injective`. TODO: provide a `NoZeroSMulDivisors` instance. We can't do
that here because importing that definition would create import cycles."]
lemma zpow_left_injective (hn : n ≠ 0) : Injective ((· ^ n) : α → α) := by
  obtain hn | hn := hn.lt_or_lt
  · refine fun a b (hab : a ^ n = b ^ n) ↦
      (zpow_strictMono_left _ $ Int.neg_pos_of_neg hn).injective ?_
    rw [zpow_neg, zpow_neg, hab]
  · exact (zpow_strictMono_left _ hn).injective
#align zpow_left_injective zpow_left_injective
#align zsmul_right_injective zsmul_right_injective

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (zpow_left_injective hn).eq_iff
#align zpow_left_inj zpow_left_inj
#align zsmul_right_inj zsmul_right_inj

/-- Alias of `zpow_left_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive "Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`."]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn
#align zpow_eq_zpow_iff' zpow_eq_zpow_iff'
#align zsmul_eq_zsmul_iff' zsmul_eq_zsmul_iff'

end LinearOrderedCommGroup

section LinearOrderedAddCommGroupWithTop

variable {α : Type*} [LinearOrderedAddCommGroupWithTop α]

@[simp]
lemma top_ne_zero' :
    (⊤ : α) ≠ 0 := by
  intro nh
  have ⟨a, b, h⟩ := Nontrivial.exists_pair_ne (α := α)
  have : a + 0 ≠ b + 0 := by simpa
  rw [← nh] at this
  simp at this

@[simp] lemma neg_eq_top {a : α} : -a = ⊤ ↔ a = ⊤ where
  mp h := by
    by_contra nh
    replace nh := add_neg_cancel_of_ne_top nh
    rw [h, add_top] at nh
    exact top_ne_zero' nh
  mpr h := h ▸ neg_top

@[simp]
lemma add_eq_top {a b : α} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ where
  mp h := by
    by_contra nh
    rw [not_or] at nh
    replace h := congrArg (-a + ·) h
    dsimp only at h
    rw [add_top, ← add_assoc, add_comm (-a), add_neg_cancel_of_ne_top,
      zero_add] at h
    · exact nh.2 h
    · exact nh.1
  mpr h := by
    cases h <;> simp_all

instance (priority := 100) toSubtractionMonoid : SubtractionMonoid α where
  neg_neg (a) := by
    by_cases h : a = ⊤
    · simp [h]
    · have h2 : ¬ -a = ⊤ := fun nh ↦ h <| (neg_eq_top ..).mp nh
      replace h2 : a + (-a + - -a) = a + 0 := congrArg (a + ·) (add_neg_cancel_of_ne_top h2)
      rw [← add_assoc, add_neg_cancel_of_ne_top h] at h2
      simp only [zero_add, add_zero] at h2
      exact h2
  neg_add_rev (a b) := by
    by_cases ha : a = ⊤
    · simp [ha]
    by_cases hb : b = ⊤
    · simp [hb]
    apply (_ : Function.Injective (a + b + ·))
    · dsimp
      rw [add_neg_cancel_of_ne_top, ← add_assoc, add_assoc a,
        add_neg_cancel_of_ne_top hb, add_zero,
        add_neg_cancel_of_ne_top ha]
      simp [ha, hb]
    · apply Function.LeftInverse.injective (g := (-(a + b) + ·))
      intro x
      dsimp only
      rw [← add_assoc, add_comm (-(a + b)), add_neg_cancel_of_ne_top, zero_add]
      simp [ha, hb]
  neg_eq_of_add (a b) (h) := by
    have oh := congrArg (-a + ·) h
    dsimp only at oh
    rw [add_zero, ← add_assoc, add_comm (-a), add_neg_cancel_of_ne_top, zero_add] at oh
    · exact oh.symm
    intro v
    simp [v] at h

end LinearOrderedAddCommGroupWithTop
