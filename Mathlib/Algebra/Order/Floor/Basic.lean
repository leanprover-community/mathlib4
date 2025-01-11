/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Group.Int
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.GaloisConnection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
/-!
# Floor and ceil

## Summary

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.

## Main Definitions

* `FloorSemiring`: An ordered semiring with natural-valued floor and ceil.
* `Nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.
* `Nat.ceil a`: Least natural `n` such that `a ≤ n`.

* `FloorRing`: A linearly ordered ring with integer-valued floor and ceil.
* `Int.floor a`: Greatest integer `z` such that `z ≤ a`.
* `Int.ceil a`: Least integer `z` such that `a ≤ z`.
* `Int.fract a`: Fractional part of `a`, defined as `a - floor a`.
* `round a`: Nearest integer to `a`. It rounds halves towards infinity.

## Notations

* `⌊a⌋₊` is `Nat.floor a`.
* `⌈a⌉₊` is `Nat.ceil a`.
* `⌊a⌋` is `Int.floor a`.
* `⌈a⌉` is `Int.ceil a`.

The index `₊` in the notations for `Nat.floor` and `Nat.ceil` is used in analogy to the notation
for `nnnorm`.

## TODO

`LinearOrderedRing`/`LinearOrderedSemiring` can be relaxed to `OrderedRing`/`OrderedSemiring` in
many lemmas.

## Tags

rounding, floor, ceil
-/

assert_not_exists Finset

open Set

variable {F α β : Type*}

/-! ### Floor semiring -/

namespace Nat

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] [FloorSemiring α]

-- TODO: should these lemmas be `simp`? `norm_cast`?

theorem floor_div_nat (a : α) (n : ℕ) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply div_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [cast_zero, div_zero, Nat.div_zero, floor_zero]
  refine (floor_eq_iff ?_).2 ?_
  · exact div_nonneg ha n.cast_nonneg
  constructor
  · exact cast_div_le.trans (div_le_div_of_nonneg_right (floor_le ha) n.cast_nonneg)
  rw [div_lt_iff₀, add_mul, one_mul, ← cast_mul, ← cast_add, ← floor_lt ha]
  · exact lt_div_mul_add hn
  · exact cast_pos.2 hn

theorem floor_div_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n) :=
  floor_div_nat a n

/-- Natural division is the floor of field division. -/
theorem floor_div_eq_div (m n : ℕ) : ⌊(m : α) / n⌋₊ = m / n := by
  convert floor_div_nat (m : α) n
  rw [m.floor_natCast]

end LinearOrderedSemifield

section LinearOrderedField
variable [LinearOrderedField α] [FloorSemiring α] {a b : α}

lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ ≤ a) : b * a < ⌊a⌋₊ := by
  calc
    b * a < b * (⌊a⌋₊ + 1) := by gcongr; exacts [hb₀, lt_floor_add_one _]
    _ ≤ ⌊a⌋₊ := by
      rw [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le]
      exact le_floor hba

lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a) : ⌈a⌉₊ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉₊ ≤ (⌈(b - 1)⁻¹⌉₊ : α) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉₊ < a + 1 := ceil_lt_add_one <| hba.trans' <| by positivity
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr; positivity
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b ≤ a) : ⌈a⌉₊ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (ceil_lt_mul hb hba).le

lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋₊ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉₊ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉₊ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField
end Nat

/-! ### Floor rings -/

namespace Int

variable [LinearOrderedRing α] [FloorRing α] {z : ℤ} {a b : α}


/-! #### Floor -/

theorem abs_sub_lt_one_of_floor_eq_floor {α : Type*} [LinearOrderedCommRing α] [FloorRing α]
    {a b : α} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  have : a < ⌊a⌋ + 1 := lt_floor_add_one a
  have : b < ⌊b⌋ + 1 := lt_floor_add_one b
  have : (⌊a⌋ : α) = ⌊b⌋ := Int.cast_inj.2 h
  have : (⌊a⌋ : α) ≤ a := floor_le a
  have : (⌊b⌋ : α) ≤ b := floor_le b
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩


/-! #### Fractional part -/

theorem fract_eq_iff {a b : α} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
  ⟨fun h => by
    rw [← h]
    exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
   by
    rintro ⟨h₀, h₁, z, hz⟩
    rw [← self_sub_floor, eq_comm, eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq, hz,
      Int.cast_inj, floor_eq_iff, ← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩

theorem fract_eq_fract {a b : α} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
  ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
   by
    rintro ⟨z, hz⟩
    refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, ?_⟩
    rw [eq_add_of_sub_eq hz, add_comm, Int.cast_add]
    exact add_sub_sub_cancel _ _ _⟩

@[simp]
theorem fract_eq_self {a : α} : fract a = a ↔ 0 ≤ a ∧ a < 1 :=
  fract_eq_iff.trans <| and_assoc.symm.trans <| and_iff_left ⟨0, by simp⟩

@[simp]
theorem fract_fract (a : α) : fract (fract a) = fract a :=
  fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩

theorem fract_add (a b : α) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
  ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by
    unfold fract
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg, cast_add, cast_neg]
    abel⟩

theorem fract_neg {x : α} (hx : fract x ≠ 0) : fract (-x) = 1 - fract x := by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[simp]
theorem fract_neg_eq_zero {x : α} : fract (-x) = 0 ↔ fract x = 0 := by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

theorem fract_mul_nat (a : α) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z := by
  induction' b with c hc
  · use 0; simp
  · rcases hc with ⟨z, hz⟩
    rw [Nat.cast_add, mul_add, mul_add, Nat.cast_one, mul_one, mul_one]
    rcases fract_add (a * c) a with ⟨y, hy⟩
    use z - y
    rw [Int.cast_sub, ← hz, ← hy]
    abel

section LinearOrderedField

variable {k : Type*} [LinearOrderedField k] [FloorRing k] {b : k}

theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a ∈ Ico 0 a :=
  ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

theorem fract_div_mul_self_add_zsmul_eq (a b : k) (ha : a ≠ 0) :
    fract (b / a) * a + ⌊b / a⌋ • a = b := by
  rw [zsmul_eq_mul, ← add_mul, fract_add_floor, div_mul_cancel₀ b ha]

theorem sub_floor_div_mul_nonneg (a : k) (hb : 0 < b) : 0 ≤ a - ⌊a / b⌋ * b :=
  sub_nonneg_of_le <| (le_div_iff₀ hb).1 <| floor_le _

theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b :=
  sub_lt_iff_lt_add.2 <| by
    -- Porting note: `← one_add_mul` worked in mathlib3 without the argument
    rw [← one_add_mul _ b, ← div_lt_iff₀ hb, add_comm]
    exact lt_floor_add_one _

theorem fract_div_natCast_eq_div_natCast_mod {m n : ℕ} : fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : k) := by
    norm_cast
  refine fract_eq_iff.mpr ⟨?_, ?_, m / n, ?_⟩
  · positivity
  · simpa only [div_lt_one hn', Nat.cast_lt] using m.mod_lt hn
  · rw [sub_eq_iff_eq_add', ← mul_right_inj' hn'.ne', mul_div_cancel₀ _ hn'.ne', mul_add,
      mul_div_cancel₀ _ hn'.ne']
    norm_cast
    rw [← Nat.cast_add, Nat.mod_add_div m n]

theorem fract_div_intCast_eq_div_intCast_mod {m : ℤ} {n : ℕ} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : ∀ {l : ℤ}, 0 ≤ l → fract ((l : k) / n) = ↑(l % n) / n := by
    intros l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (ofNat_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : ℤ)
  have hm₁ : 0 ≤ m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : ℤ)) : k) / (n : k))
      -- Porting note: the `rw [cast_neg, cast_natCast]` was `push_cast`
      = fract (-(m₀ : k) / n) := by rw [cast_neg, cast_natCast]
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : ℤ)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : ℤ) % ↑n) / Nat.cast n := ?_

  · rw [← fract_int_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    -- Porting note: the `simp` was `push_cast`
    simp [m₁]
  · congr 2
    change (q * ↑n - (↑m₀ : ℤ)) % ↑n = _
    rw [sub_eq_add_neg, add_comm (q * ↑n), add_mul_emod_self]

end LinearOrderedField

/-! #### Ceil -/

theorem ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, (⌈a⌉ : α) = z := fun a ha =>
  mod_cast ceil_eq_on_Ioc z a ha

theorem fract_eq_zero_or_add_one_sub_ceil (a : α) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : α) := by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : α) = ⌊a⌋ + 1 by
    rw [this, ← self_sub_fract]
    abel
  norm_cast
  rw [ceil_eq_iff]
  refine ⟨?_, _root_.le_of_lt <| by simp⟩
  rw [cast_add, cast_one, add_tsub_cancel_right, ← self_sub_fract a, sub_lt_self_iff]
  exact ha.symm.lt_of_le (fract_nonneg a)

theorem ceil_eq_add_one_sub_fract (ha : fract a ≠ 0) : (⌈a⌉ : α) = a + 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

theorem ceil_sub_self_eq (ha : fract a ≠ 0) : (⌈a⌉ : α) - a = 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

section LinearOrderedField
variable {k : Type*} [LinearOrderedField k] [FloorRing k] {a b : k}

lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ ≤ a) : b * a < ⌊a⌋ := by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; exacts [hb₀, lt_floor_add_one _]
    _ ≤ ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

lemma ceil_div_ceil_inv_sub_one (ha : 1 ≤ a) : ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉ := by
  obtain rfl | ha := ha.eq_or_lt
  · simp
  have : 0 < a - 1 := by linarith
  have : 0 < ⌈(a - 1)⁻¹⌉ := ceil_pos.2 <| by positivity
  refine le_antisymm (ceil_le.2 <| div_le_self (by positivity) ha.le) <| ?_
  rw [le_ceil_iff, sub_lt_comm, div_eq_mul_inv, ← mul_one_sub,
    ← lt_div_iff₀ (sub_pos.2 <| inv_lt_one_of_one_lt₀ ha)]
  convert ceil_lt_add_one _ using 1
  field_simp

lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a) : ⌈a⌉ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ ≤ (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr; positivity
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b ≤ a) : ⌈a⌉ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (ceil_lt_mul hb hba).le

lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField

end Int

open Int

/-! ### Round -/

section round

section LinearOrderedRing

variable [LinearOrderedRing α] [FloorRing α]

theorem abs_sub_round_eq_min (x : α) : |x - round x| = min (fract x) (1 - fract x) := by
  simp_rw [round, min_def_lt, two_mul, ← lt_tsub_iff_left]
  cases' lt_or_ge (fract x) (1 - fract x) with hx hx
  · rw [if_pos hx, if_pos hx, self_sub_floor, abs_fract]
  · have : 0 < fract x := by
      replace hx : 0 < fract x + fract x := lt_of_lt_of_le zero_lt_one (tsub_le_iff_left.mp hx)
      simpa only [← two_mul, mul_pos_iff_of_pos_left, zero_lt_two] using hx
    rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr hx), abs_sub_comm, ceil_sub_self_eq this.ne.symm,
      abs_one_sub_fract]

theorem round_le (x : α) (z : ℤ) : |x - round x| ≤ |x - z| := by
  rw [abs_sub_round_eq_min, min_le_iff]
  rcases le_or_lt (z : α) x with (hx | hx) <;> [left; right]
  · conv_rhs => rw [abs_eq_self.mpr (sub_nonneg.mpr hx), ← fract_add_floor x, add_sub_assoc]
    simpa only [le_add_iff_nonneg_right, sub_nonneg, cast_le] using le_floor.mpr hx
  · rw [abs_eq_neg_self.mpr (sub_neg.mpr hx).le]
    conv_rhs => rw [← fract_add_floor x]
    rw [add_sub_assoc, add_comm, neg_add, neg_sub, le_add_neg_iff_add_le, sub_add_cancel,
      le_sub_comm]
    norm_cast
    exact floor_le_sub_one_iff.mpr hx

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField α] [FloorRing α]

theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  simp_rw [round, (by simp only [lt_div_iff₀', two_pos] : 2 * fract x < 1 ↔ fract x < 1 / 2)]
  cases' lt_or_le (fract x) (1 / 2) with hx hx
  · conv_rhs => rw [← fract_add_floor x, add_assoc, add_left_comm, floor_int_add]
    rw [if_pos hx, self_eq_add_right, floor_eq_iff, cast_zero, zero_add]
    constructor
    · linarith [fract_nonneg x]
    · linarith
  · have : ⌊fract x + 1 / 2⌋ = 1 := by
      rw [floor_eq_iff]
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [fract_lt_one x]
    rw [if_neg (not_lt.mpr hx), ← fract_add_floor x, add_assoc, add_left_comm, floor_int_add,
      ceil_add_int, add_comm _ ⌊x⌋, add_right_inj, ceil_eq_iff, this, cast_one, sub_self]
    constructor
    · linarith
    · linarith [fract_lt_one x]

@[simp]
theorem round_two_inv : round (2⁻¹ : α) = 1 := by
  simp only [round_eq, ← one_div, add_halves, floor_one]

@[simp]
theorem round_neg_two_inv : round (-2⁻¹ : α) = 0 := by
  simp only [round_eq, ← one_div, neg_add_cancel, floor_zero]

@[simp]
theorem round_eq_zero_iff {x : α} : round x = 0 ↔ x ∈ Ico (-(1 / 2)) ((1 : α) / 2) := by
  rw [round_eq, floor_eq_zero_iff, add_mem_Ico_iff_left]
  norm_num

theorem abs_sub_round (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq, abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

theorem abs_sub_round_div_natCast_eq {m n : ℕ} :
    |(m : α) / n - round ((m : α) / n)| = ↑(min (m % n) (n - m % n)) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min, Nat.cast_min, ← min_div_div_right hn'.le,
    fract_div_natCast_eq_div_natCast_mod, Nat.cast_sub (m.mod_lt hn).le, sub_div, div_self hn'.ne']

@[bound]
theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
  rw [round_eq x, show x - 1 / 2 = x + 1 / 2 - 1 by linarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

@[bound]
theorem round_le_add_half (x : α) : round x ≤ x + 1 / 2 := by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)

end LinearOrderedField

end round

namespace Int

variable [LinearOrderedRing α] [LinearOrderedRing β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋ = ⌊a⌋ :=
  floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉ = ⌈a⌉ :=
  ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

theorem map_fract (f : F) (hf : StrictMono f) (a : α) : fract (f a) = f (fract a) := by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]

end Int

namespace Int

variable [LinearOrderedField α] [LinearOrderedField β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by
  have H : f 2 = 2 := map_natCast f 2
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, H]
  -- Porting note: was
  -- simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_bit0, map_one]
  -- Would have thought that `map_natCast` would replace `map_bit0, map_one` but seems not

end Int

section FloorRingToSemiring

variable [LinearOrderedRing α] [FloorRing α]

/-! #### A floor ring as a floor semiring -/

-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {_} ha := Int.toNat_of_nonpos (Int.floor_nonpos ha.le)
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_natCast]
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast]

theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl

theorem Int.ceil_toNat (a : α) : ⌈a⌉.toNat = ⌈a⌉₊ :=
  rfl

@[simp]
theorem Nat.floor_int : (Nat.floor : ℤ → ℕ) = Int.toNat :=
  rfl

@[simp]
theorem Nat.ceil_int : (Nat.ceil : ℤ → ℕ) = Int.toNat :=
  rfl

variable {a : α}

theorem Int.natCast_floor_eq_floor (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

theorem Int.natCast_ceil_eq_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

theorem natCast_floor_eq_intCast_floor (ha : 0 ≤ a) : (⌊a⌋₊ : α) = ⌊a⌋ := by
  rw [← Int.natCast_floor_eq_floor ha, Int.cast_natCast]

theorem natCast_ceil_eq_intCast_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : α) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil ha, Int.cast_natCast]

@[deprecated (since := "2024-08-20")] alias Int.ofNat_floor_eq_floor := natCast_floor_eq_floor
@[deprecated (since := "2024-08-20")] alias Int.ofNat_ceil_eq_ceil := natCast_ceil_eq_ceil

end FloorRingToSemiring

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

private theorem int_floor_nonneg [LinearOrderedRing α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
    0 ≤ ⌊a⌋ :=
  Int.floor_nonneg.2 ha

private theorem int_floor_nonneg_of_pos [LinearOrderedRing α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 ≤ ⌊a⌋ :=
  int_floor_nonneg ha.le

/-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
@[positivity ⌊ _ ⌋]
def evalIntFloor : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α' $i $j $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg_of_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.floor application"

private theorem nat_ceil_pos [LinearOrderedSemiring α] [FloorSemiring α] {a : α} :
    0 < a → 0 < ⌈a⌉₊ :=
  Nat.ceil_pos.2

/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
@[positivity ⌈ _ ⌉₊]
def evalNatCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α' $i $j $a) =>
    let _i : Q(LinearOrderedSemiring $α') ← synthInstanceQ (u := u_1) _
    assertInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(nat_ceil_pos (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Nat.ceil application"

private theorem int_ceil_pos [LinearOrderedRing α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ :=
  Int.ceil_pos.2

/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
@[positivity ⌈ _ ⌉]
def evalIntCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α' $i $j $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.positive q(int_ceil_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(Int.ceil_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.ceil application"

end Mathlib.Meta.Positivity
