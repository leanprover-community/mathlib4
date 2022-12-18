/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.parity
! leanprover-community/mathlib commit dcf2250875895376a142faeeac5eabff32c48655
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Data.Nat.Cast.Basic

/-!  # Squares, even and odd elements

This file proves some general facts about squares, even and odd elements of semirings.

In the implementation, we define `is_square` and we let `even` be the notion transported by
`to_additive`.  The definition are therefore as follows:
```lean
is_square a ↔ ∃ r, a = r * r
even a ↔ ∃ r, a = r + r
```

Odd elements are not unified with a multiplicative notion.

## Future work

* TODO: Try to generalize further the typeclass assumptions on `is_square/even`.
  For instance, in some cases, there are `semiring` assumptions that I (DT) am not convinced are
  necessary.
* TODO: Consider moving the definition and lemmas about `odd` to a separate file.
* TODO: The "old" definition of `even a` asked for the existence of an element `c` such that
  `a = 2 * c`.  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.
 -/


open MulOpposite

variable {F α β R : Type _}

section Mul

variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `is_square a` if `a = r * r`,
for some `r : α`. -/
@[to_additive Even
      "An element `a` of a type `α` with addition satisfies `even a` if `a = r + r`,\nfor some `r : α`."]
def IsSquare (a : α) : Prop :=
  ∃ r, a = r * r
#align is_square IsSquare

@[simp, to_additive]
theorem is_square_mul_self (m : α) : IsSquare (m * m) :=
  ⟨m, rfl⟩
#align is_square_mul_self is_square_mul_self

-- Porting note: explicitly introduced name
@[to_additive is_even_add_op_iff]
theorem is_square_op_iff (a : α) : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨c, hc⟩ => ⟨unop c, by rw [← unop_mul, ← hc, unop_op]⟩, fun ⟨c, hc⟩ => by simp [hc]⟩
#align is_square_op_iff is_square_op_iff

end Mul

@[simp, to_additive is_even_zero]
theorem is_square_one [MulOneClass α] : IsSquare (1 : α) :=
  ⟨1, (mul_one _).symm⟩
#align is_square_one is_square_one

@[to_additive]
theorem IsSquare.map [MulOneClass α] [MulOneClass β] [MonoidHomClass F α β] {m : α} (f : F) :
    IsSquare m → IsSquare (f m) := by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp⟩
#align is_square.map IsSquare.map

section Monoid

variable [Monoid α] {n : ℕ} {a : α}


@[to_additive even_iff_exists_two_nsmul]
theorem is_square_iff_exists_sq (m : α) : IsSquare m ↔ ∃ c, m = c ^ 2 := by simp [IsSquare, pow_two]
#align is_square_iff_exists_sq is_square_iff_exists_sq

alias is_square_iff_exists_sq ↔ IsSquare.exists_sq is_square_of_exists_sq

-- attribute
--   [to_additive Even.exists_two_nsmul
--       "Alias of the forwards direction of\n`even_iff_exists_two_nsmul`."]
--   IsSquare.exists_sq

-- attribute
--   [to_additive even_of_exists_two_nsmul
--       "Alias of the backwards direction of\n`even_iff_exists_two_nsmul`."]
--   is_square_of_exists_sq

-- @[to_additive Even.nsmul]
theorem IsSquare.pow (n : ℕ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨a, rfl⟩
  exact ⟨a ^ n, (Commute.refl _).mul_pow _⟩
#align is_square.pow IsSquare.pow

-- @[simp, to_additive Even.nsmul']
theorem Even.is_square_pow : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨n, rfl⟩ a
  exact ⟨a ^ n, pow_add _ _ _⟩
#align even.is_square_pow Even.is_square_pow

@[simp, to_additive even_two_nsmul]
theorem is_square_sq (a : α) : IsSquare (a ^ 2) :=
  ⟨a, pow_two _⟩
#align is_square_sq is_square_sq

variable [HasDistribNeg α]

theorem Even.neg_pow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [← two_mul, pow_mul, neg_sq]
#align even.neg_pow Even.neg_pow

theorem Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]
#align even.neg_one_pow Even.neg_one_pow

end Monoid

@[to_additive]
theorem IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a * b, mul_mul_mul_comm _ _ _ _⟩
#align is_square.mul IsSquare.mul

variable (α)

@[simp]
theorem is_square_zero [MulZeroClass α] : IsSquare (0 : α) :=
  ⟨0, (mul_zero _).symm⟩
#align is_square_zero is_square_zero

variable {α}

section DivisionMonoid

variable [DivisionMonoid α] {a : α}

@[simp, to_additive even_neg]
theorem is_square_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← is_square_op_iff, ← inv_inv a]
    exact h.map (MulEquiv.inv' α)
  · exact ((is_square_op_iff a).mpr h).map (MulEquiv.inv' α).symm
#align is_square_inv is_square_inv

alias is_square_inv ↔ _ IsSquare.inv

attribute [to_additive] IsSquare.inv

@[to_additive]
theorem IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨a, rfl⟩
  exact ⟨a ^ n, (Commute.refl _).mul_zpow _⟩
#align is_square.zpow IsSquare.zpow

variable [HasDistribNeg α] {n : ℤ}

theorem Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  exact zpow_bit0_neg _ _
#align even.neg_zpow Even.neg_zpow

theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
#align even.neg_one_zpow Even.neg_one_zpow

end DivisionMonoid

theorem even_abs [SubtractionMonoid α] [LinearOrder α] {a : α} : Even (|a|) ↔ Even a := by
  cases abs_choice a
  · have h : abs a = a := by assumption
    simp only [h, even_neg]
    rfl
  · have h : abs a = -a := by assumption
    simp only [h, even_neg]
    rfl
#align even_abs even_abs

@[to_additive]
theorem IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv
#align is_square.div IsSquare.div

@[simp, to_additive Even.zsmul']
theorem Even.is_square_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨n, rfl⟩ a
  exact ⟨a ^ n, zpow_add _ _ _⟩
#align even.is_square_zpow Even.is_square_zpow

-- `odd.tsub` requires `canonically_linear_ordered_semiring`, which we don't have
theorem Even.tsub [CanonicallyLinearOrderedAddMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {m n : α} (hm : Even m) (hn : Even n) : Even (m - n) :=
  by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine' ⟨a - b, _⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm
#align even.tsub Even.tsub

theorem even_iff_exists_bit0 [Add α] {a : α} : Even a ↔ ∃ b, a = bit0 b :=
  Iff.rfl
#align even_iff_exists_bit0 even_iff_exists_bit0

alias even_iff_exists_bit0 ↔ Even.exists_bit0 _

section Semiring

variable [Semiring α] [Semiring β] {m n : α}

theorem even_iff_exists_two_mul (m : α) : Even m ↔ ∃ c, m = 2 * c := by
  simp [even_iff_exists_two_nsmul]
#align even_iff_exists_two_mul even_iff_exists_two_mul

theorem even_iff_two_dvd {a : α} : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]
#align even_iff_two_dvd even_iff_two_dvd

@[simp]
theorem range_two_mul (α : Type _) [Semiring α] : (Set.range fun x : α => 2 * x) = { a | Even a } :=
  by
  ext x
  simp [eq_comm, two_mul, Even]
#align range_two_mul range_two_mul

@[simp]
theorem even_bit0 (a : α) : Even (bit0 a) :=
  ⟨a, rfl⟩
#align even_bit0 even_bit0

@[simp]
theorem even_two : Even (2 : α) :=
  ⟨1, by rfl⟩
#align even_two even_two

@[simp]
theorem Even.mul_left (hm : Even m) (n) : Even (n * m) :=
  hm.map (AddMonoidHom.mulLeft n)
#align even.mul_left Even.mul_left

@[simp]
theorem Even.mul_right (hm : Even m) (n) : Even (m * n) :=
  hm.map (AddMonoidHom.mulRight n)
#align even.mul_right Even.mul_right

theorem even_two_mul (m : α) : Even (2 * m) :=
  ⟨m, two_mul _⟩
#align even_two_mul even_two_mul

theorem Even.pow_of_ne_zero (hm : Even m) : ∀ {a : ℕ}, a ≠ 0 → Even (m ^ a)
  | 0, a0 => (a0 rfl).elim
  | a + 1, _ => by
    rw [pow_succ]
    exact hm.mul_right _
#align even.pow_of_ne_zero Even.pow_of_ne_zero

section WithOdd

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop :=
  ∃ k, a = 2 * k + 1
#align odd Odd

theorem odd_iff_exists_bit1 {a : α} : Odd a ↔ ∃ b, a = bit1 b :=
  exists_congr fun b => by
    rw [two_mul]
    rfl
#align odd_iff_exists_bit1 odd_iff_exists_bit1

alias odd_iff_exists_bit1 ↔ Odd.exists_bit1 _

@[simp]
theorem odd_bit1 (a : α) : Odd (bit1 a) :=
  odd_iff_exists_bit1.2 ⟨a, rfl⟩
#align odd_bit1 odd_bit1

@[simp]
theorem range_two_mul_add_one (α : Type _) [Semiring α] :
    (Set.range fun x : α => 2 * x + 1) = { a | Odd a } := by
  ext x
  simp [Odd, eq_comm]
#align range_two_mul_add_one range_two_mul_add_one

theorem Even.add_odd : Even m → Odd n → Odd (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, by rw [mul_add, ← two_mul, add_assoc]⟩
#align even.add_odd Even.add_odd

theorem Odd.add_even (hm : Odd m) (hn : Even n) : Odd (m + n) := by
  rw [add_comm]
  exact hn.add_odd hm
#align odd.add_even Odd.add_even

theorem Odd.add_odd : Odd m → Odd n → Even (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨n + m + 1, _⟩
  rw [← two_mul, ← add_assoc, add_comm _ (2 * n), ← add_assoc, ← mul_add, add_assoc,
    mul_add _ (n + m), mul_one]
  rfl
#align odd.add_odd Odd.add_odd

@[simp]
theorem odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
#align odd_one odd_one

@[simp]
theorem odd_two_mul_add_one (m : α) : Odd (2 * m + 1) :=
  ⟨m, rfl⟩
#align odd_two_mul_add_one odd_two_mul_add_one

theorem Odd.map [RingHomClass F α β] (f : F) : Odd m → Odd (f m) := by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp [two_mul]⟩
#align odd.map Odd.map

@[simp]
theorem Odd.mul : Odd m → Odd n → Odd (m * n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨2 * m * n + n + m, _⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
#align odd.mul Odd.mul

theorem Odd.pow (hm : Odd m) : ∀ {a : ℕ}, Odd (m ^ a)
  | 0 => by
    rw [pow_zero]
    exact odd_one
  | a + 1 => by
    rw [pow_succ]
    exact hm.mul <| Odd.pow hm
#align odd.pow Odd.pow

end WithOdd

end Semiring

section Monoid

variable [Monoid α] [HasDistribNeg α] {a : α} {n : ℕ}


theorem Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
#align odd.neg_pow Odd.neg_pow

theorem Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]
#align odd.neg_one_pow Odd.neg_one_pow

end Monoid

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α]

-- this holds more generally in a `canonically_ordered_add_monoid` if we refactor `odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
theorem Odd.pos [Nontrivial α] {n : α} (hn : Odd n) : 0 < n := by
  obtain ⟨k, rfl⟩ := hn
  rw [pos_iff_ne_zero, Ne.def, add_eq_zero_iff, not_and']
  exact fun h => (one_ne_zero h).elim
#align odd.pos Odd.pos

end CanonicallyOrderedCommSemiring

section Ring

variable [Ring α] {a b : α} {n : ℕ}

@[simp]
theorem even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
#align even_neg_two even_neg_two

theorem Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right, ←
    neg_add, hk]
#align odd.neg Odd.neg

@[simp]
theorem odd_neg : Odd (-a) ↔ Odd a :=
  ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩
#align odd_neg odd_neg

@[simp]
theorem odd_neg_one : Odd (-1 : α) := by simp
#align odd_neg_one odd_neg_one

theorem Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_even hb.neg
#align odd.sub_even Odd.sub_even

theorem Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg
#align even.sub_odd Even.sub_odd

theorem Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add_odd hb.neg
#align odd.sub_odd Odd.sub_odd

theorem odd_abs [LinearOrder α] : Odd (abs a) ↔ Odd a := by
  cases' abs_choice a with h h <;> simp only [h, odd_neg] <;> rfl
#align odd_abs odd_abs

end Ring

section Powers

variable [LinearOrderedRing R] {a : R} {n : ℕ}

theorem Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  cases' hn with k hk ; simpa only [hk, two_mul] using pow_bit0_nonneg a k
#align even.pow_nonneg Even.pow_nonneg

theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := by
  cases' hn with k hk ; simpa only [hk, two_mul] using pow_bit0_pos ha k
#align even.pow_pos Even.pow_pos

theorem Odd.pow_nonpos (hn : Odd n) (ha : a ≤ 0) : a ^ n ≤ 0 := by
  cases' hn with k hk ; simpa only [hk, two_mul] using pow_bit1_nonpos_iff.mpr ha
#align odd.pow_nonpos Odd.pow_nonpos

theorem Odd.pow_neg (hn : Odd n) (ha : a < 0) : a ^ n < 0 := by
  cases' hn with k hk ; simpa only [hk, two_mul] using pow_bit1_neg_iff.mpr ha
#align odd.pow_neg Odd.pow_neg

theorem Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  ⟨fun h => le_of_not_lt fun ha => h.not_lt <| hn.pow_neg ha, fun ha => pow_nonneg ha n⟩
#align odd.pow_nonneg_iff Odd.pow_nonneg_iff

theorem Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
  ⟨fun h => le_of_not_lt fun ha => h.not_lt <| pow_pos ha _, hn.pow_nonpos⟩
#align odd.pow_nonpos_iff Odd.pow_nonpos_iff

theorem Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a :=
  ⟨fun h => lt_of_not_le fun ha => h.not_le <| hn.pow_nonpos ha, fun ha => pow_pos ha n⟩
#align odd.pow_pos_iff Odd.pow_pos_iff

theorem Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 :=
  ⟨fun h => lt_of_not_le fun ha => h.not_le <| pow_nonneg ha _, hn.pow_neg⟩
#align odd.pow_neg_iff Odd.pow_neg_iff

theorem Even.pow_pos_iff (hn : Even n) (h₀ : 0 < n) : 0 < a ^ n ↔ a ≠ 0 :=
  ⟨fun h ha => by
    rw [ha, zero_pow h₀] at h
    exact lt_irrefl 0 h, hn.pow_pos⟩
#align even.pow_pos_iff Even.pow_pos_iff

theorem Even.pow_abs {p : ℕ} (hp : Even p) (a : R) : |a| ^ p = a ^ p := by
  rw [← abs_pow, abs_eq_self]
  exact hp.pow_nonneg _
#align even.pow_abs Even.pow_abs

@[simp]
theorem pow_bit0_abs (a : R) (p : ℕ) : |a| ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).pow_abs _
#align pow_bit0_abs pow_bit0_abs

theorem Odd.strict_mono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  cases' hn with k hk ; simpa only [hk, two_mul] using strict_mono_pow_bit1 _
#align odd.strict_mono_pow Odd.strict_mono_pow

end Powers
