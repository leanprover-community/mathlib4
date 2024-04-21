/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Set.Defs

#align_import algebra.parity from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!  # Squares, even and odd elements

This file proves some general facts about squares, even and odd elements of semirings.

In the implementation, we define `IsSquare` and we let `Even` be the notion transported by
`to_additive`.  The definition are therefore as follows:
```lean
IsSquare a ↔ ∃ r, a = r * r
Even a ↔ ∃ r, a = r + r
```

Odd elements are not unified with a multiplicative notion.

## Future work

* TODO: Try to generalize further the typeclass assumptions on `IsSquare/Even`.
  For instance, in some cases, there are `Semiring` assumptions that I (DT) am not convinced are
  necessary.
* TODO: Consider moving the definition and lemmas about `Odd` to a separate file.
* TODO: The "old" definition of `Even a` asked for the existence of an element `c` such that
  `a = 2 * c`.  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.
 -/


open MulOpposite

variable {F α β R : Type*}

section Mul

variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`,
for some `r : α`. -/
@[to_additive
      "An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,
      for some `r : α`."]
def IsSquare (a : α) : Prop :=
  ∃ r, a = r * r
#align is_square IsSquare
#align even Even

@[to_additive (attr := simp)]
theorem isSquare_mul_self (m : α) : IsSquare (m * m) :=
  ⟨m, rfl⟩
#align is_square_mul_self isSquare_mul_self
#align even_add_self even_add_self

@[to_additive]
theorem isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨c, hc⟩ => ⟨unop c, congr_arg unop hc⟩, fun ⟨c, hc⟩ => ⟨op c, congr_arg op hc⟩⟩
#align is_square_op_iff isSquare_op_iff
#align even_op_iff even_op_iff

@[to_additive]
theorem isSquare_unop_iff {a : αᵐᵒᵖ} : IsSquare (unop a) ↔ IsSquare a := isSquare_op_iff.symm

@[to_additive]
instance [DecidablePred (IsSquare : α → Prop)] : DecidablePred (IsSquare : αᵐᵒᵖ → Prop) :=
  fun _ => decidable_of_iff _ isSquare_unop_iff

@[simp]
theorem even_ofMul_iff {a : α} : Even (Additive.ofMul a) ↔ IsSquare a := Iff.rfl

@[simp]
theorem isSquare_toMul_iff {a : Additive α} : IsSquare (Additive.toMul a) ↔ Even a := Iff.rfl

instance [DecidablePred (IsSquare : α → Prop)] : DecidablePred (Even : Additive α → Prop) :=
  fun _ => decidable_of_iff _ isSquare_toMul_iff

end Mul

section Add
variable [Add α]

@[simp]
theorem isSquare_ofAdd_iff {a : α} : IsSquare (Multiplicative.ofAdd a) ↔ Even a := Iff.rfl

@[simp]
theorem even_toAdd_iff {a : Multiplicative α} :
    Even (Multiplicative.toAdd a) ↔ IsSquare a := Iff.rfl

instance [DecidablePred (Even : α → Prop)] : DecidablePred (IsSquare : Multiplicative α → Prop) :=
  fun _ => decidable_of_iff _ even_toAdd_iff

end Add

@[to_additive (attr := simp)]
theorem isSquare_one [MulOneClass α] : IsSquare (1 : α) :=
  ⟨1, (mul_one _).symm⟩
#align is_square_one isSquare_one
#align even_zero even_zero

@[to_additive]
theorem IsSquare.map [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]
    {m : α} (f : F) :
    IsSquare m → IsSquare (f m) := by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp⟩
#align is_square.map IsSquare.map
#align even.map Even.map

section Monoid

variable [Monoid α] {n : ℕ} {a : α}


@[to_additive even_iff_exists_two_nsmul]
theorem isSquare_iff_exists_sq (m : α) : IsSquare m ↔ ∃ c, m = c ^ 2 := by simp [IsSquare, pow_two]
#align is_square_iff_exists_sq isSquare_iff_exists_sq
#align even_iff_exists_two_nsmul even_iff_exists_two_nsmul

alias ⟨IsSquare.exists_sq, isSquare_of_exists_sq⟩ := isSquare_iff_exists_sq
#align is_square.exists_sq IsSquare.exists_sq
#align is_square_of_exists_sq isSquare_of_exists_sq

attribute
  [to_additive Even.exists_two_nsmul
      "Alias of the forwards direction of `even_iff_exists_two_nsmul`."]
  IsSquare.exists_sq
#align even.exists_two_nsmul Even.exists_two_nsmul

@[to_additive]
theorem IsSquare.pow (n : ℕ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨a, rfl⟩
  exact ⟨a ^ n, (Commute.refl _).mul_pow _⟩
#align is_square.pow IsSquare.pow
#align even.nsmul Even.nsmul

/- Porting note (#10618): `simp` attribute removed because linter reports:
simp can prove this:
  by simp only [even_two, Even.nsmul']
-/
@[to_additive Even.nsmul']
theorem Even.isSquare_pow : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨n, rfl⟩ a
  exact ⟨a ^ n, pow_add _ _ _⟩
#align even.is_square_pow Even.isSquare_pow
#align even.nsmul' Even.nsmul'

/- Porting note (#10618): `simp` attribute removed because linter reports:
simp can prove this:
  by simp only [even_two, Even.is_square_pow]
-/
@[to_additive even_two_nsmul]
theorem IsSquare_sq (a : α) : IsSquare (a ^ 2) :=
  ⟨a, pow_two _⟩
#align is_square_sq IsSquare_sq
#align even_two_nsmul even_two_nsmul

variable [HasDistribNeg α]

@[simp]
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
#align even.add Even.add

variable (α)

@[simp]
theorem isSquare_zero [MulZeroClass α] : IsSquare (0 : α) :=
  ⟨0, (mul_zero _).symm⟩
#align is_square_zero isSquare_zero

variable {α}

section DivisionMonoid

variable [DivisionMonoid α] {a : α}

@[to_additive (attr := simp)]
theorem isSquare_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← isSquare_op_iff, ← inv_inv a]
    exact h.map (MulEquiv.inv' α)
  · exact (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm
#align is_square_inv isSquare_inv
#align even_neg even_neg

alias ⟨_, IsSquare.inv⟩ := isSquare_inv
#align is_square.inv IsSquare.inv

attribute [to_additive] IsSquare.inv
#align even.neg Even.neg

@[to_additive]
theorem IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨a, rfl⟩
  exact ⟨a ^ n, (Commute.refl _).mul_zpow _⟩
#align is_square.zpow IsSquare.zpow
#align even.zsmul Even.zsmul

variable [HasDistribNeg α] {n : ℤ}

theorem Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  exact zpow_bit0_neg _ _
#align even.neg_zpow Even.neg_zpow

theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
#align even.neg_one_zpow Even.neg_one_zpow

end DivisionMonoid

theorem even_abs [AddGroup α] [LinearOrder α] {a : α} : Even |a| ↔ Even a := by
  cases abs_choice a
  · have h : abs a = a := by assumption
    simp only [h, even_neg]
  · have h : abs a = -a := by assumption
    simp only [h, even_neg]
#align even_abs even_abs

@[to_additive]
theorem IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv
#align is_square.div IsSquare.div
#align even.sub Even.sub

@[to_additive (attr := simp) Even.zsmul']
theorem Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨n, rfl⟩ a
  exact ⟨a ^ n, zpow_add _ _ _⟩
#align even.is_square_zpow Even.isSquare_zpow
#align even.zsmul' Even.zsmul'

-- `Odd.tsub` requires `CanonicallyLinearOrderedSemiring`, which we don't have
theorem Even.tsub [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine' ⟨a - b, _⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm
#align even.tsub Even.tsub

set_option linter.deprecated false in
theorem even_iff_exists_bit0 [Add α] {a : α} : Even a ↔ ∃ b, a = bit0 b :=
  Iff.rfl
#align even_iff_exists_bit0 even_iff_exists_bit0

alias ⟨Even.exists_bit0, _⟩ := even_iff_exists_bit0
#align even.exists_bit0 Even.exists_bit0

section Semiring

variable [Semiring α] [Semiring β] {a b : α} {n : ℕ}

theorem even_iff_exists_two_mul (a : α) : Even a ↔ ∃ b, a = 2 * b := by
  simp [even_iff_exists_two_nsmul]
#align even_iff_exists_two_mul even_iff_exists_two_mul

theorem even_iff_two_dvd {a : α} : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]
#align even_iff_two_dvd even_iff_two_dvd

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd
#align even.two_dvd Even.two_dvd

theorem Even.trans_dvd (ha : Even a) (hab : a ∣ b) : Even b :=
  even_iff_two_dvd.2 <| ha.two_dvd.trans hab
#align even.trans_dvd Even.trans_dvd

theorem Dvd.dvd.even (hab : a ∣ b) (ha : Even a) : Even b :=
  ha.trans_dvd hab
#align has_dvd.dvd.even Dvd.dvd.even

@[simp]
theorem range_two_mul (α) [Semiring α] : (Set.range fun x : α => 2 * x) = { a | Even a } := by
  ext x
  simp [eq_comm, two_mul, Even]
#align range_two_mul range_two_mul

set_option linter.deprecated false in
@[simp] theorem even_bit0 (a : α) : Even (bit0 a) :=
  ⟨a, rfl⟩
#align even_bit0 even_bit0

@[simp]
theorem even_two : Even (2 : α) :=
  ⟨1, by rw [one_add_one_eq_two]⟩
#align even_two even_two

@[simp]
theorem Even.mul_left (ha : Even a) (b) : Even (b * a) :=
  ha.map (AddMonoidHom.mulLeft b)
#align even.mul_left Even.mul_left

@[simp]
theorem Even.mul_right (ha : Even a) (b) : Even (a * b) :=
  ha.map (AddMonoidHom.mulRight b)
#align even.mul_right Even.mul_right

theorem even_two_mul (a : α) : Even (2 * a) :=
  ⟨a, two_mul _⟩
#align even_two_mul even_two_mul

theorem Even.pow_of_ne_zero (ha : Even a) : ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
  | 0, a0 => (a0 rfl).elim
  | a + 1, _ => by
    rw [pow_succ]
    exact ha.mul_left _
#align even.pow_of_ne_zero Even.pow_of_ne_zero

section WithOdd

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def Odd (a : α) : Prop :=
  ∃ k, a = 2 * k + 1
#align odd Odd

set_option linter.deprecated false in
theorem odd_iff_exists_bit1 {a : α} : Odd a ↔ ∃ b, a = bit1 b :=
  exists_congr fun b => by
    rw [two_mul]
    rfl
#align odd_iff_exists_bit1 odd_iff_exists_bit1

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1
#align odd.exists_bit1 Odd.exists_bit1

set_option linter.deprecated false in
@[simp] theorem odd_bit1 (a : α) : Odd (bit1 a) :=
  odd_iff_exists_bit1.2 ⟨a, rfl⟩
#align odd_bit1 odd_bit1

@[simp]
theorem range_two_mul_add_one (α : Type*) [Semiring α] :
    (Set.range fun x : α => 2 * x + 1) = { a | Odd a } := by
  ext x
  simp [Odd, eq_comm]
#align range_two_mul_add_one range_two_mul_add_one

theorem Even.add_odd : Even a → Odd b → Odd (a + b) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, by rw [mul_add, ← two_mul, add_assoc]⟩
#align even.add_odd Even.add_odd

theorem Even.odd_add : Even a → Odd b → Odd (b + a) :=
  fun he ho ↦ by simp only [he.add_odd ho, add_comm b a]

theorem Odd.add_even (ha : Odd a) (hb : Even b) : Odd (a + b) := by
  rw [add_comm]
  exact hb.add_odd ha
#align odd.add_even Odd.add_even

theorem Odd.add_odd : Odd a → Odd b → Even (a + b) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  refine' ⟨n + m + 1, _⟩
  rw [two_mul, two_mul]
  ac_rfl
#align odd.add_odd Odd.add_odd

@[simp]
theorem odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
#align odd_one odd_one

@[simp] lemma Even.add_one (h : Even a) : Odd (a + 1) := h.add_odd odd_one

@[simp] lemma Even.one_add (h : Even a) : Odd (1 + a) := h.odd_add odd_one

theorem odd_two_mul_add_one (a : α) : Odd (2 * a + 1) :=
  ⟨a, rfl⟩
#align odd_two_mul_add_one odd_two_mul_add_one

@[simp] lemma odd_add_self_one' : Odd (a + (a + 1)) := by simp [← add_assoc]

@[simp] lemma odd_add_one_self : Odd (a + 1 + a) := by simp [add_comm _ a]

@[simp] lemma odd_add_one_self' : Odd (a + (1 + a)) := by simp [add_comm 1 a]

@[simp] lemma one_add_self_self : Odd (1 + a + a) := by simp [add_comm 1 a]

theorem Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a → Odd (f a) := by
  rintro ⟨m, rfl⟩
  exact ⟨f m, by simp [two_mul]⟩
#align odd.map Odd.map

@[simp]
theorem Odd.mul : Odd a → Odd b → Odd (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  refine' ⟨2 * a * b + b + a, _⟩
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
#align odd.mul Odd.mul

theorem Odd.pow (ha : Odd a) : ∀ {n : ℕ}, Odd (a ^ n)
  | 0 => by
    rw [pow_zero]
    exact odd_one
  | a + 1 => by
    rw [pow_succ]
    exact (Odd.pow ha).mul ha
#align odd.pow Odd.pow

lemma Odd.pow_add_pow_eq_zero [IsCancelAdd α] (hn : Odd n) (hab : a + b = 0) :
    a ^ n + b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  induction' k with k ih
  · simpa
  have : a ^ 2 = b ^ 2 := add_right_cancel $
    calc
      a ^ 2 + a * b = 0 := by rw [sq, ← mul_add, hab, mul_zero]
      _ = b ^ 2 + a * b := by rw [sq, ← add_mul, add_comm, hab, zero_mul]
  refine add_right_cancel (b := b ^ (2 * k + 1) * a ^ 2) ?_
  calc
    _ = (a ^ (2 * k + 1) + b ^ (2 * k + 1)) * a ^ 2 + b ^ (2 * k + 3) := by
      rw [add_mul, ← pow_add, add_right_comm]; rfl
    _ = _ := by rw [ih, zero_mul, zero_add, zero_add, this, ← pow_add]

end WithOdd

end Semiring

section Monoid

variable [Monoid α] [HasDistribNeg α] {a : α} {n : ℕ}

theorem Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a
  simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
#align odd.neg_pow Odd.neg_pow

@[simp]
theorem Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]
#align odd.neg_one_pow Odd.neg_one_pow

end Monoid

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α]

-- this holds more generally in a `CanonicallyOrderedAddCommMonoid` if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
theorem Odd.pos [Nontrivial α] {a : α} (hn : Odd a) : 0 < a := by
  obtain ⟨k, rfl⟩ := hn
  rw [pos_iff_ne_zero, Ne, add_eq_zero_iff, not_and']
  exact fun h => (one_ne_zero h).elim
#align odd.pos Odd.pos

end CanonicallyOrderedCommSemiring

section Ring

variable [Ring α] {a b : α} {n : ℕ}

/- Porting note (#10618): attribute `simp` removed based on linter report
simp can prove this:
  by simp only [even_neg, even_two]
-/
-- @[simp]
theorem even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
#align even_neg_two even_neg_two

theorem Odd.neg (ha : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := ha
  use -(k + 1)
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right, ←
    neg_add, hk]
#align odd.neg Odd.neg

@[simp]
theorem odd_neg : Odd (-a) ↔ Odd a :=
  ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩
#align odd_neg odd_neg

/- Porting note (#10618): attribute `simp` removed based on linter report
simp can prove this:
  by simp only [odd_neg, odd_one]
-/
-- @[simp]
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
  cases' abs_choice a with h h <;> simp only [h, odd_neg]
#align odd_abs odd_abs

end Ring

section Powers

/-!
### Lemmas for canonically linear ordered semirings or linear ordered rings

The slightly unusual typeclass assumptions `[LinearOrderedSemiring R] [ExistsAddOfLE R]` cover two
more familiar settings:
* `[LinearOrderedRing R]`, eg `ℤ`, `ℚ` or `ℝ`
* `[CanonicallyLinearOrderedSemiring R]` (although we don't actually have this typeclass), eg `ℕ`,
  `ℚ≥0` or `ℝ≥0`
-/

section LinearOrderedSemiring
variable [LinearOrderedSemiring R] [ExistsAddOfLE R] {a b : R} {n : ℕ}

theorem Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add]; exact mul_self_nonneg _
#align even.pow_nonneg Even.pow_nonneg

theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n :=
  (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)
#align even.pow_pos Even.pow_pos

theorem Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (pow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  exact mul_neg_of_pos_of_neg ((even_two_mul _).pow_pos ha.ne) ha
#align odd.pow_neg_iff Odd.pow_neg_iff

theorem Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff
#align odd.pow_nonneg_iff Odd.pow_nonneg_iff

theorem Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.pow_neg_iff, pow_eq_zero_iff]
  rintro rfl; simp [Odd, eq_comm (a := 0)] at hn
#align odd.pow_nonpos_iff Odd.pow_nonpos_iff

theorem Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff
#align odd.pow_pos_iff Odd.pow_pos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
#align odd.pow_nonpos Odd.pow_nonpos

alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff
#align odd.pow_neg Odd.pow_neg

theorem Even.pow_pos_iff (hn : Even n) (h₀ : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 :=
  ⟨fun h ha => by
    rw [ha, zero_pow h₀] at h
    exact lt_irrefl 0 h, hn.pow_pos⟩
#align even.pow_pos_iff Even.pow_pos_iff

lemma Odd.strictMono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  have hn₀ : n ≠ 0 := by rintro rfl; simp [Odd, eq_comm (a := 0)] at hn
  intro a b hab
  obtain ha | ha := le_total 0 a
  · exact pow_lt_pow_left hab ha hn₀
  obtain hb | hb := lt_or_le 0 b
  · exact (hn.pow_nonpos ha).trans_lt (pow_pos hb _)
  obtain ⟨c, hac⟩ := exists_add_of_le ha
  obtain ⟨d, hbd⟩ := exists_add_of_le hb
  have hd := nonneg_of_le_add_right (hb.trans_eq hbd)
  refine lt_of_add_lt_add_right (a := c ^ n + d ^ n) ?_
  dsimp
  calc
    a ^ n + (c ^ n + d ^ n) = d ^ n := by
      rw [← add_assoc, hn.pow_add_pow_eq_zero hac.symm, zero_add]
    _ < c ^ n := pow_lt_pow_left ?_ hd hn₀
    _ = b ^ n + (c ^ n + d ^ n) := by rw [add_left_comm, hn.pow_add_pow_eq_zero hbd.symm, add_zero]
  refine lt_of_add_lt_add_right (a := a + b) ?_
  rwa [add_rotate', ← hbd, add_zero, add_left_comm, ← add_assoc, ← hac, zero_add]
#align odd.strict_mono_pow Odd.strictMono_pow

end LinearOrderedSemiring

section LinearOrderedRing
variable [LinearOrderedRing R] {a : R} {n : ℕ}

theorem Even.pow_abs {p : ℕ} (hp : Even p) (a : R) : |a| ^ p = a ^ p := by
  rw [← abs_pow, abs_eq_self]
  exact hp.pow_nonneg _
#align even.pow_abs Even.pow_abs

set_option linter.deprecated false in
@[simp]
theorem pow_bit0_abs (a : R) (p : ℕ) : |a| ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).pow_abs _
#align pow_bit0_abs pow_bit0_abs

end LinearOrderedRing

end Powers
