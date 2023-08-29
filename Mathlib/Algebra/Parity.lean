/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Data.Nat.Cast.Basic

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
theorem isSquare_op_iff (a : α) : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨c, hc⟩ => ⟨unop c, by rw [← unop_mul, ← hc, unop_op]⟩, fun ⟨c, hc⟩ => by simp [hc]⟩
                              -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align is_square_op_iff isSquare_op_iff
#align even_op_iff even_op_iff

end Mul

@[to_additive (attr := simp)]
theorem isSquare_one [MulOneClass α] : IsSquare (1 : α) :=
  ⟨1, (mul_one _).symm⟩
#align is_square_one isSquare_one
#align even_zero even_zero

@[to_additive]
theorem IsSquare.map [MulOneClass α] [MulOneClass β] [MonoidHomClass F α β] {m : α} (f : F) :
    IsSquare m → IsSquare (f m) := by
  rintro ⟨m, rfl⟩
  -- ⊢ IsSquare (↑f (m * m))
  exact ⟨f m, by simp⟩
  -- 🎉 no goals
#align is_square.map IsSquare.map
#align even.map Even.map

section Monoid

variable [Monoid α] {n : ℕ} {a : α}


@[to_additive even_iff_exists_two_nsmul]
theorem isSquare_iff_exists_sq (m : α) : IsSquare m ↔ ∃ c, m = c ^ 2 := by simp [IsSquare, pow_two]
                                                                           -- 🎉 no goals
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
  -- ⊢ IsSquare ((a * a) ^ n)
  exact ⟨a ^ n, (Commute.refl _).mul_pow _⟩
  -- 🎉 no goals
#align is_square.pow IsSquare.pow
#align even.nsmul Even.nsmul

/- Porting note: `simp` attribute removed because linter reports:
simp can prove this:
  by simp only [even_two, Even.nsmul']
-/
@[to_additive Even.nsmul']
theorem Even.isSquare_pow : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨n, rfl⟩ a
  -- ⊢ IsSquare (a ^ (n + n))
  exact ⟨a ^ n, pow_add _ _ _⟩
  -- 🎉 no goals
#align even.is_square_pow Even.isSquare_pow
#align even.nsmul' Even.nsmul'

/- Porting note: `simp` attribute removed because linter reports:
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
  -- ⊢ (-a) ^ (c + c) = a ^ (c + c)
  simp_rw [← two_mul, pow_mul, neg_sq]
  -- 🎉 no goals
#align even.neg_pow Even.neg_pow

theorem Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]
                                                               -- 🎉 no goals
#align even.neg_one_pow Even.neg_one_pow

end Monoid

@[to_additive]
theorem IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  -- ⊢ IsSquare (a * a * (b * b))
  exact ⟨a * b, mul_mul_mul_comm _ _ _ _⟩
  -- 🎉 no goals
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
  -- ⊢ IsSquare a
  · rw [← isSquare_op_iff, ← inv_inv a]
    -- ⊢ IsSquare (op a⁻¹⁻¹)
    exact h.map (MulEquiv.inv' α)
    -- 🎉 no goals
  · exact ((isSquare_op_iff a).mpr h).map (MulEquiv.inv' α).symm
    -- 🎉 no goals
#align is_square_inv isSquare_inv
#align even_neg even_neg

alias ⟨_, IsSquare.inv⟩ := isSquare_inv
#align is_square.inv IsSquare.inv

attribute [to_additive] IsSquare.inv
#align even.neg Even.neg

@[to_additive]
theorem IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨a, rfl⟩
  -- ⊢ IsSquare ((a * a) ^ n)
  exact ⟨a ^ n, (Commute.refl _).mul_zpow _⟩
  -- 🎉 no goals
#align is_square.zpow IsSquare.zpow
#align even.zsmul Even.zsmul

variable [HasDistribNeg α] {n : ℤ}

theorem Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a
  -- ⊢ (-a) ^ (c + c) = a ^ (c + c)
  exact zpow_bit0_neg _ _
  -- 🎉 no goals
#align even.neg_zpow Even.neg_zpow

theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]
                                                                -- 🎉 no goals
#align even.neg_one_zpow Even.neg_one_zpow

end DivisionMonoid

theorem even_abs [SubtractionMonoid α] [LinearOrder α] {a : α} : Even |a| ↔ Even a := by
  cases abs_choice a
  -- ⊢ Even |a| ↔ Even a
  · have h : abs a = a := by assumption
    -- ⊢ Even |a| ↔ Even a
    simp only [h, even_neg]
    -- 🎉 no goals
  · have h : abs a = -a := by assumption
    -- ⊢ Even |a| ↔ Even a
    simp only [h, even_neg]
    -- 🎉 no goals
#align even_abs even_abs

@[to_additive]
theorem IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by
  rw [div_eq_mul_inv]
  -- ⊢ IsSquare (a * b⁻¹)
  exact ha.mul hb.inv
  -- 🎉 no goals
#align is_square.div IsSquare.div
#align even.sub Even.sub

@[to_additive (attr := simp) Even.zsmul']
theorem Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨n, rfl⟩ a
  -- ⊢ IsSquare (a ^ (n + n))
  exact ⟨a ^ n, zpow_add _ _ _⟩
  -- 🎉 no goals
#align even.is_square_zpow Even.isSquare_zpow
#align even.zsmul' Even.zsmul'

-- `Odd.tsub` requires `CanonicallyLinearOrderedSemiring`, which we don't have
theorem Even.tsub [CanonicallyLinearOrderedAddMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  -- ⊢ Even (a + a - n)
  obtain ⟨b, rfl⟩ := hn
  -- ⊢ Even (a + a - (b + b))
  refine' ⟨a - b, _⟩
  -- ⊢ a + a - (b + b) = a - b + (a - b)
  obtain h | h := le_total a b
  -- ⊢ a + a - (b + b) = a - b + (a - b)
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
    -- 🎉 no goals
  · exact (tsub_add_tsub_comm h h).symm
    -- 🎉 no goals
#align even.tsub Even.tsub

set_option linter.deprecated false in
theorem even_iff_exists_bit0 [Add α] {a : α} : Even a ↔ ∃ b, a = bit0 b :=
  Iff.rfl
#align even_iff_exists_bit0 even_iff_exists_bit0

alias ⟨Even.exists_bit0, _⟩ := even_iff_exists_bit0
#align even.exists_bit0 Even.exists_bit0

section Semiring

variable [Semiring α] [Semiring β] {m n : α}

theorem even_iff_exists_two_mul (m : α) : Even m ↔ ∃ c, m = 2 * c := by
  simp [even_iff_exists_two_nsmul]
  -- 🎉 no goals
#align even_iff_exists_two_mul even_iff_exists_two_mul

theorem even_iff_two_dvd {a : α} : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]
                                                        -- 🎉 no goals
#align even_iff_two_dvd even_iff_two_dvd

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd
#align even.two_dvd Even.two_dvd

theorem Even.trans_dvd (hm : Even m) (hn : m ∣ n) : Even n :=
  even_iff_two_dvd.2 <| hm.two_dvd.trans hn
#align even.trans_dvd Even.trans_dvd

theorem Dvd.dvd.even (hn : m ∣ n) (hm : Even m) : Even n :=
  hm.trans_dvd hn
#align has_dvd.dvd.even Dvd.dvd.even

@[simp]
theorem range_two_mul (α) [Semiring α] : (Set.range fun x : α => 2 * x) = { a | Even a } := by
  ext x
  -- ⊢ (x ∈ Set.range fun x => 2 * x) ↔ x ∈ {a | Even a}
  simp [eq_comm, two_mul, Even]
  -- 🎉 no goals
#align range_two_mul range_two_mul

set_option linter.deprecated false in
@[simp] theorem even_bit0 (a : α) : Even (bit0 a) :=
  ⟨a, rfl⟩
#align even_bit0 even_bit0

@[simp]
theorem even_two : Even (2 : α) :=
  ⟨1, by rw[one_add_one_eq_two]⟩
         -- 🎉 no goals
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
    -- ⊢ Even (m * m ^ a)
    exact hm.mul_right _
    -- 🎉 no goals
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
    -- ⊢ a = b + b + 1 ↔ a = bit1 b
    rfl
    -- 🎉 no goals
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
  -- ⊢ (x ∈ Set.range fun x => 2 * x + 1) ↔ x ∈ {a | Odd a}
  simp [Odd, eq_comm]
  -- 🎉 no goals
#align range_two_mul_add_one range_two_mul_add_one

theorem Even.add_odd : Even m → Odd n → Odd (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  -- ⊢ Odd (m + m + (2 * n + 1))
  exact ⟨m + n, by rw [mul_add, ← two_mul, add_assoc]⟩
  -- 🎉 no goals
#align even.add_odd Even.add_odd

theorem Even.odd_add : Even m → Odd n → Odd (n + m) :=
  fun he ho ↦ by simp only [he.add_odd ho, add_comm n m]
                 -- 🎉 no goals

theorem Odd.add_even (hm : Odd m) (hn : Even n) : Odd (m + n) := by
  rw [add_comm]
  -- ⊢ Odd (n + m)
  exact hn.add_odd hm
  -- 🎉 no goals
#align odd.add_even Odd.add_even

theorem Odd.add_odd : Odd m → Odd n → Even (m + n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  -- ⊢ Even (2 * m + 1 + (2 * n + 1))
  refine' ⟨n + m + 1, _⟩
  -- ⊢ 2 * m + 1 + (2 * n + 1) = n + m + 1 + (n + m + 1)
  rw [two_mul, two_mul]
  -- ⊢ m + m + 1 + (n + n + 1) = n + m + 1 + (n + m + 1)
  ac_rfl
  -- 🎉 no goals
#align odd.add_odd Odd.add_odd

@[simp]
theorem odd_one : Odd (1 : α) :=
  ⟨0, (zero_add _).symm.trans (congr_arg (· + (1 : α)) (mul_zero _).symm)⟩
#align odd_one odd_one

@[simp] lemma Even.add_one (h : Even m) : Odd (m + 1) := h.add_odd odd_one

@[simp] lemma Even.one_add (h : Even m) : Odd (1 + m) := h.odd_add odd_one

theorem odd_two_mul_add_one (m : α) : Odd (2 * m + 1) :=
  ⟨m, rfl⟩
#align odd_two_mul_add_one odd_two_mul_add_one

@[simp] lemma odd_add_self_one' : Odd (m + (m + 1)) := by simp [← add_assoc]
                                                          -- 🎉 no goals

@[simp] lemma odd_add_one_self : Odd (m + 1 + m) := by simp [add_comm _ m]
                                                       -- 🎉 no goals

@[simp] lemma odd_add_one_self' : Odd (m + (1 + m)) := by simp [add_comm 1 m]
                                                          -- 🎉 no goals

@[simp] lemma one_add_self_self : Odd (1 + m + m) := by simp [add_comm 1 m]
                                                        -- 🎉 no goals

theorem Odd.map [RingHomClass F α β] (f : F) : Odd m → Odd (f m) := by
  rintro ⟨m, rfl⟩
  -- ⊢ Odd (↑f (2 * m + 1))
  exact ⟨f m, by simp [two_mul]⟩
  -- 🎉 no goals
#align odd.map Odd.map

@[simp]
theorem Odd.mul : Odd m → Odd n → Odd (m * n) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  -- ⊢ Odd ((2 * m + 1) * (2 * n + 1))
  refine' ⟨2 * m * n + n + m, _⟩
  -- ⊢ (2 * m + 1) * (2 * n + 1) = 2 * (2 * m * n + n + m) + 1
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← Nat.cast_two, ← Nat.cast_comm]
#align odd.mul Odd.mul

theorem Odd.pow (hm : Odd m) : ∀ {a : ℕ}, Odd (m ^ a)
  | 0 => by
    rw [pow_zero]
    -- ⊢ Odd 1
    exact odd_one
    -- 🎉 no goals
  | a + 1 => by
    rw [pow_succ]
    -- ⊢ Odd (m * m ^ a)
    exact hm.mul <| Odd.pow hm
    -- 🎉 no goals
#align odd.pow Odd.pow

end WithOdd

end Semiring

section Monoid

variable [Monoid α] [HasDistribNeg α] {a : α} {n : ℕ}

theorem Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a
  -- ⊢ (-a) ^ (2 * c + 1) = -a ^ (2 * c + 1)
  simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
  -- 🎉 no goals
#align odd.neg_pow Odd.neg_pow

@[simp]
theorem Odd.neg_one_pow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]
                                                              -- 🎉 no goals
#align odd.neg_one_pow Odd.neg_one_pow

end Monoid

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α]

-- this holds more generally in a `CanonicallyOrderedAddMonoid` if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
theorem Odd.pos [Nontrivial α] {n : α} (hn : Odd n) : 0 < n := by
  obtain ⟨k, rfl⟩ := hn
  -- ⊢ 0 < 2 * k + 1
  rw [pos_iff_ne_zero, Ne.def, add_eq_zero_iff, not_and']
  -- ⊢ 1 = 0 → ¬2 * k = 0
  exact fun h => (one_ne_zero h).elim
  -- 🎉 no goals
#align odd.pos Odd.pos

end CanonicallyOrderedCommSemiring

section Ring

variable [Ring α] {a b : α} {n : ℕ}

/- Porting note: attribute `simp` removed based on linter report
simp can prove this:
  by simp only [even_neg, even_two]
-/
-- @[simp]
theorem even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]
                                           -- 🎉 no goals
#align even_neg_two even_neg_two

theorem Odd.neg (hp : Odd a) : Odd (-a) := by
  obtain ⟨k, hk⟩ := hp
  -- ⊢ Odd (-a)
  use -(k + 1)
  -- ⊢ -a = 2 * -(k + 1) + 1
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add, neg_add_cancel_right, ←
    neg_add, hk]
#align odd.neg Odd.neg

@[simp]
theorem odd_neg : Odd (-a) ↔ Odd a :=
  ⟨fun h => neg_neg a ▸ h.neg, Odd.neg⟩
#align odd_neg odd_neg

/- Porting note: attribute `simp` removed based on linter report
simp can prove this:
  by simp only [odd_neg, odd_one]
-/
-- @[simp]
theorem odd_neg_one : Odd (-1 : α) := by simp
                                         -- 🎉 no goals
#align odd_neg_one odd_neg_one

theorem Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  -- ⊢ Odd (a + -b)
  exact ha.add_even hb.neg
  -- 🎉 no goals
#align odd.sub_even Odd.sub_even

theorem Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b) := by
  rw [sub_eq_add_neg]
  -- ⊢ Odd (a + -b)
  exact ha.add_odd hb.neg
  -- 🎉 no goals
#align even.sub_odd Even.sub_odd

theorem Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  rw [sub_eq_add_neg]
  -- ⊢ Even (a + -b)
  exact ha.add_odd hb.neg
  -- 🎉 no goals
#align odd.sub_odd Odd.sub_odd

theorem odd_abs [LinearOrder α] : Odd (abs a) ↔ Odd a := by
  cases' abs_choice a with h h <;> simp only [h, odd_neg]
  -- ⊢ Odd |a| ↔ Odd a
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align odd_abs odd_abs

end Ring

section Powers

set_option linter.deprecated false

variable [LinearOrderedRing R] {a : R} {n : ℕ}

theorem Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  cases' hn with k hk; simpa only [hk, two_mul] using pow_bit0_nonneg a k
  -- ⊢ 0 ≤ a ^ n
                       -- 🎉 no goals
#align even.pow_nonneg Even.pow_nonneg

theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := by
  cases' hn with k hk; simpa only [hk, two_mul] using pow_bit0_pos ha k
  -- ⊢ 0 < a ^ n
                       -- 🎉 no goals
#align even.pow_pos Even.pow_pos

theorem Odd.pow_nonpos (hn : Odd n) (ha : a ≤ 0) : a ^ n ≤ 0 := by
  cases' hn with k hk; simpa only [hk, two_mul] using pow_bit1_nonpos_iff.mpr ha
  -- ⊢ a ^ n ≤ 0
                       -- 🎉 no goals
#align odd.pow_nonpos Odd.pow_nonpos

theorem Odd.pow_neg (hn : Odd n) (ha : a < 0) : a ^ n < 0 := by
  cases' hn with k hk; simpa only [hk, two_mul] using pow_bit1_neg_iff.mpr ha
  -- ⊢ a ^ n < 0
                       -- 🎉 no goals
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
    -- ⊢ False
    exact lt_irrefl 0 h, hn.pow_pos⟩
    -- 🎉 no goals
#align even.pow_pos_iff Even.pow_pos_iff

theorem Even.pow_abs {p : ℕ} (hp : Even p) (a : R) : |a| ^ p = a ^ p := by
  rw [← abs_pow, abs_eq_self]
  -- ⊢ 0 ≤ a ^ p
  exact hp.pow_nonneg _
  -- 🎉 no goals
#align even.pow_abs Even.pow_abs

@[simp]
theorem pow_bit0_abs (a : R) (p : ℕ) : |a| ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).pow_abs _
#align pow_bit0_abs pow_bit0_abs

theorem Odd.strictMono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  cases' hn with k hk; simpa only [hk, two_mul] using strictMono_pow_bit1 _
  -- ⊢ StrictMono fun a => a ^ n
                       -- 🎉 no goals
#align odd.strict_mono_pow Odd.strictMono_pow

end Powers
