/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Fintype.Parity
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.FieldTheory.Finite.Basic

#align_import number_theory.legendre_symbol.quadratic_char.basic from "leanprover-community/mathlib"@"5b2fe80501ff327b9109fb09b7cc8c325cd0d7d9"

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/


/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/


section Define

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadraticCharFun_mul`.

We will later define `quadraticChar` to be a multiplicative character
of type `MulChar F ℤ`, when the domain is a finite field `F`.
-/
def quadraticCharFun (α : Type*) [MonoidWithZero α] [DecidableEq α]
    [DecidablePred (IsSquare : α → Prop)] (a : α) : ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1
#align quadratic_char_fun quadraticCharFun

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section quadraticChar

open MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Some basic API lemmas -/
theorem quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0 := by
  simp only [quadraticCharFun]
  -- ⊢ (if a = 0 then 0 else if IsSquare a then 1 else -1) = 0 ↔ a = 0
  by_cases ha : a = 0
  -- ⊢ (if a = 0 then 0 else if IsSquare a then 1 else -1) = 0 ↔ a = 0
  · simp only [ha, eq_self_iff_true, if_true]
    -- 🎉 no goals
  · simp only [ha, if_false, iff_false_iff]
    -- ⊢ ¬(if IsSquare a then 1 else -1) = 0
    split_ifs <;> simp only [neg_eq_zero, one_ne_zero, not_false_iff]
    -- ⊢ ¬1 = 0
                  -- 🎉 no goals
                  -- 🎉 no goals
#align quadratic_char_fun_eq_zero_iff quadraticCharFun_eq_zero_iff

@[simp]
theorem quadraticCharFun_zero : quadraticCharFun F 0 = 0 := by
  simp only [quadraticCharFun, eq_self_iff_true, if_true, id.def]
  -- 🎉 no goals
#align quadratic_char_fun_zero quadraticCharFun_zero

@[simp]
theorem quadraticCharFun_one : quadraticCharFun F 1 = 1 := by
  simp only [quadraticCharFun, one_ne_zero, isSquare_one, if_true, if_false, id.def]
  -- 🎉 no goals
#align quadratic_char_fun_one quadraticCharFun_one

/-- If `ringChar F = 2`, then `quadraticCharFun F` takes the value `1` on nonzero elements. -/
theorem quadraticCharFun_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = 1 := by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  -- ⊢ ¬IsSquare a → False
  exact fun h => h (FiniteField.isSquare_of_char_two hF a)
  -- 🎉 no goals
#align quadratic_char_fun_eq_one_of_char_two quadraticCharFun_eq_one_of_char_two

/-- If `ringChar F` is odd, then `quadraticCharFun F a` can be computed in
terms of `a ^ (Fintype.card F / 2)`. -/
theorem quadraticCharFun_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 := by
  simp only [quadraticCharFun, ha, if_false]
  -- ⊢ (if IsSquare a then 1 else -1) = if a ^ (Fintype.card F / 2) = 1 then 1 else …
  simp_rw [FiniteField.isSquare_iff hF ha]
  -- 🎉 no goals
#align quadratic_char_fun_eq_pow_of_char_ne_two quadraticCharFun_eq_pow_of_char_ne_two

/-- The quadratic character is multiplicative. -/
theorem quadraticCharFun_mul (a b : F) :
    quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b := by
  by_cases ha : a = 0
  -- ⊢ quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b
  · rw [ha, zero_mul, quadraticCharFun_zero, zero_mul]
    -- 🎉 no goals
  -- now `a ≠ 0`
  by_cases hb : b = 0
  -- ⊢ quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b
  · rw [hb, mul_zero, quadraticCharFun_zero, mul_zero]
    -- 🎉 no goals
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  -- ⊢ quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b
  by_cases hF : ringChar F = 2
  -- ⊢ quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b
  ·-- case `ringChar F = 2`
    rw [quadraticCharFun_eq_one_of_char_two hF ha, quadraticCharFun_eq_one_of_char_two hF hb,
      quadraticCharFun_eq_one_of_char_two hF hab, mul_one]
  · -- case of odd characteristic
    rw [quadraticCharFun_eq_pow_of_char_ne_two hF ha, quadraticCharFun_eq_pow_of_char_ne_two hF hb,
      quadraticCharFun_eq_pow_of_char_ne_two hF hab, mul_pow]
    cases' FiniteField.pow_dichotomy hF hb with hb' hb'
    -- ⊢ (if a ^ (Fintype.card F / 2) * b ^ (Fintype.card F / 2) = 1 then 1 else -1)  …
    · simp only [hb', mul_one, eq_self_iff_true, if_true]
      -- 🎉 no goals
    · have h := Ring.neg_one_ne_one_of_char_ne_two hF
      -- ⊢ (if a ^ (Fintype.card F / 2) * b ^ (Fintype.card F / 2) = 1 then 1 else -1)  …
      -- `-1 ≠ 1`
      simp only [hb', h, mul_neg, mul_one, if_false, ite_mul, neg_mul]
      -- ⊢ (if -a ^ (Fintype.card F / 2) = 1 then 1 else -1) = -if a ^ (Fintype.card F  …
      cases' FiniteField.pow_dichotomy hF ha with ha' ha' <;>
      -- ⊢ (if -a ^ (Fintype.card F / 2) = 1 then 1 else -1) = -if a ^ (Fintype.card F  …
        simp only [ha', h, neg_neg, eq_self_iff_true, if_true, if_false]
        -- 🎉 no goals
        -- 🎉 no goals
#align quadratic_char_fun_mul quadraticCharFun_mul

variable (F)

/-- The quadratic character as a multiplicative character. -/
@[simps]
def quadraticChar : MulChar F ℤ where
  toFun := quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero
                          -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := quadraticCharFun F, map_one' := (_ : …
                                                             -- 🎉 no goals
#align quadratic_char quadraticChar

variable {F}

/-- The value of the quadratic character on `a` is zero iff `a = 0`. -/
theorem quadraticChar_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0 :=
  quadraticCharFun_eq_zero_iff
#align quadratic_char_eq_zero_iff quadraticChar_eq_zero_iff

-- @[simp] -- Porting note: simp can prove this
theorem quadraticChar_zero : quadraticChar F 0 = 0 := by
  simp only [quadraticChar_apply, quadraticCharFun_zero]
  -- 🎉 no goals
#align quadratic_char_zero quadraticChar_zero

/-- For nonzero `a : F`, `quadraticChar F a = 1 ↔ IsSquare a`. -/
theorem quadraticChar_one_iff_isSquare {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ↔ IsSquare a := by
  simp only [quadraticChar_apply, quadraticCharFun, ha, (by decide : (-1 : ℤ) ≠ 1), if_false,
    ite_eq_left_iff, imp_false, Classical.not_not]
#align quadratic_char_one_iff_is_square quadraticChar_one_iff_isSquare

/-- The quadratic character takes the value `1` on nonzero squares. -/
theorem quadraticChar_sq_one' {a : F} (ha : a ≠ 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [quadraticCharFun, ha, pow_eq_zero_iff, Nat.succ_pos', IsSquare_sq, if_true, if_false,
    quadraticChar_apply]
#align quadratic_char_sq_one' quadraticChar_sq_one'

/-- The square of the quadratic character on nonzero arguments is `1`. -/
theorem quadraticChar_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a ^ 2 = 1 := by
  -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5164): was
  -- rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']
  erw [pow_two, ← map_mul (quadraticChar F) a, ← pow_two]
  -- ⊢ ↑(quadraticChar F) (a ^ 2) = 1
  apply quadraticChar_sq_one' ha
  -- 🎉 no goals
#align quadratic_char_sq_one quadraticChar_sq_one

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
theorem quadraticChar_dichotomy {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
  sq_eq_one_iff.1 <| quadraticChar_sq_one ha
#align quadratic_char_dichotomy quadraticChar_dichotomy

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
theorem quadraticChar_eq_neg_one_iff_not_one {a : F} (ha : a ≠ 0) :
    quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1 := by
  refine' ⟨fun h => _, fun h₂ => (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩
  -- ⊢ ¬↑(quadraticChar F) a = 1
  rw [h]
  -- ⊢ ¬-1 = 1
  norm_num
  -- 🎉 no goals
#align quadratic_char_eq_neg_one_iff_not_one quadraticChar_eq_neg_one_iff_not_one

/-- For `a : F`, `quadraticChar F a = -1 ↔ ¬ IsSquare a`. -/
theorem quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a := by
  by_cases ha : a = 0
  -- ⊢ ↑(quadraticChar F) a = -1 ↔ ¬IsSquare a
  · simp only [ha, isSquare_zero, MulChar.map_zero, zero_eq_neg, one_ne_zero, not_true]
    -- 🎉 no goals
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]
    -- 🎉 no goals
#align quadratic_char_neg_one_iff_not_is_square quadraticChar_neg_one_iff_not_isSquare

/-- If `F` has odd characteristic, then `quadraticChar F` takes the value `-1`. -/
theorem quadraticChar_exists_neg_one (hF : ringChar F ≠ 2) : ∃ a, quadraticChar F a = -1 :=
  (FiniteField.exists_nonsquare hF).imp fun _ h₁ => quadraticChar_neg_one_iff_not_isSquare.mpr h₁
#align quadratic_char_exists_neg_one quadraticChar_exists_neg_one

/-- If `ringChar F = 2`, then `quadraticChar F` takes the value `1` on nonzero elements. -/
theorem quadraticChar_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 :=
  quadraticCharFun_eq_one_of_char_two hF ha
#align quadratic_char_eq_one_of_char_two quadraticChar_eq_one_of_char_two

/-- If `ringChar F` is odd, then `quadraticChar F a` can be computed in
terms of `a ^ (Fintype.card F / 2)`. -/
theorem quadraticChar_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  quadraticCharFun_eq_pow_of_char_ne_two hF ha
#align quadratic_char_eq_pow_of_char_ne_two quadraticChar_eq_pow_of_char_ne_two

theorem quadraticChar_eq_pow_of_char_ne_two' (hF : ringChar F ≠ 2) (a : F) :
    (quadraticChar F a : F) = a ^ (Fintype.card F / 2) := by
  by_cases ha : a = 0
  -- ⊢ ↑(↑(quadraticChar F) a) = a ^ (Fintype.card F / 2)
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    -- ⊢ ↑(↑(quadraticChar F) a) = a ^ (Fintype.card F / 2)
    simp only [ha, zero_pow this, quadraticChar_apply, quadraticCharFun_zero, Int.cast_zero]
    -- 🎉 no goals
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    -- ⊢ ↑(if a ^ (Fintype.card F / 2) = 1 then 1 else -1) = a ^ (Fintype.card F / 2)
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
    -- ⊢ ↑(if a ^ (Fintype.card F / 2) = 1 then 1 else -1) = a ^ (Fintype.card F / 2)
    · simp only [ha', eq_self_iff_true, if_true, Int.cast_one]
      -- 🎉 no goals
    · have ha'' := Or.resolve_left (FiniteField.pow_dichotomy hF ha) ha'
      -- ⊢ ↑(if a ^ (Fintype.card F / 2) = 1 then 1 else -1) = a ^ (Fintype.card F / 2)
      simp only [ha'', Int.cast_ite, Int.cast_one, Int.cast_neg, ite_eq_right_iff]
      -- ⊢ -1 = 1 → 1 = -1
      exact Eq.symm
      -- 🎉 no goals
#align quadratic_char_eq_pow_of_char_ne_two' quadraticChar_eq_pow_of_char_ne_two'

variable (F)

/-- The quadratic character is quadratic as a multiplicative character. -/
theorem quadraticChar_isQuadratic : (quadraticChar F).IsQuadratic := by
  intro a
  -- ⊢ ↑(quadraticChar F) a = 0 ∨ ↑(quadraticChar F) a = 1 ∨ ↑(quadraticChar F) a = …
  by_cases ha : a = 0
  -- ⊢ ↑(quadraticChar F) a = 0 ∨ ↑(quadraticChar F) a = 1 ∨ ↑(quadraticChar F) a = …
  · left; rw [ha]; exact quadraticChar_zero
    -- ⊢ ↑(quadraticChar F) a = 0
          -- ⊢ ↑(quadraticChar F) 0 = 0
                   -- 🎉 no goals
  · right; exact quadraticChar_dichotomy ha
    -- ⊢ ↑(quadraticChar F) a = 1 ∨ ↑(quadraticChar F) a = -1
           -- 🎉 no goals
#align quadratic_char_is_quadratic quadraticChar_isQuadratic

variable {F}

/-- The quadratic character is nontrivial as a multiplicative character
when the domain has odd characteristic. -/
theorem quadraticChar_isNontrivial (hF : ringChar F ≠ 2) : (quadraticChar F).IsNontrivial := by
  rcases quadraticChar_exists_neg_one hF with ⟨a, ha⟩
  -- ⊢ IsNontrivial (quadraticChar F)
  have hu : IsUnit a := by by_contra hf; rw [MulChar.map_nonunit _ hf] at ha; norm_num at ha
  -- ⊢ IsNontrivial (quadraticChar F)
  refine' ⟨hu.unit, (_ : quadraticChar F a ≠ 1)⟩
  -- ⊢ ↑(quadraticChar F) a ≠ 1
  rw [ha]
  -- ⊢ -1 ≠ 1
  norm_num
  -- 🎉 no goals
#align quadratic_char_is_nontrivial quadraticChar_isNontrivial

/-- The number of solutions to `x^2 = a` is determined by the quadratic character. -/
theorem quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F) :
    ↑{x : F | x ^ 2 = a}.toFinset.card = quadraticChar F a + 1 := by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0
  -- ⊢ ↑(Finset.card (Set.toFinset {x | x ^ 2 = a})) = ↑(quadraticChar F) a + 1
  · simp only [h₀, pow_eq_zero_iff, Nat.succ_pos', Int.ofNat_succ, Int.ofNat_zero, MulChar.map_zero,
      Set.setOf_eq_eq_singleton, Set.toFinset_card, Set.card_singleton]
  · set s := {x : F | x ^ 2 = a}.toFinset
    -- ⊢ ↑(Finset.card s) = ↑(quadraticChar F) a + 1
    by_cases h : IsSquare a
    -- ⊢ ↑(Finset.card s) = ↑(quadraticChar F) a + 1
    · rw [(quadraticChar_one_iff_isSquare h₀).mpr h]
      -- ⊢ ↑(Finset.card s) = 1 + 1
      rcases h with ⟨b, h⟩
      -- ⊢ ↑(Finset.card s) = 1 + 1
      rw [h, mul_self_eq_zero] at h₀
      -- ⊢ ↑(Finset.card s) = 1 + 1
      have h₁ : s = [b, -b].toFinset := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, List.toFinset_cons,
          List.toFinset_nil, insert_emptyc_eq, Finset.mem_insert, Finset.mem_singleton]
        rw [← pow_two] at h
        simp only [h, Set.toFinset_setOf, Finset.mem_univ, Finset.mem_filter, true_and]
        constructor
        · exact eq_or_eq_neg_of_sq_eq_sq _ _
        · rintro (h₂ | h₂) <;> rw [h₂]
          simp only [neg_sq]
      norm_cast
      -- ⊢ Finset.card s = 1 + 1
      rw [h₁, List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
      -- ⊢ Finset.card (insert b (insert (-b) ∅)) = 1 + 1
      exact Finset.card_doubleton (Ne.symm (mt (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀))
      -- 🎉 no goals
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h]
      -- ⊢ ↑(Finset.card s) = -1 + 1
      simp only [Int.coe_nat_eq_zero, Finset.card_eq_zero, Set.toFinset_card, Fintype.card_ofFinset,
        Set.mem_setOf_eq, add_left_neg]
      ext x
      -- ⊢ x ∈ Set.toFinset {x | x ^ 2 = a} ↔ x ∈ ∅
      -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5026):
      -- added (Set.mem_toFinset), Set.mem_setOf
      simp only [iff_false_iff, Finset.mem_filter, Finset.mem_univ, true_and_iff,
        Finset.not_mem_empty, (Set.mem_toFinset), Set.mem_setOf]
      rw [isSquare_iff_exists_sq] at h
      -- ⊢ ¬x ^ 2 = a
      exact fun h' => h ⟨_, h'.symm⟩
      -- 🎉 no goals
#align quadratic_char_card_sqrts quadraticChar_card_sqrts

open scoped BigOperators

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
theorem quadraticChar_sum_zero (hF : ringChar F ≠ 2) : ∑ a : F, quadraticChar F a = 0 :=
  IsNontrivial.sum_eq_zero (quadraticChar_isNontrivial hF)
#align quadratic_char_sum_zero quadraticChar_sum_zero

end quadraticChar

/-!
### Special values of the quadratic character

We express `quadraticChar F (-1)` in terms of `χ₄`.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The value of the quadratic character at `-1` -/
theorem quadraticChar_neg_one [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-1) = χ₄ (Fintype.card F) := by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  -- ⊢ ↑(quadraticChar F) (-1) = ↑χ₄ ↑(Fintype.card F)
  rw [h, χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  -- ⊢ (if (-1) ^ (Fintype.card F / 2) = 1 then 1 else -1) = (-1) ^ (Fintype.card F …
  set n := Fintype.card F / 2
  -- ⊢ (if (-1) ^ n = 1 then 1 else -1) = (-1) ^ n
  cases' Nat.even_or_odd n with h₂ h₂
  -- ⊢ (if (-1) ^ n = 1 then 1 else -1) = (-1) ^ n
  · simp only [Even.neg_one_pow h₂, eq_self_iff_true, if_true]
    -- 🎉 no goals
  · simp only [Odd.neg_one_pow h₂, Ring.neg_one_ne_one_of_char_ne_two hF, ite_false]
    -- 🎉 no goals
#align quadratic_char_neg_one quadraticChar_neg_one

/-- `-1` is a square in `F` iff `#F` is not congruent to `3` mod `4`. -/
theorem FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  classical -- suggested by the linter (instead of `[DecidableEq F]`)
  by_cases hF : ringChar F = 2
  · simp only [FiniteField.isSquare_of_char_two hF, Ne.def, true_iff_iff]
    exact fun hf =>
      one_ne_zero <|
        (Nat.odd_of_mod_four_eq_three hf).symm.trans <| FiniteField.even_card_of_char_two hF
  · have h₁ := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F)),
      quadraticChar_neg_one hF, χ₄_nat_eq_if_mod_four, h₁]
    simp only [Nat.one_ne_zero, if_false, ite_eq_left_iff, Ne.def, (by decide : (-1 : ℤ) ≠ 1),
      imp_false, Classical.not_not]
    exact
      ⟨fun h => ne_of_eq_of_ne h (by decide : 1 ≠ 3), Or.resolve_right (Nat.odd_mod_four_iff.mp h₁)⟩
#align finite_field.is_square_neg_one_iff FiniteField.isSquare_neg_one_iff

end SpecialValues
