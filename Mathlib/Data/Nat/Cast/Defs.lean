/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.NeZero

#align_import data.nat.cast.defs from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`AddMonoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `natCast : ℕ → R` field.

Preferentially, the homomorphism is written as the coercion `Nat.cast`.

## Main declarations

* `NatCast`: Type class for `Nat.cast`.
* `AddMonoidWithOne`: Type class for which `Nat.cast` is a canonical monoid homomorphism from `ℕ`.
* `Nat.cast`: Canonical homomorphism `ℕ → R`.
-/

set_option autoImplicit true

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
#align nat.unary_cast Nat.unaryCast

#align has_nat_cast NatCast
#align has_nat_cast.nat_cast NatCast.natCast

#align nat.cast Nat.cast

-- the following four declarations are not in mathlib3 and are relevant to the way numeric
-- literals are handled in Lean 4.

/-- A type class for natural numbers which are greater than or equal to `2`. -/
class Nat.AtLeastTwo (n : ℕ) : Prop where
  prop : n ≥ 2

instance instNatAtLeastTwo : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ $ Nat.succ_le_succ $ Nat.zero_le _

/-- Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`. This
instance is what makes things like `37 : R` type check.  Note that `0` and `1` are not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidWithOne`) through
`Zero` and `One`, respectively. -/
@[nolint unusedArguments]
instance instOfNat [NatCast R] [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n.cast

@[simp, norm_cast] theorem Nat.cast_ofNat [NatCast R] [Nat.AtLeastTwo n] :
  (Nat.cast (no_index (OfNat.ofNat n)) : R) = OfNat.ofNat n := rfl

theorem Nat.cast_eq_ofNat [NatCast R] [Nat.AtLeastTwo n] : (Nat.cast n : R) = OfNat.ofNat n := rfl

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type u) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl
#align add_monoid_with_one AddMonoidWithOne
#align add_monoid_with_one.to_has_nat_cast AddMonoidWithOne.toNatCast
#align add_monoid_with_one.to_add_monoid AddMonoidWithOne.toAddMonoid
#align add_monoid_with_one.to_has_one AddMonoidWithOne.toOne
#align add_monoid_with_one.nat_cast_zero AddMonoidWithOne.natCast_zero
#align add_monoid_with_one.nat_cast_succ AddMonoidWithOne.natCast_succ

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.  -/
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R
#align add_comm_monoid_with_one AddCommMonoidWithOne
#align add_comm_monoid_with_one.to_add_monoid_with_one AddCommMonoidWithOne.toAddMonoidWithOne
#align add_comm_monoid_with_one.to_add_comm_monoid AddCommMonoidWithOne.toAddCommMonoid

library_note "coercion into rings"
/--
Coercions such as `Nat.castCoe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `R` should be set up as follows:
```lean
instance : CoeTail ℕ R where coe := ...
instance : CoeHTCT ℕ R where coe := ...
```

It needs to be `CoeTail` instead of `Coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
Sometimes we also need to declare the `CoeHTCT` instance
if we need to shadow another coercion
(e.g. `Nat.cast` should be used over `Int.ofNat`).
-/

namespace Nat
variable [AddMonoidWithOne R]

@[simp, norm_cast]
theorem cast_zero : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
#align nat.cast_zero Nat.cast_zero

-- Lemmas about `Nat.succ` need to get a low priority, so that they are tried last.
-- This is because `Nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp 500, norm_cast 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _
#align nat.cast_succ Nat.cast_succ

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _
#align nat.cast_add_one Nat.cast_add_one

@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) :
    ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl
  -- ⊢ ↑m = ↑m
                -- 🎉 no goals
                -- 🎉 no goals
#align nat.cast_ite Nat.cast_ite

end Nat

namespace Nat

@[simp, norm_cast]
theorem cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by
  rw [cast_succ, Nat.cast_zero, zero_add]
  -- 🎉 no goals
#align nat.cast_one Nat.cast_oneₓ

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n <;> simp [add_succ, add_assoc, Nat.add_zero, Nat.cast_one, Nat.cast_zero, *]
  -- ⊢ ↑(m + zero) = ↑m + ↑zero
                  -- 🎉 no goals
                  -- 🎉 no goals
#align nat.cast_add Nat.cast_addₓ

/-- Computationally friendlier cast than `Nat.unaryCast`, using binary representation. -/
protected def binCast [Zero R] [One R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0
    then (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2))
    else (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2)) + 1
decreasing_by (exact Nat.div_lt_self (Nat.succ_pos n) (Nat.le_refl 2))
               -- 🎉 no goals
               -- 🎉 no goals
               -- 🎉 no goals
               -- 🎉 no goals
#align nat.bin_cast Nat.binCast

@[simp]
theorem binCast_eq [AddMonoidWithOne R] (n : ℕ) : (Nat.binCast n : R) = ((n : ℕ) : R) := by
  apply Nat.strongInductionOn n
  -- ⊢ ∀ (n : ℕ), (∀ (m : ℕ), m < n → Nat.binCast m = ↑m) → Nat.binCast n = ↑n
  intros k hk
  -- ⊢ Nat.binCast k = ↑k
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · rw [←Nat.mod_add_div (succ k) 2]
        rw [if_pos h, hk _ $ Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ←Nat.cast_add]
        rw [Nat.succ_eq_add_one, h, Nat.zero_add, Nat.succ_mul, Nat.one_mul]
      · rw [←Nat.mod_add_div (succ k) 2]
        rw [if_neg h, hk _ $ Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ←Nat.cast_add]
        have h1 := Or.resolve_left (Nat.mod_two_eq_zero_or_one (succ k)) h
        rw [h1, Nat.add_comm 1, Nat.succ_mul, Nat.one_mul]
        simp only [Nat.cast_add, Nat.cast_one]
#align nat.bin_cast_eq Nat.binCast_eq

section deprecated
set_option linter.deprecated false

@[norm_cast, deprecated]
theorem cast_bit0 [AddMonoidWithOne R] (n : ℕ) : ((bit0 n : ℕ) : R) = bit0 (n : R) :=
  Nat.cast_add _ _
#align nat.cast_bit0 Nat.cast_bit0

@[norm_cast, deprecated]
theorem cast_bit1 [AddMonoidWithOne R] (n : ℕ) : ((bit1 n : ℕ) : R) = bit1 (n : R) := by
  rw [bit1, cast_add_one, cast_bit0]; rfl
  -- ⊢ bit0 ↑n + 1 = bit1 ↑n
                                      -- 🎉 no goals
#align nat.cast_bit1 Nat.cast_bit1

end deprecated

theorem cast_two [AddMonoidWithOne R] : ((2 : ℕ) : R) = (2 : R) := rfl
#align nat.cast_two Nat.cast_two

attribute [simp, norm_cast] Int.natAbs_ofNat

end Nat

/-- `AddMonoidWithOne` implementation using unary recursion. -/
@[reducible]
protected def AddMonoidWithOne.unary {R : Type*} [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }
#align add_monoid_with_one.unary AddMonoidWithOne.unary

/-- `AddMonoidWithOne` implementation using binary recursion. -/
@[reducible]
protected def AddMonoidWithOne.binary {R : Type*} [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast, Nat.cast],
                       -- 🎉 no goals
    natCast_succ := fun n => by
      dsimp only [NatCast.natCast]
      -- ⊢ Nat.binCast (n + 1) = Nat.binCast n + 1
      letI : AddMonoidWithOne R := AddMonoidWithOne.unary
      -- ⊢ Nat.binCast (n + 1) = Nat.binCast n + 1
      rw [Nat.binCast_eq, Nat.binCast_eq, Nat.cast_succ] }
      -- 🎉 no goals
#align add_monoid_with_one.binary AddMonoidWithOne.binary

namespace NeZero

lemma natCast_ne (n : ℕ) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] :
  (n : R) ≠ 0 := h.out
#align ne_zero.nat_cast_ne NeZero.natCast_ne

lemma of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [h : NeZero (n : R)] : NeZero n :=
  ⟨by rintro rfl; exact h.out Nat.cast_zero⟩
      -- ⊢ False
                  -- 🎉 no goals
#align ne_zero.of_ne_zero_coe NeZero.of_neZero_natCast

lemma pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : ℕ} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_neZero_natCast R).out
#align ne_zero.pos_of_ne_zero_coe NeZero.pos_of_neZero_natCast

end NeZero

theorem one_add_one_eq_two [AddMonoidWithOne α] : 1 + 1 = (2 : α) := by
  rw [←Nat.cast_one, ←Nat.cast_add]
  -- ⊢ ↑(1 + 1) = 2
  apply congrArg
  -- ⊢ 1 + 1 = 2
  decide
  -- 🎉 no goals
#align one_add_one_eq_two one_add_one_eq_two

theorem two_add_one_eq_three [AddMonoidWithOne α] : 2 + 1 = (3 : α) := by
  rw [←one_add_one_eq_two, ←Nat.cast_one, ←Nat.cast_add, ←Nat.cast_add]
  -- ⊢ ↑(1 + 1 + 1) = 3
  apply congrArg
  -- ⊢ 1 + 1 + 1 = 3
  decide
  -- 🎉 no goals

theorem three_add_one_eq_four [AddMonoidWithOne α] : 3 + 1 = (4 : α) := by
  rw [←two_add_one_eq_three, ←one_add_one_eq_two, ←Nat.cast_one,
    ←Nat.cast_add, ←Nat.cast_add, ←Nat.cast_add]
  apply congrArg
  -- ⊢ 1 + 1 + 1 + 1 = 4
  decide
  -- 🎉 no goals
