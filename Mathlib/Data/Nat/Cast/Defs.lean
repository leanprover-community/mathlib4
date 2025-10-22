/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.OfNat

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

variable {R : Type*}

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`. This
instance is what makes things like `37 : R` type check.  Note that `0` and `1` are not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidWithOne`) through
`Zero` and `One`, respectively. -/
@[nolint unusedArguments]
instance (priority := 100) instOfNatAtLeastTwo {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    OfNat R n where
  ofNat := n.cast

library_note2 «no_index around OfNat.ofNat»
/--
When writing lemmas about `OfNat.ofNat` that assume `Nat.AtLeastTwo`, the term needs to be wrapped
in `no_index` so as not to confuse `simp`, as `no_index (OfNat.ofNat n)`.

Rather than referencing this library note, use `ofNat(n)` as a shorthand for
`no_index (OfNat.ofNat n)`.

Some discussion is [on Zulip here](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20Polynomial.2Ecoeff.20example/near/395438147).
-/

@[simp, norm_cast] theorem Nat.cast_ofNat {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    (Nat.cast ofNat(n) : R) = ofNat(n) := rfl

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type*) extends AddMonoid R, One R, NatCast R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`. -/
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R

library_note2 «coercion into rings»
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

-- Lemmas about `Nat.succ` need to get a low priority, so that they are tried last.
-- This is because `Nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[norm_cast 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 :=
  AddMonoidWithOne.natCast_succ _

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 :=
  cast_succ _

@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : ℕ) :
    ((ite P m n : ℕ) : R) = ite P (m : R) (n : R) := by
  split_ifs <;> rfl

end Nat

namespace Nat

@[simp, norm_cast]
theorem cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by
  rw [cast_succ, Nat.cast_zero, zero_add]

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [add_succ, cast_succ, ih, cast_succ, add_assoc]

/-- Computationally friendlier cast than `Nat.unaryCast`, using binary representation. -/
protected def binCast [Zero R] [One R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0
    then (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2))
    else (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2)) + 1

@[simp]
theorem binCast_eq [AddMonoidWithOne R] (n : ℕ) :
    (Nat.binCast n : R) = ((n : ℕ) : R) := by
  induction n using Nat.strongRecOn with | ind k hk => ?_
  cases k with
  | zero => rw [Nat.binCast, Nat.cast_zero]
  | succ k =>
      rw [Nat.binCast]
      by_cases h : (k + 1) % 2 = 0
      · conv => rhs; rw [← Nat.mod_add_div (k+1) 2]
        rw [if_pos h, hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ← Nat.cast_add]
        rw [h, Nat.zero_add, Nat.succ_mul, Nat.one_mul]
      · conv => rhs; rw [← Nat.mod_add_div (k+1) 2]
        rw [if_neg h, hk _ <| Nat.div_lt_self (Nat.succ_pos k) (Nat.le_refl 2), ← Nat.cast_add]
        have h1 := Or.resolve_left (Nat.mod_two_eq_zero_or_one (succ k)) h
        rw [h1, Nat.add_comm 1, Nat.succ_mul, Nat.one_mul]
        simp only [Nat.cast_add, Nat.cast_one]

theorem cast_two [NatCast R] : ((2 : ℕ) : R) = (2 : R) := rfl

theorem cast_three [NatCast R] : ((3 : ℕ) : R) = (3 : R) := rfl

theorem cast_four [NatCast R] : ((4 : ℕ) : R) = (4 : R) := rfl

attribute [simp, norm_cast] Int.natAbs_natCast

end Nat

/-- `AddMonoidWithOne` implementation using unary recursion. -/
protected abbrev AddMonoidWithOne.unary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with }

/-- `AddMonoidWithOne` implementation using binary recursion. -/
protected abbrev AddMonoidWithOne.binary [AddMonoid R] [One R] : AddMonoidWithOne R :=
  { ‹One R›, ‹AddMonoid R› with
    natCast := Nat.binCast,
    natCast_zero := by simp only [Nat.binCast],
    natCast_succ := fun n => by
      letI : AddMonoidWithOne R := AddMonoidWithOne.unary
      rw [Nat.binCast_eq, Nat.binCast_eq, Nat.cast_succ] }

theorem one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2 : R) := by
  rw [← Nat.cast_one, ← Nat.cast_add]
  apply congrArg
  decide

theorem two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 = (3 : R) := by
  rw [← one_add_one_eq_two, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add]
  apply congrArg
  decide

theorem three_add_one_eq_four [AddMonoidWithOne R] : 3 + 1 = (4 : R) := by
  rw [← two_add_one_eq_three, ← one_add_one_eq_two, ← Nat.cast_one,
    ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  apply congrArg
  decide

theorem two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = (4 : R) := by
  simp [← one_add_one_eq_two, ← Nat.cast_one, ← three_add_one_eq_four,
    ← two_add_one_eq_three, add_assoc]

section nsmul

@[simp] lemma nsmul_one {A} [AddMonoidWithOne A] : ∀ n : ℕ, n • (1 : A) = n
  | 0 => by simp [zero_nsmul]
  | n + 1 => by simp [succ_nsmul, nsmul_one n]

end nsmul
