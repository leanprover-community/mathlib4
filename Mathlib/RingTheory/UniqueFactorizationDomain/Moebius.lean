/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# The Moebius function on a unique factorization monoid

We define the Moebius function on a unique factorization monoid.

## Main definitions

* `UniqueFactorizationMonoid.moebius`: The Moebius function on a unique factorization monoid,
  defined to be `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise.

## Main statements

* `IsRelPrime.moebius_mul`: The Moebius function is a multiplicative function.
-/

@[expose] public section

namespace UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a b : α}

/-- The Moebius function on a unique factorization monoid, defined to be
  `((-1) ^ (factors a).card)` if `a` is squarefree and `0` otherwise. -/
noncomputable def moebius (a : α) : ℤ :=
  open Classical in
  if Squarefree a then ((-1) ^ (factors a).card) else 0

-- Todo: prove `Int.moebius_eq` as well.
theorem _root_.Nat.moebius_eq (n : ℕ) : moebius n = ArithmeticFunction.moebius n := by
  rw [moebius]
  congr
  simp [Nat.factors_eq, ArithmeticFunction.cardFactors_apply]

@[simp]
theorem _root_.Squarefree.moebius_eq (ha : Squarefree a) : moebius a = (-1) ^ (factors a).card :=
  if_pos ha

@[simp]
theorem moebius_of_not_squarefree (ha : ¬ Squarefree a) : moebius a = 0 :=
  if_neg ha

theorem moebius_zero [Nontrivial α] : moebius (0 : α) = 0 := by
  simp

theorem moebius_one : moebius (1 : α) = 1 := by
  simp

theorem _root_.Associated.moebius_eq (h : Associated a b) : moebius a = moebius b := by
  rw [moebius, moebius, h.squarefree_iff, h.card_factors_eq]

theorem _root_.IsUnit.moebius_eq (ha : IsUnit a) : moebius a = 1 := by
  rw [(associated_one_iff_isUnit.mpr ha).moebius_eq, moebius_one]

theorem _root_.Irreducible.moebius_eq (ha : Irreducible a) : moebius a = -1 := by
  rw [ha.squarefree.moebius_eq, card_factors_of_irreducible ha, pow_one]

theorem _root_.IsRelPrime.moebius_mul (h : IsRelPrime a b) :
    moebius (a * b) = moebius a * moebius b := by
  rcases subsingleton_or_nontrivial α
  · rw [Subsingleton.elim a 1, moebius_one, one_mul, one_mul]
  by_cases ha : Squarefree a; swap
  · simp [ha, mt Squarefree.of_mul_left ha]
  by_cases hb : Squarefree b; swap
  · simp [hb, mt Squarefree.of_mul_right hb]
  have hab : Squarefree (a * b) := squarefree_mul_iff.mpr ⟨h, ha, hb⟩
  rw [hab.moebius_eq, Multiset.card_eq_card_of_rel (factors_mul ha.ne_zero hb.ne_zero),
    Multiset.card_add, pow_add, ha.moebius_eq, hb.moebius_eq]

end UniqueFactorizationMonoid
