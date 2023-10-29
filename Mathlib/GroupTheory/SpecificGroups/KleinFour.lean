/-
Copyright (c) 2023 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Klein Four Group

The Klein (Vierergruppe) four-group is a non-cyclic abelian group with four elements, in which
each element is self-inverse and in which composing any two of the three non-identity elements
produces the third one.

## Main definitions

* `KleinFourGroup` is the Klein four-group with elements `e`, `a`, `b`, and `c`,
  which is defined in terms of `Multiplicative ((ZMod 2) × (ZMod 2))`.

## Main results

* `KleinFourGroup_eq_DihedralGroup2` proves the Klein four-group is isomorphic to
  `DihedralGroup 2`.

## References

* https://en.wikipedia.org/wiki/Klein_four-group
* https://en.wikipedia.org/wiki/Alternating_group

## TODO

* Prove `KleinFourGroup` is isomorphic to the normal subgroup of `alternatingGroup (Fin 4)`
  with the permutation cycles `V = {(), (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)}`.  This is the kernel
  of the surjection of `alternatingGroup (Fin 4)` onto `alternatingGroup (Fin 3) ≃ (ZMod 3)`.
  In other words, we have the exact sequence `V → A₄ → A₃`.

* The outer automorphism group of `A₆` is the Klein four-group `V = (ZMod 2) × (ZMod 2)`,
  and is related to the outer automorphism of `S₆`. The extra outer automorphism in `A₆`
  swaps the 3-cycles (like `(1 2 3)`) with elements of shape `3²` (like `(1 2 3)(4 5 6)`).

## Tags
non-cyclic abelian group
-/

/-- Klein four-group. -/
abbrev KleinFourGroup := Multiplicative (ZMod 2 × ZMod 2)

namespace KleinFourGroup

open DihedralGroup Equiv

/-- Element `e` of Klein four-group. -/
def e : KleinFourGroup := 1

/-- Element `a` of Klein four-group. -/
def a : KleinFourGroup := Multiplicative.ofAdd (0, 1)

/-- Element `b` of Klein four-group. -/
def b : KleinFourGroup := Multiplicative.ofAdd (1, 0)

/-- Element `c` of Klein four-group. -/
def c : KleinFourGroup := Multiplicative.ofAdd (1, 1)

/-- Klein four-group is a group of order 4. -/
theorem card : Fintype.card KleinFourGroup = 4 :=
  rfl

/-- Klein four-group is a group of order 4. -/
theorem nat_card : Nat.card KleinFourGroup = 4 := by
  simp only [Nat.card_eq_fintype_card]

@[simp] theorem a_order_two : a ^ 2 = 1 :=
  rfl

@[simp] theorem b_order_two : b ^ 2 = 1 :=
  rfl

@[simp] theorem c_order_two : c ^ 2 = 1 :=
  rfl

@[simp] theorem orderOf_a : orderOf a = 2 := by
  apply orderOf_eq_prime
  · exact a_order_two
  · intro ha
    rw [a] at ha
    simp only [ofAdd_eq_one] at ha

@[simp] theorem orderOf_b : orderOf b = 2 := by
  apply orderOf_eq_prime
  · exact b_order_two
  · intro hb
    rw [b] at hb
    simp only [ofAdd_eq_one] at hb

@[simp] theorem orderOf_c : orderOf c = 2 := by
  apply orderOf_eq_prime
  · exact c_order_two
  · intro hc
    rw [c] at hc
    simp only [ofAdd_eq_one] at hc

theorem exponent : Monoid.exponent KleinFourGroup = 2 := by
  have : Monoid.exponent KleinFourGroup = lcm 2 2 := by
    apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      simp only [lcm_same, normalize_apply, normUnit_eq_one, Units.val_one, mul_one]
      intro k
      match k with
      | (0, 0) => rfl
      | (0, 1) => rfl
      | (1, 0) => rfl
      | (1, 1) => rfl
    · apply lcm_dvd
      repeat {convert Monoid.order_dvd_exponent a; exact orderOf_a.symm}
  assumption

/-- Klein four-group is a non-cyclic group. -/
theorem notIsCyclic : ¬ IsCyclic KleinFourGroup := by
  intro h
  have h₁ := IsCyclic.iff_exponent_eq_card.mp h
  rw [exponent,card] at h₁
  contradiction

/-- Klein four-group is isomorphic to the Dihedral group of order 4. -/
def KleinFourGroup_eq_DihedralGroup2 : KleinFourGroup ≃* DihedralGroup 2 where
  toFun k :=
    match k with
    | (0, 0) => 1
    | (0, 1) => sr 1
    | (1, 0) => r 1
    | (1, 1) => sr 1 * r 1
  invFun d :=
    match d with
    | 1 => (0, 0)
    | sr 1 => (0, 1)
    | r 1 => (1, 0)
    | sr 1 * r 1 => (1, 1)
  left_inv k := by
    match k with
    | (0, 0) => rfl
    | (0, 1) => rfl
    | (1, 0) => rfl
    | (1, 1) => rfl
  right_inv := by simp
  map_mul' := by simp

end KleinFourGroup
