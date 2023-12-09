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

* `KleinFour` : Klein four-group with elements `e`, `a`, `b`, and `c`, which is defined
  in terms of `Multiplicative (ZMod 2 × ZMod 2)`.
* `mulEquivDihedralGroup2` : Klein four-group is isomorphic to `DihedralGroup 2`.

## References

* https://en.wikipedia.org/wiki/Klein_four-group
* https://en.wikipedia.org/wiki/Alternating_group

## TODO

* Prove `KleinFour` is isomorphic to the normal subgroup of `alternatingGroup (Fin 4)`
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
abbrev KleinFour := Multiplicative (ZMod 2 × ZMod 2)

namespace KleinFour

open DihedralGroup Equiv

/-- Element `a` of Klein four-group. -/
def a : KleinFour := Multiplicative.ofAdd (0, 1)

/-- Element `b` of Klein four-group. -/
def b : KleinFour := Multiplicative.ofAdd (1, 0)

/-- Element `c` of Klein four-group. -/
def c : KleinFour := Multiplicative.ofAdd (1, 1)

/-- Klein four-group is a group of order 4. -/
theorem card : Fintype.card KleinFour = 4 :=
  rfl

/-- Klein four-group is a group of order 4. -/
theorem nat_card : Nat.card KleinFour = 4 := by
  simp (config := {decide := true}) only [Nat.card_eq_fintype_card]

@[simp] theorem a_sq : a ^ 2 = 1 :=
  rfl

@[simp] theorem b_sq : b ^ 2 = 1 :=
  rfl

@[simp] theorem c_sq : c ^ 2 = 1 :=
  rfl

@[simp] theorem orderOf_a : orderOf a = 2 :=
  orderOf_eq_prime a_sq (by decide)

@[simp] theorem orderOf_b : orderOf b = 2 :=
  orderOf_eq_prime b_sq (by decide)

@[simp] theorem orderOf_c : orderOf c = 2 :=
  orderOf_eq_prime c_sq (by decide)

@[simp high]
theorem exponent : Monoid.exponent KleinFour = 2 := by
  simp [AddMonoid.exponent_prod]

/-- Klein four-group is a non-cyclic group. -/
theorem notIsCyclic : ¬ IsCyclic KleinFour := by
  intro h
  have h₁ := IsCyclic.iff_exponent_eq_card.mp h
  rw [exponent, card] at h₁
  contradiction

/-- Klein four-group is isomorphic to the Dihedral group of order 4. -/
@[simps]
def mulEquivDihedralGroupTwo : KleinFour ≃* DihedralGroup 2 where
  toFun := fun
    | (0, 0) => 1
    | (0, 1) => sr 1
    | (1, 0) => r 1
    | (1, 1) => sr 1 * r 1
  invFun := fun
    | 1 => (0, 0)
    | sr 1 => (0, 1)
    | r 1 => (1, 0)
    | sr 1 * r 1 => (1, 1)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by simp (config := {decide := true})

end KleinFour
