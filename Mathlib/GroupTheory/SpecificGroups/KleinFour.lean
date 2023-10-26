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

* `KleinFourGroup` is the Klein four-group with elements `e`, `a`, `b`, and `c`.

## Main results

* `KleinFourGroup_eq_DihedralGroup2` proves the Klein four-group is `MulEquiv` to
  `DihedralGroup 2`.
* `KleinFourGroup_eq_ProdZMod2` proves the Klein four-group is `Equiv` to the direct
  product `(ZMod 2) × (ZMod 2)`.

## References

* https://en.wikipedia.org/wiki/Klein_four-group

## Tags
non-cyclic abelian group
-/

/-- Klein four-group. -/
inductive KleinFourGroup : Type
  | e : KleinFourGroup
  | a : KleinFourGroup
  | b : KleinFourGroup
  | c : KleinFourGroup
  deriving DecidableEq

namespace KleinFourGroup

open DihedralGroup Equiv

/-- Multiplication of the Klein four-group. -/
private def mul : KleinFourGroup → KleinFourGroup → KleinFourGroup
  | e, x => x
  | x, e => x
  | a, a => e
  | a, b => c
  | a, c => b
  | b, a => c
  | b, b => e
  | b, c => a
  | c, a => b
  | c, b => a
  | c, c => e

/-- `1` is the identity matrix. -/
private def one : KleinFourGroup :=
  e

instance : Inhabited (KleinFourGroup) :=
  ⟨one⟩

/-- The inverse of an element of the Klein four-group. -/
private def inv : KleinFourGroup → KleinFourGroup
  | e => e
  | a => a
  | b => b
  | c => c

/-- The group structure on `KleinFourGroup`. -/
instance : Group (KleinFourGroup) where
  mul := mul
  mul_assoc := by
    rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul]
  one := one
  one_mul := by rintro (a | a) <;> rfl
  mul_one := by rintro (a | a) <;> rfl
  inv := inv
  mul_left_inv := by rintro (a | a) <;> rfl

/-- Klein four-group is an abelian group. -/
instance commGroup : CommGroup (KleinFourGroup) where
  mul_comm k₁ k₂ := by
    cases k₁ <;> cases k₂ <;> rfl

/-- Klein four-group is a finite group. -/
instance fintype : Fintype (KleinFourGroup) where
  elems := [e, a, b, c].toFinset
  complete i := by cases i <;> simp

/-- Klein four-group is a group of order 4. -/
theorem card : Fintype.card (KleinFourGroup) = 4 := by
  simp

/-- Klein four-group is a group of order 4. -/
theorem nat_card : Nat.card (KleinFourGroup) = 4 := by
  simp only [Nat.card_eq_fintype_card]

@[simp] theorem a_order_two : a ^ 2 = 1 :=
  rfl

@[simp] theorem b_order_two : b ^ 2 = 1 :=
  rfl

@[simp] theorem c_order_two : c ^ 2 = 1 :=
  rfl

@[simp] theorem orderOf_one : orderOf 1 = 1 := by
  simp only [orderOf_eq_one_iff]

@[simp] theorem orderOf_a : orderOf a = 2 := by
  apply orderOf_eq_prime
  · exact a_order_two
  · simp

@[simp] theorem orderOf_b : orderOf b = 2 := by
  apply orderOf_eq_prime
  · exact b_order_two
  · simp

@[simp] theorem orderOf_c : orderOf c = 2 := by
  apply orderOf_eq_prime
  · exact c_order_two
  · simp

@[simp] theorem one_def : (1 : KleinFourGroup) = e :=
  rfl

theorem exponent : Monoid.exponent (KleinFourGroup) = 2 := by
  have : Monoid.exponent (KleinFourGroup) = lcm 2 2 := by
    apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      simp
    · apply lcm_dvd
      repeat {convert Monoid.order_dvd_exponent a; exact orderOf_a.symm}
  assumption

/-- Klein four-group is a non-cyclic group. -/
theorem notIsCyclic : ¬ IsCyclic (KleinFourGroup) := by
  intro h
  have h₁ := IsCyclic.iff_exponent_eq_card.mp h
  rw [exponent,card] at h₁
  contradiction

/-- Klein four-group is isomorphic to the Dihedral group of order 4. -/
theorem KleinFourGroup_eq_DihedralGroup2 : KleinFourGroup ≃* DihedralGroup 2 where
  toFun k := match k with
    | e => (1 : DihedralGroup 2)
    | a => (sr 1 : DihedralGroup 2)
    | b => (r 1 : DihedralGroup 2)
    | c => (sr 1 * r 1 : DihedralGroup 2)
  invFun d := match d with
    | 1 => e
    | (sr 1 : DihedralGroup 2) => a
    | (r 1 : DihedralGroup 2) => b
    | (sr 1 * r 1 : DihedralGroup 2) => c
  left_inv := by simp
  right_inv := by simp
  map_mul' := by simp

/-- Klein four-group is equivalent to direct product of two cyclic groups of
order two. -/
theorem KleinFourGroup_eq_ProdZMod2 : KleinFourGroup ≃ (ZMod 2) × (ZMod 2) where
  toFun k := match k with
    | e => (0, 0)
    | a => (0, 1)
    | b => (1, 0)
    | c => (1, 1)
  invFun d := match d with
    | (0, 0) => e
    | (0, 1) => a
    | (1, 0) => b
    | (1, 1) => c
  left_inv := by simp
  right_inv := by simp

end KleinFourGroup
