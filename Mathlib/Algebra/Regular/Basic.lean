/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Commute
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements, along with their `to_additive`
analogues add-left-regular, add-right-regular and add-regular elements.

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `is_regular_of_ne_zero` implies that every non-zero element of an integral domain is regular.
Since it assumes that the ring is a `cancel_monoid_with_zero` it applies also, for instance, to `ℕ`.

The lemmas in Section `mul_zero_class` show that the `0` element is (left/right-)regular if and
only if the `mul_zero_class` is trivial.  This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/


variable {R : Type _}

section Mul

variable [Mul R]

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective. -/
@[to_additive IsAddLeftRegular "An add-left-regular element is an element `c` such that addition on the left by `c`\nis injective. -/\n"]
def IsLeftRegular (c : R) :=
  (c * ·).Injective
#align is_left_regular IsLeftRegular

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive IsAddRightRegular "An add-right-regular element is an element `c` such that addition on the right by `c`\nis injective."]
def IsRightRegular (c : R) :=
  (· * c).Injective
#align is_right_regular IsRightRegular

/-- An add-regular element is an element `c` such that addition by `c` both on the left and
on the right is injective. -/
structure IsAddRegular {R : Type _} [Add R] (c : R) : Prop where
  left : IsAddLeftRegular c -- Porting note: It seems like to_additive is misbehaving
  right : IsAddRightRegular c
#align is_add_regular IsAddRegular

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure IsRegular (c : R) : Prop where
  left : IsLeftRegular c
  right : IsRightRegular c
#align is_regular IsRegular

attribute [to_additive IsAddRegular] IsRegular

@[to_additive]
protected theorem MulLECancellable.is_left_regular [PartialOrder R] {a : R} (ha : MulLECancellable a) :
    IsLeftRegular a :=
  ha.Injective
#align mul_le_cancellable.is_left_regular MulLECancellable.is_left_regular

theorem IsLeftRegular.right_of_commute {a : R} (ca : ∀ b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
  fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm
#align is_left_regular.right_of_commute IsLeftRegular.right_of_commute

theorem Commute.is_regular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩
#align commute.is_regular_iff Commute.is_regular_iff

end Mul

section Semigroup

variable [Semigroup R] {a b : R}

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive "In an additive semigroup, the sum of add-left-regular elements is add-left.regular."]
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb
#align is_left_regular.mul IsLeftRegular.mul

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive "In an additive semigroup, the sum of add-right-regular elements is add-right-regular."]
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) : IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra
#align is_right_regular.mul IsRightRegular.mul

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive
      "If an element `b` becomes add-left-regular after adding to it on the left a\nadd-left-regular element, then `b` is add-left-regular."]
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (by rwa [comp_mul_left a b])
#align is_left_regular.of_mul IsLeftRegular.of_mul

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[simp,
  to_additive
      "An element is add-left-regular if and only if adding to it on the left a\nadd-left-regular element is add-left-regular."]
theorem mul_is_left_regular_iff (b : R) (ha : IsLeftRegular a) : IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩
#align mul_is_left_regular_iff mul_is_left_regular_iff

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive
      "If an element `b` becomes add-right-regular after adding to it on the right a\nadd-right-regular element, then `b` is add-right-regular."]
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine' fun x y xy => ab (_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc, ← mul_assoc]
  exact congr_fun (congr_arg (· * ·) xy) a
#align is_right_regular.of_mul IsRightRegular.of_mul

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[simp,
  to_additive
      "An element is add-right-regular if and only if adding it on the right to a\nadd-right-regular element is add-right-regular."]
theorem mul_is_right_regular_iff (b : R) (ha : IsRightRegular a) : IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩
#align mul_is_right_regular_iff mul_is_right_regular_iff

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive "Two elements `a` and `b` are add-regular if and only if both sums `a + b` and `b + a`\nare add-regular."]
theorem is_regular_mul_and_mul_iff : IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b := by
  refine' ⟨_, _⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩

  · rintro ⟨ha, hb⟩
    exact
      ⟨⟨(mul_is_left_regular_iff _ ha.left).mpr hb.left, (mul_is_right_regular_iff _ hb.right).mpr ha.right⟩,
        ⟨(mul_is_left_regular_iff _ hb.left).mpr ha.left, (mul_is_right_regular_iff _ ha.right).mpr hb.right⟩⟩

#align is_regular_mul_and_mul_iff is_regular_mul_and_mul_iff

/-- The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
@[to_additive "The \"most used\" implication of `add_and_add_iff`, with split hypotheses,\ninstead of `∧`."]
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) : IsRegular a ∧ IsRegular b :=
  is_regular_mul_and_mul_iff.mp ⟨ab, ba⟩
#align is_regular.and_of_mul_of_mul IsRegular.and_of_mul_of_mul

end Semigroup

section MulZeroClass

variable [MulZeroClass R] {a b : R}

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩
#align is_left_regular.subsingleton IsLeftRegular.subsingleton

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩
#align is_right_regular.subsingleton IsRightRegular.subsingleton

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R :=
  h.left.subsingleton
#align is_regular.subsingleton IsRegular.subsingleton

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem is_left_regular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩
#align is_left_regular_zero_iff_subsingleton is_left_regular_zero_iff_subsingleton

/-- In a non-trivial `mul_zero_class`, the `0` element is not left-regular. -/
theorem not_is_left_regular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, is_left_regular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl
#align not_is_left_regular_zero_iff not_is_left_regular_zero_iff

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem is_right_regular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩
#align is_right_regular_zero_iff_subsingleton is_right_regular_zero_iff_subsingleton

/-- In a non-trivial `mul_zero_class`, the `0` element is not right-regular. -/
theorem not_is_right_regular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, is_right_regular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl
#align not_is_right_regular_zero_iff not_is_right_regular_zero_iff

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem is_regular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.subsingleton, fun h =>
    ⟨is_left_regular_zero_iff_subsingleton.mpr h, is_right_regular_zero_iff_subsingleton.mpr h⟩⟩
#align is_regular_iff_subsingleton is_regular_iff_subsingleton

/-- A left-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine' xy (la (_ : 0 * x = 0 * y)) -- Porting note: lean4 seems to need the type signature
  rw [zero_mul, zero_mul]
#align is_left_regular.ne_zero IsLeftRegular.ne_zero

/-- A right-regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine' xy (ra (_ : x * 0 = y * 0))
  rw [mul_zero, mul_zero]
#align is_right_regular.ne_zero IsRightRegular.ne_zero

/-- A regular element of a `nontrivial` `mul_zero_class` is non-zero. -/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 :=
  la.left.ne_zero
#align is_regular.ne_zero IsRegular.ne_zero

/-- In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
theorem not_is_left_regular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_is_left_regular_zero_iff.mpr nR
#align not_is_left_regular_zero not_is_left_regular_zero

/-- In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
theorem not_is_right_regular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_is_right_regular_zero_iff.mpr nR
#align not_is_right_regular_zero not_is_right_regular_zero

/-- In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
theorem not_is_regular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl
#align not_is_regular_zero not_is_regular_zero

end MulZeroClass

section MulOneClass

variable [MulOneClass R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive "If adding `0` on either side is the identity, `0` is regular."]
theorem is_regular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩
#align is_regular_one is_regular_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup R] {a b : R}

/-- A product is regular if and only if the factors are. -/
@[to_additive "A sum is add-regular if and only if the summands are."]
theorem is_regular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine' Iff.trans _ is_regular_mul_and_mul_iff
  refine' ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩
#align is_regular_mul_iff is_regular_mul_iff

end CommSemigroup

section Monoid

variable [Monoid R] {a b : R}

/-- An element admitting a left inverse is left-regular. -/
@[to_additive "An element admitting a left additive opposite is add-left-regular."]
theorem is_left_regular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  @IsLeftRegular.of_mul R _ _ _
    (by
      rw [h]
      exact is_regular_one.left)
#align is_left_regular_of_mul_eq_one is_left_regular_of_mul_eq_one

/-- An element admitting a right inverse is right-regular. -/
@[to_additive "An element admitting a right additive opposite is add-right-regular."]
theorem is_right_regular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  IsRightRegular.of_mul
    (by
      rw [h]
      exact is_regular_one.right)
#align is_right_regular_of_mul_eq_one is_right_regular_of_mul_eq_one

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive "If `R` is an additive monoid, an element in `add_units R` is add-regular."]
theorem Units.is_regular (a : Rˣ) : IsRegular (a : R) :=
  ⟨is_left_regular_of_mul_eq_one a.inv_mul, is_right_regular_of_mul_eq_one a.mul_inv⟩
#align units.is_regular Units.is_regular

/-- A unit in a monoid is regular. -/
@[to_additive "An additive unit in an additive monoid is add-regular."]
theorem IsUnit.is_regular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.is_regular a
#align is_unit.is_regular IsUnit.is_regular

end Monoid

/-- Elements of a left cancel semigroup are left regular. -/
@[to_additive "Elements of an add left cancel semigroup are add-left-regular."]
theorem is_left_regular_of_left_cancel_semigroup [LeftCancelSemigroup R] (g : R) : IsLeftRegular g :=
  mul_right_injective g
#align is_left_regular_of_left_cancel_semigroup is_left_regular_of_left_cancel_semigroup

/-- Elements of a right cancel semigroup are right regular. -/
@[to_additive "Elements of an add right cancel semigroup are add-right-regular"]
theorem is_right_regular_of_right_cancel_semigroup [RightCancelSemigroup R] (g : R) : IsRightRegular g :=
  mul_left_injective g
#align is_right_regular_of_right_cancel_semigroup is_right_regular_of_right_cancel_semigroup

section CancelMonoid

variable [CancelMonoid R]

/-- Elements of a cancel monoid are regular.  Cancel semigroups do not appear to exist. -/
@[to_additive "Elements of an add cancel monoid are regular.  Add cancel semigroups do not appear to exist."]
theorem is_regular_of_cancel_monoid (g : R) : IsRegular g :=
  ⟨mul_right_injective g, mul_left_injective g⟩
#align is_regular_of_cancel_monoid is_regular_of_cancel_monoid

end CancelMonoid

section CancelMonoidWithZero

variable [CancelMonoidWithZero R] {a : R}

/-- Non-zero elements of an integral domain are regular. -/
theorem is_regular_of_ne_zero (a0 : a ≠ 0) : IsRegular a :=
  ⟨fun _ _ => (mul_right_inj' a0).mp, fun _ _ => (mul_left_inj' a0).mp⟩
#align is_regular_of_ne_zero is_regular_of_ne_zero

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
theorem is_regular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 :=
  ⟨IsRegular.ne_zero, is_regular_of_ne_zero⟩
#align is_regular_iff_ne_zero is_regular_iff_ne_zero

end CancelMonoidWithZero
