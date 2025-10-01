/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Regular.Defs

/-!
# Regular elements

By definition, a regular element in a commutative ring is a non-zero divisor.
Lemma `isRegular_of_ne_zero` implies that every non-zero element of an integral domain is regular.
Since it assumes that the ring is a `CancelMonoidWithZero` it applies also, for instance, to `ℕ`.

The lemmas in Section `MulZeroClass` show that the `0` element is (left/right-)regular if and
only if the `MulZeroClass` is trivial.  This is useful when figuring out stopping conditions for
regular sequences: if `0` is ever an element of a regular sequence, then we can extend the sequence
by adding one further `0`.

The final goal is to develop part of the API to prove, eventually, results about non-zero-divisors.
-/

variable {R : Type*}

section Mul

variable [Mul R]

@[to_additive] theorem IsLeftRegular.right_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
  fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm

@[to_additive] theorem IsRightRegular.left_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsRightRegular a) : IsLeftRegular a := by
  simp only [@Commute.symm_iff R _ a] at ca
  exact fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm

@[to_additive] theorem Commute.isRightRegular_iff {a : R} (ca : ∀ b, Commute a b) :
    IsRightRegular a ↔ IsLeftRegular a :=
  ⟨IsRightRegular.left_of_commute ca, IsLeftRegular.right_of_commute ca⟩

@[to_additive]
theorem Commute.isRegular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

end Mul

section Semigroup

variable [Semigroup R] {a b : R}

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive
/-- In an additive semigroup, the sum of add-left-regular elements is add-left.regular. -/]
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive
/-- In an additive semigroup, the sum of add-right-regular elements is add-right-regular. -/]
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
    IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

/-- In a semigroup, the product of regular elements is regular. -/
@[to_additive /-- In an additive semigroup, the sum of add-regular elements is add-regular. -/]
theorem IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) :
    IsRegular (a * b) :=
  ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive /-- If an element `b` becomes add-left-regular after adding to it on the left
an add-left-regular element, then `b` is add-left-regular. -/]
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[to_additive (attr := simp) /-- An element is add-left-regular if and only if adding to it on the
left an add-left-regular element is add-left-regular. -/]
theorem mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) :
    IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive /-- If an element `b` becomes add-right-regular after adding to it on the right
an add-right-regular element, then `b` is add-right-regular. -/]
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc, ← mul_assoc]
  exact congr_arg (· * a) xy

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[to_additive (attr := simp)
/-- An element is add-right-regular if and only if adding it on the right to
an add-right-regular element is add-right-regular. -/]
theorem mul_isRightRegular_iff (b : R) (ha : IsRightRegular a) :
    IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive /-- Two elements `a` and `b` are add-regular if and only if both sums `a + b` and
`b + a` are add-regular. -/]
theorem isRegular_mul_and_mul_iff :
    IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

/-- The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
@[to_additive /-- The "most used" implication of `add_and_add_iff`, with split
hypotheses, instead of `∧`. -/]
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) :
    IsRegular a ∧ IsRegular b :=
  isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

end Semigroup


section MulOneClass

variable [MulOneClass R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive /-- If adding `0` on either side is the identity, `0` is regular. -/]
theorem isRegular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

end MulOneClass

section CommSemigroup

variable [CommSemigroup R] {a b : R}

/-- A product is regular if and only if the factors are. -/
@[to_additive /-- A sum is add-regular if and only if the summands are. -/]
theorem isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

end CommSemigroup

section Monoid

variable [Monoid R] {a b : R} {n : ℕ}

/-- An element admitting a left inverse is left-regular. -/
@[to_additive /-- An element admitting a left additive opposite is add-left-regular. -/]
theorem isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

/-- An element admitting a right inverse is right-regular. -/
@[to_additive /-- An element admitting a right additive opposite is add-right-regular. -/]
theorem isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive /-- If `R` is an additive monoid, an element in `add_units R` is add-regular. -/]
theorem Units.isRegular (a : Rˣ) : IsRegular (a : R) :=
  ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

/-- A unit in a monoid is regular. -/
@[to_additive /-- An additive unit in an additive monoid is add-regular. -/]
theorem IsUnit.isRegular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

/-- Any power of a left-regular element is left-regular. -/
@[to_additive]
lemma IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

/-- Any power of a right-regular element is right-regular. -/
@[to_additive]
lemma IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
  rw [IsRightRegular, ← mul_right_iterate]
  exact rra.iterate n

/-- Any power of a regular element is regular. -/
@[to_additive] lemma IsRegular.pow (n : ℕ) (ra : IsRegular a) : IsRegular (a ^ n) :=
  ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩

/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
@[to_additive]
lemma IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

/-- An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
@[to_additive]
lemma IsRightRegular.pow_iff (n0 : 0 < n) : IsRightRegular (a ^ n) ↔ IsRightRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']; exact .of_mul
  mpr := .pow n

/-- An element `a` is regular if and only if a positive power of `a` is regular. -/
@[to_additive] lemma IsRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsRegular (a ^ n) ↔ IsRegular a where
  mp h := ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩
  mpr h := ⟨.pow n h.left, .pow n h.right⟩

@[to_additive (attr := simp)] lemma IsLeftRegular.mul_left_eq_self_iff (ha : IsLeftRegular a) :
    a * b = a ↔ b = 1 :=
  ⟨fun h ↦ by rwa [← ha.eq_iff, mul_one], fun h ↦ by rw [h, mul_one]⟩

@[to_additive (attr := simp)] lemma IsRightRegular.mul_right_eq_self_iff (ha : IsRightRegular a) :
    b * a = a ↔ b = 1 :=
  ⟨fun h ↦ by rwa [← ha.eq_iff, one_mul], fun h ↦ by rw [h, one_mul]⟩

end Monoid
