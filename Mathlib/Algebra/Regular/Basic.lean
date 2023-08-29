/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Commute
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.GroupWithZero.Basic

#align_import algebra.regular.basic from "leanprover-community/mathlib"@"5cd3c25312f210fec96ba1edb2aebfb2ccf2010f"

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements, along with their `to_additive`
analogues add-left-regular, add-right-regular and add-regular elements.

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

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective. -/
@[to_additive "An add-left-regular element is an element `c` such that addition
    on the left by `c` is injective."]
def IsLeftRegular (c : R) :=
  (c * ·).Injective
#align is_left_regular IsLeftRegular
#align is_add_left_regular IsAddLeftRegular

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive "An add-right-regular element is an element `c` such that addition
    on the right by `c` is injective."]
def IsRightRegular (c : R) :=
  (· * c).Injective
#align is_right_regular IsRightRegular
#align is_add_right_regular IsAddRightRegular

/-- An add-regular element is an element `c` such that addition by `c` both on the left and
on the right is injective. -/
structure IsAddRegular {R : Type*} [Add R] (c : R) : Prop where
  /-- An add-regular element `c` is left-regular -/
  left : IsAddLeftRegular c -- Porting note: It seems like to_additive is misbehaving
  /-- An add-regular element `c` is right-regular -/
  right : IsAddRightRegular c
#align is_add_regular IsAddRegular

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure IsRegular (c : R) : Prop where
  /-- A regular element `c` is left-regular -/
  left : IsLeftRegular c
  /-- A regular element `c` is right-regular -/
  right : IsRightRegular c
#align is_regular IsRegular

attribute [simp] IsRegular.left IsRegular.right

attribute [to_additive] IsRegular

@[to_additive]
protected theorem MulLECancellable.isLeftRegular [PartialOrder R] {a : R}
    (ha : MulLECancellable a) : IsLeftRegular a :=
  ha.Injective
#align mul_le_cancellable.is_left_regular MulLECancellable.isLeftRegular
#align add_le_cancellable.is_add_left_regular AddLECancellable.isAddLeftRegular

theorem IsLeftRegular.right_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
  fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm
#align is_left_regular.right_of_commute IsLeftRegular.right_of_commute

theorem Commute.isRegular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩
#align commute.is_regular_iff Commute.isRegular_iff

end Mul

section Semigroup

variable [Semigroup R] {a b : R}

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive "In an additive semigroup, the sum of add-left-regular elements is add-left.regular."]
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb
#align is_left_regular.mul IsLeftRegular.mul
#align is_add_left_regular.add IsAddLeftRegular.add

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive "In an additive semigroup, the sum of add-right-regular elements is
add-right-regular."]
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
    IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra
#align is_right_regular.mul IsRightRegular.mul
#align is_add_right_regular.add IsAddRightRegular.add

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive "If an element `b` becomes add-left-regular after adding to it on the left
an add-left-regular element, then `b` is add-left-regular."]
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (by rwa [comp_mul_left a b])
                                 -- 🎉 no goals
#align is_left_regular.of_mul IsLeftRegular.of_mul
#align is_add_left_regular.of_add IsAddLeftRegular.of_add

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[to_additive (attr := simp) "An element is add-left-regular if and only if adding to it on the left
an add-left-regular element is add-left-regular."]
theorem mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) :
    IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩
#align mul_is_left_regular_iff mul_isLeftRegular_iff
#align add_is_add_left_regular_iff add_isAddLeftRegular_iff

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive "If an element `b` becomes add-right-regular after adding to it on the right
an add-right-regular element, then `b` is add-right-regular."]
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine' fun x y xy => ab (_ : x * (b * a) = y * (b * a))
  -- ⊢ x * (b * a) = y * (b * a)
  rw [← mul_assoc, ← mul_assoc]
  -- ⊢ x * b * a = y * b * a
  exact congr_fun (congr_arg (· * ·) xy) a
  -- 🎉 no goals
#align is_right_regular.of_mul IsRightRegular.of_mul
#align is_add_right_regular.of_add IsAddRightRegular.of_add

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[to_additive (attr := simp)
"An element is add-right-regular if and only if adding it on the right to
an add-right-regular element is add-right-regular."]
theorem mul_isRightRegular_iff (b : R) (ha : IsRightRegular a) :
    IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩
#align mul_is_right_regular_iff mul_isRightRegular_iff
#align add_is_add_right_regular_iff add_isAddRightRegular_iff

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive "Two elements `a` and `b` are add-regular if and only if both sums `a + b` and
`b + a` are add-regular."]
theorem isRegular_mul_and_mul_iff :
    IsRegular (a * b) ∧ IsRegular (b * a) ↔ IsRegular a ∧ IsRegular b := by
  refine' ⟨_, _⟩
  -- ⊢ IsRegular (a * b) ∧ IsRegular (b * a) → IsRegular a ∧ IsRegular b
  · rintro ⟨ab, ba⟩
    -- ⊢ IsRegular a ∧ IsRegular b
    exact
      ⟨⟨IsLeftRegular.of_mul ba.left, IsRightRegular.of_mul ab.right⟩,
        ⟨IsLeftRegular.of_mul ab.left, IsRightRegular.of_mul ba.right⟩⟩
  · rintro ⟨ha, hb⟩
    -- ⊢ IsRegular (a * b) ∧ IsRegular (b * a)
    exact
      ⟨⟨(mul_isLeftRegular_iff _ ha.left).mpr hb.left,
          (mul_isRightRegular_iff _ hb.right).mpr ha.right⟩,
        ⟨(mul_isLeftRegular_iff _ hb.left).mpr ha.left,
          (mul_isRightRegular_iff _ ha.right).mpr hb.right⟩⟩
#align is_regular_mul_and_mul_iff isRegular_mul_and_mul_iff
#align is_add_regular_add_and_add_iff isAddRegular_add_and_add_iff

/-- The "most used" implication of `mul_and_mul_iff`, with split hypotheses, instead of `∧`. -/
@[to_additive "The \"most used\" implication of `add_and_add_iff`, with split
hypotheses, instead of `∧`."]
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) :
    IsRegular a ∧ IsRegular b :=
  isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩
#align is_regular.and_of_mul_of_mul IsRegular.and_of_mul_of_mul
#align is_add_regular.and_of_add_of_add IsAddRegular.and_of_add_of_add

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
theorem isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩
#align is_left_regular_zero_iff_subsingleton isLeftRegular_zero_iff_subsingleton

/-- In a non-trivial `MulZeroClass`, the `0` element is not left-regular. -/
theorem not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isLeftRegular_zero_iff_subsingleton, subsingleton_iff]
  -- ⊢ (¬∃ x y, x ≠ y) ↔ ∀ (x y : R), x = y
  push_neg
  -- ⊢ (∀ (x y : R), x = y) ↔ ∀ (x y : R), x = y
  exact Iff.rfl
  -- 🎉 no goals
#align not_is_left_regular_zero_iff not_isLeftRegular_zero_iff

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩
#align is_right_regular_zero_iff_subsingleton isRightRegular_zero_iff_subsingleton

/-- In a non-trivial `MulZeroClass`, the `0` element is not right-regular. -/
theorem not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isRightRegular_zero_iff_subsingleton, subsingleton_iff]
  -- ⊢ (¬∃ x y, x ≠ y) ↔ ∀ (x y : R), x = y
  push_neg
  -- ⊢ (∀ (x y : R), x = y) ↔ ∀ (x y : R), x = y
  exact Iff.rfl
  -- 🎉 no goals
#align not_is_right_regular_zero_iff not_isRightRegular_zero_iff

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩
#align is_regular_iff_subsingleton isRegular_iff_subsingleton

/-- A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  -- ⊢ False
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  -- ⊢ False
  refine' xy (la (_ : 0 * x = 0 * y)) -- Porting note: lean4 seems to need the type signature
  -- ⊢ 0 * x = 0 * y
  rw [zero_mul, zero_mul]
  -- 🎉 no goals
#align is_left_regular.ne_zero IsLeftRegular.ne_zero

/-- A right-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  -- ⊢ False
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  -- ⊢ False
  refine' xy (ra (_ : x * 0 = y * 0))
  -- ⊢ x * 0 = y * 0
  rw [mul_zero, mul_zero]
  -- 🎉 no goals
#align is_right_regular.ne_zero IsRightRegular.ne_zero

/-- A regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 :=
  la.left.ne_zero
#align is_regular.ne_zero IsRegular.ne_zero

/-- In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
theorem not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_isLeftRegular_zero_iff.mpr nR
#align not_is_left_regular_zero not_isLeftRegular_zero

/-- In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
theorem not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_isRightRegular_zero_iff.mpr nR
#align not_is_right_regular_zero not_isRightRegular_zero

/-- In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
theorem not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl
#align not_is_regular_zero not_isRegular_zero

@[simp] lemma IsLeftRegular.mul_left_eq_zero_iff (hb : IsLeftRegular b) : b * a = 0 ↔ a = 0 := by
  nth_rw 1 [← mul_zero b]
  -- ⊢ b * a = b * 0 ↔ a = 0
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha, mul_zero]⟩
  -- 🎉 no goals

@[simp] lemma IsRightRegular.mul_right_eq_zero_iff (hb : IsRightRegular b) : a * b = 0 ↔ a = 0 := by
  nth_rw 1 [← zero_mul b]
  -- ⊢ a * b = 0 * b ↔ a = 0
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha, zero_mul]⟩
  -- 🎉 no goals

end MulZeroClass

section MulOneClass

variable [MulOneClass R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive "If adding `0` on either side is the identity, `0` is regular."]
theorem isRegular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩
#align is_regular_one isRegular_one
#align is_add_regular_zero isAddRegular_zero

end MulOneClass

section CommSemigroup

variable [CommSemigroup R] {a b : R}

/-- A product is regular if and only if the factors are. -/
@[to_additive "A sum is add-regular if and only if the summands are."]
theorem isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine' Iff.trans _ isRegular_mul_and_mul_iff
  -- ⊢ IsRegular (a * b) ↔ IsRegular (a * b) ∧ IsRegular (b * a)
  refine' ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩
  -- 🎉 no goals
#align is_regular_mul_iff isRegular_mul_iff
#align is_add_regular_add_iff isAddRegular_add_iff

end CommSemigroup

section Monoid

variable [Monoid R] {a b : R}

/-- An element admitting a left inverse is left-regular. -/
@[to_additive "An element admitting a left additive opposite is add-left-regular."]
theorem isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  @IsLeftRegular.of_mul R _ _ _ (by rw [h]; exact isRegular_one.left)
                                    -- ⊢ IsLeftRegular 1
                                            -- 🎉 no goals
#align is_left_regular_of_mul_eq_one isLeftRegular_of_mul_eq_one
#align is_add_left_regular_of_add_eq_zero isAddLeftRegular_of_add_eq_zero

/-- An element admitting a right inverse is right-regular. -/
@[to_additive "An element admitting a right additive opposite is add-right-regular."]
theorem isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  IsRightRegular.of_mul (by rw [h]; exact isRegular_one.right)
                            -- ⊢ IsRightRegular 1
                                    -- 🎉 no goals
#align is_right_regular_of_mul_eq_one isRightRegular_of_mul_eq_one
#align is_add_right_regular_of_add_eq_zero isAddRightRegular_of_add_eq_zero

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive "If `R` is an additive monoid, an element in `add_units R` is add-regular."]
theorem Units.isRegular (a : Rˣ) : IsRegular (a : R) :=
  ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩
#align units.is_regular Units.isRegular
#align add_units.is_add_regular AddUnits.isAddRegular

/-- A unit in a monoid is regular. -/
@[to_additive "An additive unit in an additive monoid is add-regular."]
theorem IsUnit.isRegular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  -- ⊢ IsRegular ↑a
  exact Units.isRegular a
  -- 🎉 no goals
#align is_unit.is_regular IsUnit.isRegular
#align is_add_unit.is_add_regular IsAddUnit.isAddRegular

end Monoid

/-- Elements of a left cancel semigroup are left regular. -/
@[to_additive "Elements of an add left cancel semigroup are add-left-regular."]
theorem isLeftRegular_of_leftCancelSemigroup [LeftCancelSemigroup R]
    (g : R) : IsLeftRegular g :=
  mul_right_injective g
#align is_left_regular_of_left_cancel_semigroup isLeftRegular_of_leftCancelSemigroup
#align is_add_left_regular_of_left_cancel_add_semigroup isAddLeftRegular_of_addLeftCancelSemigroup

/-- Elements of a right cancel semigroup are right regular. -/
@[to_additive "Elements of an add right cancel semigroup are add-right-regular"]
theorem isRightRegular_of_rightCancelSemigroup [RightCancelSemigroup R]
    (g : R) : IsRightRegular g :=
  mul_left_injective g
#align is_right_regular_of_right_cancel_semigroup isRightRegular_of_rightCancelSemigroup
#align is_add_right_regular_of_right_cancel_add_semigroup   isAddRightRegular_of_addRightCancelSemigroup

section CancelMonoid

variable [CancelMonoid R]

/-- Elements of a cancel monoid are regular.  Cancel semigroups do not appear to exist. -/
@[to_additive "Elements of an add cancel monoid are regular.
Add cancel semigroups do not appear to exist."]
theorem isRegular_of_cancelMonoid (g : R) : IsRegular g :=
  ⟨mul_right_injective g, mul_left_injective g⟩
#align is_regular_of_cancel_monoid isRegular_of_cancelMonoid
#align is_add_regular_of_cancel_add_monoid isAddRegular_of_addCancelMonoid

end CancelMonoid

section CancelMonoidWithZero

variable [CancelMonoidWithZero R] {a : R}

/-- Non-zero elements of an integral domain are regular. -/
theorem isRegular_of_ne_zero (a0 : a ≠ 0) : IsRegular a :=
  ⟨fun _ _ => (mul_right_inj' a0).mp, fun _ _ => (mul_left_inj' a0).mp⟩
#align is_regular_of_ne_zero isRegular_of_ne_zero

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
theorem isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 :=
  ⟨IsRegular.ne_zero, isRegular_of_ne_zero⟩
#align is_regular_iff_ne_zero isRegular_iff_ne_zero

end CancelMonoidWithZero
