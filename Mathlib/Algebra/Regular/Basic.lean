/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic.NthRewrite

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

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive "An add-right-regular element is an element `c` such that addition
    on the right by `c` is injective."]
def IsRightRegular (c : R) :=
  (· * c).Injective

/-- An add-regular element is an element `c` such that addition by `c` both on the left and
on the right is injective. -/
structure IsAddRegular {R : Type*} [Add R] (c : R) : Prop where
  /-- An add-regular element `c` is left-regular -/
  left : IsAddLeftRegular c -- Porting note: It seems like to_additive is misbehaving
  /-- An add-regular element `c` is right-regular -/
  right : IsAddRightRegular c

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure IsRegular (c : R) : Prop where
  /-- A regular element `c` is left-regular -/
  left : IsLeftRegular c
  /-- A regular element `c` is right-regular -/
  right : IsRightRegular c

attribute [simp] IsRegular.left IsRegular.right

attribute [to_additive] IsRegular

@[to_additive]
theorem isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

@[to_additive]
protected theorem MulLECancellable.isLeftRegular [PartialOrder R] {a : R}
    (ha : MulLECancellable a) : IsLeftRegular a :=
  ha.Injective

theorem IsLeftRegular.right_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsLeftRegular a) : IsRightRegular a :=
  fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm

theorem IsRightRegular.left_of_commute {a : R}
    (ca : ∀ b, Commute a b) (h : IsRightRegular a) : IsLeftRegular a := by
  simp_rw [@Commute.symm_iff R _ a] at ca
  exact fun x y xy => h <| (ca x).trans <| xy.trans <| (ca y).symm

theorem Commute.isRightRegular_iff {a : R} (ca : ∀ b, Commute a b) :
    IsRightRegular a ↔ IsLeftRegular a :=
  ⟨IsRightRegular.left_of_commute ca, IsLeftRegular.right_of_commute ca⟩

theorem Commute.isRegular_iff {a : R} (ca : ∀ b, Commute a b) : IsRegular a ↔ IsLeftRegular a :=
  ⟨fun h => h.left, fun h => ⟨h, h.right_of_commute ca⟩⟩

end Mul

section Semigroup

variable [Semigroup R] {a b : R}

/-- In a semigroup, the product of left-regular elements is left-regular. -/
@[to_additive "In an additive semigroup, the sum of add-left-regular elements is add-left.regular."]
theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) :=
  show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

/-- In a semigroup, the product of right-regular elements is right-regular. -/
@[to_additive "In an additive semigroup, the sum of add-right-regular elements is
add-right-regular."]
theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
    IsRightRegular (a * b) :=
  show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

/-- In a semigroup, the product of regular elements is regular. -/
@[to_additive "In an additive semigroup, the sum of add-regular elements is add-regular."]
theorem IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) :
    IsRegular (a * b) :=
  ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

/-- If an element `b` becomes left-regular after multiplying it on the left by a left-regular
element, then `b` is left-regular. -/
@[to_additive "If an element `b` becomes add-left-regular after adding to it on the left
an add-left-regular element, then `b` is add-left-regular."]
theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b :=
  Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

/-- An element is left-regular if and only if multiplying it on the left by a left-regular element
is left-regular. -/
@[to_additive (attr := simp) "An element is add-left-regular if and only if adding to it on the left
an add-left-regular element is add-left-regular."]
theorem mul_isLeftRegular_iff (b : R) (ha : IsLeftRegular a) :
    IsLeftRegular (a * b) ↔ IsLeftRegular b :=
  ⟨fun ab => IsLeftRegular.of_mul ab, fun ab => IsLeftRegular.mul ha ab⟩

/-- If an element `b` becomes right-regular after multiplying it on the right by a right-regular
element, then `b` is right-regular. -/
@[to_additive "If an element `b` becomes add-right-regular after adding to it on the right
an add-right-regular element, then `b` is add-right-regular."]
theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc, ← mul_assoc]
  exact congr_arg (· * a) xy

/-- An element is right-regular if and only if multiplying it on the right with a right-regular
element is right-regular. -/
@[to_additive (attr := simp)
"An element is add-right-regular if and only if adding it on the right to
an add-right-regular element is add-right-regular."]
theorem mul_isRightRegular_iff (b : R) (ha : IsRightRegular a) :
    IsRightRegular (b * a) ↔ IsRightRegular b :=
  ⟨fun ab => IsRightRegular.of_mul ab, fun ab => IsRightRegular.mul ab ha⟩

/-- Two elements `a` and `b` are regular if and only if both products `a * b` and `b * a`
are regular. -/
@[to_additive "Two elements `a` and `b` are add-regular if and only if both sums `a + b` and
`b + a` are add-regular."]
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
@[to_additive "The \"most used\" implication of `add_and_add_iff`, with split
hypotheses, instead of `∧`."]
theorem IsRegular.and_of_mul_of_mul (ab : IsRegular (a * b)) (ba : IsRegular (b * a)) :
    IsRegular a ∧ IsRegular b :=
  isRegular_mul_and_mul_iff.mp ⟨ab, ba⟩

end Semigroup

section MulZeroClass

variable [MulZeroClass R] {a b : R}

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R :=
  h.left.subsingleton

/-- The element `0` is left-regular if and only if `R` is trivial. -/
theorem isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- In a non-trivial `MulZeroClass`, the `0` element is not left-regular. -/
theorem not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isLeftRegular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl

/-- The element `0` is right-regular if and only if `R` is trivial. -/
theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- In a non-trivial `MulZeroClass`, the `0` element is not right-regular. -/
theorem not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isRightRegular_zero_iff_subsingleton, subsingleton_iff]
  push_neg
  exact Iff.rfl

/-- The element `0` is regular if and only if `R` is trivial. -/
theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

/-- A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la (?_ : 0 * x = 0 * y)) -- Porting note: lean4 seems to need the type signature
  rw [zero_mul, zero_mul]

/-- A right-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra (?_ : x * 0 = y * 0))
  rw [mul_zero, mul_zero]

/-- A regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 :=
  la.left.ne_zero

/-- In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
theorem not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_isLeftRegular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
theorem not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_isRightRegular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
theorem not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl

@[simp] lemma IsLeftRegular.mul_left_eq_zero_iff (hb : IsLeftRegular b) : b * a = 0 ↔ a = 0 := by
  nth_rw 1 [← mul_zero b]
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha]⟩

@[simp] lemma IsRightRegular.mul_right_eq_zero_iff (hb : IsRightRegular b) : a * b = 0 ↔ a = 0 := by
  nth_rw 1 [← zero_mul b]
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha]⟩

end MulZeroClass

section MulOneClass

variable [MulOneClass R]

/-- If multiplying by `1` on either side is the identity, `1` is regular. -/
@[to_additive "If adding `0` on either side is the identity, `0` is regular."]
theorem isRegular_one : IsRegular (1 : R) :=
  ⟨fun a b ab => (one_mul a).symm.trans (Eq.trans ab (one_mul b)), fun a b ab =>
    (mul_one a).symm.trans (Eq.trans ab (mul_one b))⟩

end MulOneClass

section CommSemigroup

variable [CommSemigroup R] {a b : R}

/-- A product is regular if and only if the factors are. -/
@[to_additive "A sum is add-regular if and only if the summands are."]
theorem isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

end CommSemigroup

section Monoid

variable [Monoid R] {a b : R} {n : ℕ}

/-- An element admitting a left inverse is left-regular. -/
@[to_additive "An element admitting a left additive opposite is add-left-regular."]
theorem isLeftRegular_of_mul_eq_one (h : b * a = 1) : IsLeftRegular a :=
  IsLeftRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.left)

/-- An element admitting a right inverse is right-regular. -/
@[to_additive "An element admitting a right additive opposite is add-right-regular."]
theorem isRightRegular_of_mul_eq_one (h : a * b = 1) : IsRightRegular a :=
  IsRightRegular.of_mul (a := b) (by rw [h]; exact isRegular_one.right)

/-- If `R` is a monoid, an element in `Rˣ` is regular. -/
@[to_additive "If `R` is an additive monoid, an element in `add_units R` is add-regular."]
theorem Units.isRegular (a : Rˣ) : IsRegular (a : R) :=
  ⟨isLeftRegular_of_mul_eq_one a.inv_mul, isRightRegular_of_mul_eq_one a.mul_inv⟩

/-- A unit in a monoid is regular. -/
@[to_additive "An additive unit in an additive monoid is add-regular."]
theorem IsUnit.isRegular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

/-- Any power of a left-regular element is left-regular. -/
lemma IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]

/-- Any power of a right-regular element is right-regular. -/
lemma IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) := by
  rw [IsRightRegular, ← mul_right_iterate]
  exact rra.iterate n

/-- Any power of a regular element is regular. -/
lemma IsRegular.pow (n : ℕ) (ra : IsRegular a) : IsRegular (a ^ n) :=
  ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩

/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
lemma IsLeftRegular.pow_iff (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]; exact .of_mul
  mpr := .pow n

/-- An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
lemma IsRightRegular.pow_iff (n0 : 0 < n) : IsRightRegular (a ^ n) ↔ IsRightRegular a where
  mp := by rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']; exact .of_mul
  mpr := .pow n

/-- An element `a` is regular if and only if a positive power of `a` is regular. -/
lemma IsRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsRegular (a ^ n) ↔ IsRegular a where
  mp h := ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩
  mpr h := ⟨.pow n h.left, .pow n h.right⟩

end Monoid

/-- If all multiplications cancel on the left then every element is left-regular. -/
@[to_additive "If all additions cancel on the left then every element is add-left-regular."]
theorem IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R) : IsLeftRegular g :=
  mul_right_injective g

/-- If all multiplications cancel on the right then every element is right-regular. -/
@[to_additive "If all additions cancel on the right then every element is add-right-regular."]
theorem IsRightRegular.all [Mul R] [IsRightCancelMul R] (g : R) : IsRightRegular g :=
  mul_left_injective g

/-- If all multiplications cancel then every element is regular. -/
@[to_additive "If all additions cancel then every element is add-regular."]
theorem IsRegular.all [Mul R] [IsCancelMul R] (g : R) : IsRegular g :=
  ⟨mul_right_injective g, mul_left_injective g⟩

section CancelMonoidWithZero

variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

/-- Non-zero elements of an integral domain are regular. -/
theorem isRegular_of_ne_zero (a0 : a ≠ 0) : IsRegular a :=
  ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
theorem isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 :=
  ⟨IsRegular.ne_zero, isRegular_of_ne_zero⟩

end CancelMonoidWithZero
