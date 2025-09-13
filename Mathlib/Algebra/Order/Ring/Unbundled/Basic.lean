/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Tauto

/-!
# Basic facts for ordered rings and semirings

This file develops the basics of ordered (semi)rings in an unbundled fashion for later use with
the bundled classes from `Mathlib/Algebra/Order/Ring/Defs.lean`.

The set of typeclass variables here comprises
* an algebraic class (`Semiring`, `CommSemiring`, `Ring`, `CommRing`)
* an order class (`PartialOrder`, `LinearOrder`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses found in `Algebra.Order.Ring.Defs`

* `OrderedSemiring`: Semiring with a partial order such that `+` and `*` respect `≤`.
* `StrictOrderedSemiring`: Nontrivial semiring with a partial order such that `+` and `*` respects
  `<`.
* `OrderedCommSemiring`: Commutative semiring with a partial order such that `+` and `*` respect
  `≤`.
* `StrictOrderedCommSemiring`: Nontrivial commutative semiring with a partial order such that `+`
  and `*` respect `<`.
* `OrderedRing`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `OrderedCommRing`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedSemiring`: Nontrivial semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedCommSemiring`: Nontrivial commutative semiring with a linear order such that `+`
  respects `≤` and `*` respects `<`.
* `LinearOrderedRing`: Nontrivial ring with a linear order such that `+` respects `≤` and `*`
  respects `<`.
* `LinearOrderedCommRing`: Nontrivial commutative ring with a linear order such that `+` respects
  `≤` and `*` respects `<`.
* `CanonicallyOrderedCommSemiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `OrderedSemiring`
  - `OrderedAddCommMonoid` & multiplication & `*` respects `≤`
  - `Semiring` & partial order structure & `+` respects `≤` & `*` respects `≤`
* `StrictOrderedSemiring`
  - `OrderedCancelAddCommMonoid` & multiplication & `*` respects `<` & nontriviality
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommSemiring`
  - `OrderedSemiring` & commutativity of multiplication
  - `CommSemiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommSemiring`
  - `StrictOrderedSemiring` & commutativity of multiplication
  - `OrderedCommSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedRing`
  - `OrderedSemiring` & additive inverses
  - `OrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedRing`
  - `StrictOrderedSemiring` & additive inverses
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommRing`
  - `OrderedRing` & commutativity of multiplication
  - `OrderedCommSemiring` & additive inverses
  - `CommRing` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommRing`
  - `StrictOrderedCommSemiring` & additive inverses
  - `StrictOrderedRing` & commutativity of multiplication
  - `OrderedCommRing` & `+` respects `<` & `*` respects `<` & nontriviality
* `LinearOrderedSemiring`
  - `StrictOrderedSemiring` & totality of the order
  - `LinearOrderedAddCommMonoid` & multiplication & nontriviality & `*` respects `<`
* `LinearOrderedCommSemiring`
  - `StrictOrderedCommSemiring` & totality of the order
  - `LinearOrderedSemiring` & commutativity of multiplication
* `LinearOrderedRing`
  - `StrictOrderedRing` & totality of the order
  - `LinearOrderedSemiring` & additive inverses
  - `LinearOrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & `IsDomain` & linear order structure
* `LinearOrderedCommRing`
  - `StrictOrderedCommRing` & totality of the order
  - `LinearOrderedRing` & commutativity of multiplication
  - `LinearOrderedCommSemiring` & additive inverses
  - `CommRing` & `IsDomain` & linear order structure

## Generality

Each section is labelled with a corresponding bundled ordered ring typeclass in mind. Mixins for
relating the order structures and ring structures are added as needed.

TODO: the mixin assumptions can be relaxed in most cases

-/

assert_not_exists OrderedCommMonoid MonoidHom

open Function

universe u

variable {R : Type u} {α : Type*}

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/


theorem add_one_le_two_mul [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R}
    (a1 : 1 ≤ a) : a + 1 ≤ 2 * a :=
  calc
    a + 1 ≤ a + a := add_le_add_left a1 a
    _ = 2 * a := (two_mul _).symm

section OrderedSemiring

variable [Semiring R] [Preorder R] {a b c d : R}

theorem add_le_mul_two_add [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) :=
      add_le_add_left (add_le_add a2 <| le_mul_of_one_le_left b0 <| one_le_two.trans a2) a
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

theorem mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ ≤ d * a := mul_le_mul_of_nonneg_left h <| hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ ≤ a * d := mul_le_mul_of_nonneg_right h <| hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

theorem mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

theorem mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonneg_left hbd hc

theorem mul_le_mul_of_nonneg_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_right hac hb).trans <| mul_le_mul_of_nonpos_left hdb hc

theorem mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonpos_left hdb hc

theorem mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_left hdb ha).trans <| mul_le_mul_of_nonpos_right hca hd

/-- Variant of `mul_le_of_le_one_left` for `b` non-positive instead of non-negative. -/
theorem le_mul_of_le_one_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : a ≤ 1) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/-- Variant of `le_mul_of_one_le_left` for `b` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/-- Variant of `mul_le_of_le_one_right` for `a` non-positive instead of non-negative. -/
theorem le_mul_of_le_one_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

/-- Variant of `le_mul_of_one_le_right` for `a` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

section Monotone

variable [Preorder α] {f g : α → R}

theorem antitone_mul_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone (a * ·) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

theorem antitone_mul_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

theorem Monotone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => a * f x :=
  (antitone_mul_left ha).comp_monotone hf

theorem Monotone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => f x * a :=
  (antitone_mul_right ha).comp_monotone hf

theorem Antitone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => a * f x :=
  (antitone_mul_left ha).comp hf

theorem Antitone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => f x * a :=
  (antitone_mul_right ha).comp hf

theorem Antitone.mul_monotone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Monotone g) (hf₀ : ∀ x, f x ≤ 0)
    (hg₀ : ∀ x, 0 ≤ g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

theorem Monotone.mul_antitone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (hg : Antitone g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, g x ≤ 0) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

theorem Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

end Monotone
end OrderedSemiring

section OrderedCommRing

section StrictOrderedSemiring

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem lt_two_mul_self [ZeroLEOneClass R] [MulPosStrictMono R] [NeZero (1 : R)]
    [AddLeftStrictMono R] (ha : 0 < a) : a < 2 * a :=
  lt_mul_of_one_lt_left ha one_lt_two

theorem mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ < d * a := mul_lt_mul_of_pos_left h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

theorem mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ < a * d := mul_lt_mul_of_pos_right h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

theorem mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b : R} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

/-- Variant of `mul_lt_of_lt_one_left` for `b` negative instead of positive. -/
theorem lt_mul_of_lt_one_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/-- Variant of `lt_mul_of_one_lt_left` for `b` negative instead of positive. -/
theorem mul_lt_of_one_lt_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/-- Variant of `mul_lt_of_lt_one_right` for `a` negative instead of positive. -/
theorem lt_mul_of_lt_one_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

/-- Variant of `lt_mul_of_lt_one_right` for `a` negative instead of positive. -/
theorem mul_lt_of_one_lt_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

section Monotone

variable [Preorder α] {f : α → R}

theorem strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti (a * ·) := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

theorem strictAnti_mul_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

theorem StrictMono.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => a * f x :=
  (strictAnti_mul_left ha).comp_strictMono hf

theorem StrictMono.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => f x * a :=
  (strictAnti_mul_right ha).comp_strictMono hf

theorem StrictAnti.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => a * f x :=
  (strictAnti_mul_left ha).comp hf

theorem StrictAnti.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => f x * a :=
  (strictAnti_mul_right ha).comp hf

end Monotone

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hab hd) _

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul' [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hba : b ≤ a) (hdc : d ≤ c) : a * d + b * c ≤ a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

variable [AddLeftReflectLT R]

/-- Binary strict **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  exact hd

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul' [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

end StrictOrderedSemiring

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
    [MulPosStrictMono R] [PosMulStrictMono R]
    (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

theorem nonneg_of_mul_nonneg_left [MulPosStrictMono R]
    (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h

theorem nonneg_of_mul_nonneg_right [PosMulStrictMono R]
    (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h

theorem nonpos_of_mul_nonpos_left [PosMulStrictMono R]
    (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h

theorem nonpos_of_mul_nonpos_right [PosMulStrictMono R]
    (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h

@[simp]
theorem mul_nonneg_iff_of_pos_left [PosMulStrictMono R]
    (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  convert mul_le_mul_iff_right₀ h
  simp

@[simp]
theorem mul_nonneg_iff_of_pos_right [MulPosStrictMono R]
    (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  simpa using (mul_le_mul_iff_left₀ h : 0 * c ≤ b * c ↔ 0 ≤ b)

theorem add_le_mul_of_left_le_right [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
  have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ ≤ a := a2
      _ ≤ b := ab
  calc
    a + b ≤ b + b := add_le_add_right ab b
    _ = 2 * b := (two_mul b).symm
    _ ≤ a * b := (mul_le_mul_iff_left₀ this).mpr a2

theorem add_le_mul_of_right_le_left [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftMono R] [PosMulStrictMono R]
    (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
  have : 0 < a :=
    calc 0
      _ < 2 := zero_lt_two
      _ ≤ b := b2
      _ ≤ a := ba
  calc
    a + b ≤ a + a := add_le_add_left ba a
    _ = a * 2 := (mul_two a).symm
    _ ≤ a * b := (mul_le_mul_iff_right₀ this).mpr b2

theorem add_le_mul [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
  if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_ge hab)

theorem add_le_mul' [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
  (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

theorem mul_nonneg_iff_right_nonneg_of_pos [PosMulStrictMono R]
    (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
  ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

theorem mul_nonneg_iff_left_nonneg_of_pos [PosMulStrictMono R] [MulPosStrictMono R]
    (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
  ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩

theorem nonpos_of_mul_nonneg_left [PosMulStrictMono R]
    (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_ge

theorem nonpos_of_mul_nonneg_right [MulPosStrictMono R]
    (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_ge

@[simp]
theorem Units.inv_pos
    [ZeroLEOneClass R] [NeZero (1 : R)] [PosMulStrictMono R]
    {u : Rˣ} : (0 : R) < ↑u⁻¹ ↔ (0 : R) < u :=
  have : ∀ {u : Rˣ}, (0 : R) < u → (0 : R) < ↑u⁻¹ := @fun u h =>
    (mul_pos_iff_of_pos_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]
theorem Units.inv_neg
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosMono R] [PosMulMono R]
    {u : Rˣ} : ↑u⁻¹ < (0 : R) ↔ ↑u < (0 : R) :=
  have : ∀ {u : Rˣ}, ↑u < (0 : R) → ↑u⁻¹ < (0 : R) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

theorem cmp_mul_pos_left [PosMulStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_mul_left_of_pos ha).cmp_map_eq b c

theorem cmp_mul_pos_right [MulPosStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (b * a) (c * a) = cmp b c :=
  (strictMono_mul_right_of_pos ha).cmp_map_eq b c

theorem mul_max_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_max

theorem mul_min_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_min

theorem max_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_max

theorem min_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_min

theorem le_of_mul_le_of_one_le
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMono R] [PosMulMono R]
    {a b c : R} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
  le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) <| zero_lt_one.trans_le hc

theorem nonneg_le_nonneg_of_sq_le_sq [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
  le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_ge h

theorem mul_self_le_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
  ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

theorem mul_self_lt_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
  ((@strictMonoOn_mul_self R _).lt_iff_lt h1 h2).symm

theorem mul_self_inj [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  (@strictMonoOn_mul_self R _).eq_iff_eq h1 h2

lemma sign_cases_of_C_mul_pow_nonneg [PosMulStrictMono R]
    (h : ∀ n, 0 ≤ a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 ≤ b := by
  have : 0 ≤ a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_lt'.imp_right fun ha ↦ ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1

theorem mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R] :
    0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

theorem mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

/-- Out of three elements of a `LinearOrderedRing`, two must have the same sign. -/
theorem mul_nonneg_of_three [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (a b c : R) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  aesop

lemma mul_nonneg_iff_pos_imp_nonneg [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

@[simp]
theorem mul_le_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
  (strictAnti_mul_left h).le_iff_ge

@[simp]
theorem mul_le_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  (strictAnti_mul_right h).le_iff_ge

@[simp]
theorem mul_lt_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : c * a < c * b ↔ b < a :=
  (strictAnti_mul_left h).lt_iff_gt

@[simp]
theorem mul_lt_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : a * c < b * c ↔ b < a :=
  (strictAnti_mul_right h).lt_iff_gt

theorem lt_of_mul_lt_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
  (antitone_mul_left hc).reflect_lt h

theorem lt_of_mul_lt_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
  (antitone_mul_right hc).reflect_lt h

theorem cmp_mul_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (a * b) (a * c) = cmp c b :=
  (strictAnti_mul_left ha).cmp_map_eq b c

theorem cmp_mul_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (b * a) (c * a) = cmp c b :=
  (strictAnti_mul_right ha).cmp_map_eq b c

@[simp]
theorem mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R]
    {a : R} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_gt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]

theorem nonneg_of_mul_nonpos_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

theorem nonneg_of_mul_nonpos_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

theorem pos_of_mul_neg_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
  lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

theorem pos_of_mul_neg_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
  lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

theorem neg_iff_pos_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : a < 0 ↔ 0 < b :=
  ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

theorem pos_iff_neg_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : 0 < a ↔ b < 0 :=
  ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

lemma sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 ≤ a ^ 2 := by
  obtain ha | ha := le_or_gt 0 a
  · exact pow_succ_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha.le
  have hb : 0 < b := not_le.1 fun hb ↦
    ((add_le_add_left hb a).trans_lt ((add_zero a).trans_lt ha)).ne' hab
  calc
    0 ≤ b ^ 2 := pow_succ_nonneg hb.le _
    _ = b ^ 2 + a * (a + b) := by rw [← hab, mul_zero, add_zero]
    _ = a ^ 2 + (a + b) * b := by rw [add_mul, mul_add, sq, sq, add_comm, add_assoc]
    _ = a ^ 2 := by rw [← hab, zero_mul, add_zero]

@[simp]
lemma sq_nonpos_iff [ExistsAddOfLE R]
    [PosMulMono R] [AddLeftMono R] [NoZeroDivisors R] (r : R) :
    r ^ 2 ≤ 0 ↔ r = 0 := by
  trans r ^ 2 = 0
  · rw [le_antisymm_iff, and_iff_left (sq_nonneg r)]
  · exact sq_eq_zero_iff

alias pow_two_nonneg := sq_nonneg

lemma mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 ≤ a * a := by simpa only [sq] using sq_nonneg a

/-- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff_of_nonneg, mul_self_eq_zero (M₀ := R), mul_self_eq_zero (M₀ := R)] <;>
    apply mul_self_nonneg

lemma eq_zero_of_mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left

end LinearOrderedSemiring

section LinearOrderedCommSemiring

variable [CommSemiring R] [LinearOrder R] {a d : R}

lemma max_mul_mul_le_max_mul_max [PosMulMono R] [MulPosMono R] (b c : R) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    max (a * b) (d * c) ≤ max a c * max d b :=
  have ba : b * a ≤ max d b * max c a :=
    mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b))
  have cd : c * d ≤ max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

/-- Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
lemma two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  simpa [fn_min_add_fn_max (fun x ↦ x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

/-- Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
lemma four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 4 * a * b ≤ (a + b) ^ 2 := by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

/-- Binary and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
lemma two_mul_le_add_of_sq_eq_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] {a b r : R}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b := by
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
  conv_rhs => rw [← pow_two]
  convert four_mul_le_sq_add a b using 1
  rw [mul_mul_mul_comm, two_mul, two_add_two_eq_four, ← pow_two, ht, mul_assoc]

end LinearOrderedCommSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] {a b : R}

-- TODO: Can the following five lemmas be generalised to
-- `[Semiring R] [LinearOrder R] [ExistsAddOfLE R] ..`?

lemma mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftReflectLT R] [AddLeftStrictMono R] :
    a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff (R := R), neg_pos, neg_lt_zero]

lemma mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff (R := R), neg_nonneg, neg_nonpos]

lemma mul_nonneg_iff_neg_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg (R := R)]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_pos_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← mul_neg, mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_neg_imp_nonneg [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_mul, mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

lemma neg_one_lt_zero
    [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStrictMono R] :
    -1 < (0 : R) := neg_lt_zero.2 zero_lt_one

lemma sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftStrictMono R]
    (a : R) : a - 1 < a := sub_lt_iff_lt_add.2 <| lt_add_one a

lemma mul_self_le_mul_self_of_le_of_neg_le
    [MulPosMono R] [PosMulMono R] [AddLeftMono R]
    (h₁ : a ≤ b) (h₂ : -a ≤ b) : a * a ≤ b * b :=
  (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h ↦
    (neg_mul_neg a a).symm.trans_le <|
      mul_le_mul h₂ h₂ (neg_nonneg.2 h) <| (neg_nonneg.2 h).trans h₂

lemma sub_mul_sub_nonneg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : 0 ≤ (x - a) * (x - b) ↔ x ≤ a ∨ b ≤ x := by
  rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos,
    and_iff_right_of_imp h.trans, and_iff_left_of_imp h.trans', or_comm]

lemma sub_mul_sub_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : (x - a) * (x - b) ≤ 0 ↔ a ≤ x ∧ x ≤ b := by
  rw [mul_nonpos_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos, or_iff_left_iff_imp, and_comm]
  exact And.imp h.trans h.trans'

lemma sub_mul_sub_pos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : 0 < (x - a) * (x - b) ↔ x < a ∨ b < x := by
  rw [mul_pos_iff, sub_pos, sub_pos, sub_neg, sub_neg, and_iff_right_of_imp h.trans_lt,
    and_iff_left_of_imp h.trans_lt', or_comm]

lemma sub_mul_sub_neg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : (x - a) * (x - b) < 0 ↔ a < x ∧ x < b := by
  rw [mul_neg_iff, sub_pos, sub_pos, sub_neg, sub_neg, or_iff_left_iff_imp, and_comm]
  exact And.imp h.trans_lt h.trans_lt'

end LinearOrderedRing
end OrderedCommRing
