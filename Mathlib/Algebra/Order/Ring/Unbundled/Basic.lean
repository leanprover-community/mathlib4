/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Tauto

/-!
# Basic facts for ordered rings and semirings

This file develops the basics of ordered (semi)rings in an unbundled fashion for later use with
the bundled classes from `Algebra.Order.Ring.Defs`.

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

Each section is labelled with a corresponding bundled ordered ring typeclass in mind. Mixin's for
relating the order structures and ring structures are added as needed.

TODO: the mixin assumptiosn can be relaxed in most cases

-/

assert_not_exists OrderedCommMonoid
assert_not_exists MonoidHom

open Function

universe u

variable {α : Type u} {β : Type*}

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/


theorem add_one_le_two_mul [LE α] [Semiring α] [AddLeftMono α] {a : α}
    (a1 : 1 ≤ a) : a + 1 ≤ 2 * a :=
  calc
    a + 1 ≤ a + a := add_le_add_left a1 a
    _ = 2 * a := (two_mul _).symm

section OrderedSemiring

variable [Semiring α] [Preorder α] {a b c d : α}

-- Porting note: it's unfortunate we need to write `(@one_le_two α)` here.
theorem add_le_mul_two_add [ZeroLEOneClass α] [MulPosMono α] [AddLeftMono α]
    (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) :=
      add_le_add_left (add_le_add a2 <| le_mul_of_one_le_left b0 <| (@one_le_two α).trans a2) a
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

theorem mul_le_mul_of_nonpos_left [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ ≤ d * a := mul_le_mul_of_nonneg_left h <| hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ ≤ a * d := mul_le_mul_of_nonneg_right h <| hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

theorem mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

theorem mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE α] [MulPosMono α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonneg_left hbd hc

theorem mul_le_mul_of_nonneg_of_nonpos' [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE α] [MulPosMono α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_right hac hb).trans <| mul_le_mul_of_nonpos_left hdb hc

theorem mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE α] [MulPosMono α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonpos_left hdb hc

theorem mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_left hdb ha).trans <| mul_le_mul_of_nonpos_right hca hd

/-- Variant of `mul_le_of_le_one_left` for `b` non-positive instead of non-negative. -/
theorem le_mul_of_le_one_left [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hb : b ≤ 0) (h : a ≤ 1) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/-- Variant of `le_mul_of_one_le_left` for `b` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_left [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/-- Variant of `mul_le_of_le_one_right` for `a` non-positive instead of non-negative. -/
theorem le_mul_of_le_one_right [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

/-- Variant of `le_mul_of_one_le_right` for `a` non-positive instead of non-negative. -/
theorem mul_le_of_one_le_right [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

section Monotone

variable [Preorder β] {f g : β → α}

theorem antitone_mul_left [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a : α} (ha : a ≤ 0) : Antitone (a * ·) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

theorem antitone_mul_right [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a : α} (ha : a ≤ 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

theorem Monotone.const_mul_of_nonpos [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => a * f x :=
  (antitone_mul_left ha).comp_monotone hf

theorem Monotone.mul_const_of_nonpos [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => f x * a :=
  (antitone_mul_right ha).comp_monotone hf

theorem Antitone.const_mul_of_nonpos [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => a * f x :=
  (antitone_mul_left ha).comp hf

theorem Antitone.mul_const_of_nonpos [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => f x * a :=
  (antitone_mul_right ha).comp hf

theorem Antitone.mul_monotone [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Antitone f) (hg : Monotone g) (hf₀ : ∀ x, f x ≤ 0)
    (hg₀ : ∀ x, 0 ≤ g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

theorem Monotone.mul_antitone [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Monotone f) (hg : Antitone g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, g x ≤ 0) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

theorem Antitone.mul [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hf : Antitone f) (hg : Antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

end Monotone
end OrderedSemiring

section OrderedCommRing

section StrictOrderedSemiring

variable [Semiring α] [PartialOrder α] {a b c d : α}

theorem lt_two_mul_self [ZeroLEOneClass α] [MulPosStrictMono α] [NeZero (R := α) 1]
    [AddLeftStrictMono α] (ha : 0 < a) : a < 2 * a :=
  lt_mul_of_one_lt_left ha one_lt_two

theorem mul_lt_mul_of_neg_left [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ < d * a := mul_lt_mul_of_pos_left h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

theorem mul_lt_mul_of_neg_right [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ < a * d := mul_lt_mul_of_pos_right h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

theorem mul_pos_of_neg_of_neg [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

/-- Variant of `mul_lt_of_lt_one_left` for `b` negative instead of positive. -/
theorem lt_mul_of_lt_one_left [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/-- Variant of `lt_mul_of_one_lt_left` for `b` negative instead of positive. -/
theorem mul_lt_of_one_lt_left [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/-- Variant of `mul_lt_of_lt_one_right` for `a` negative instead of positive. -/
theorem lt_mul_of_lt_one_right [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

/-- Variant of `lt_mul_of_lt_one_right` for `a` negative instead of positive. -/
theorem mul_lt_of_one_lt_right [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

section Monotone

variable [Preorder β] {f : β → α}

theorem strictAnti_mul_left [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    {a : α} (ha : a < 0) : StrictAnti (a * ·) := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

theorem strictAnti_mul_right [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    {a : α} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

theorem StrictMono.const_mul_of_neg [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => a * f x :=
  (strictAnti_mul_left ha).comp_strictMono hf

theorem StrictMono.mul_const_of_neg [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => f x * a :=
  (strictAnti_mul_right ha).comp_strictMono hf

theorem StrictAnti.const_mul_of_neg [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => a * f x :=
  (strictAnti_mul_left ha).comp hf

theorem StrictAnti.mul_const_of_neg [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => f x * a :=
  (strictAnti_mul_right ha).comp hf

end Monotone

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul [ExistsAddOfLE α] [MulPosMono α]
    [AddLeftMono α] [AddLeftReflectLE α]
    (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hab hd) _

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_le_mul_add_mul' [ExistsAddOfLE α] [MulPosMono α]
    [AddLeftMono α] [AddLeftReflectLE α]
    (hba : b ≤ a) (hdc : d ≤ c) : a * d + b * c ≤ a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

variable [AddLeftReflectLT α]

/-- Binary strict **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddLeftStrictMono α]
    (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_lt_add_left (mul_lt_mul_of_pos_right hab hd) _

/-- Binary **rearrangement inequality**. -/
lemma mul_add_mul_lt_mul_add_mul' [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddLeftStrictMono α]
    (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

end StrictOrderedSemiring

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] {a b c : α}

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
    [MulPosStrictMono α] [PosMulStrictMono α]
    (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine Decidable.or_iff_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_le hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

theorem nonneg_of_mul_nonneg_left [MulPosStrictMono α]
    (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_le h

theorem nonneg_of_mul_nonneg_right [PosMulStrictMono α]
    (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_le h

theorem nonpos_of_mul_nonpos_left [PosMulStrictMono α]
    (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_le h

theorem nonpos_of_mul_nonpos_right [PosMulStrictMono α]
    (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_le h

@[simp]
theorem mul_nonneg_iff_of_pos_left [PosMulStrictMono α]
    (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  convert mul_le_mul_left h
  simp

@[simp]
theorem mul_nonneg_iff_of_pos_right [MulPosStrictMono α]
    (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  simpa using (mul_le_mul_right h : 0 * c ≤ b * c ↔ 0 ≤ b)

theorem add_le_mul_of_left_le_right [ZeroLEOneClass α] [NeZero (R := α) 1]
    [MulPosStrictMono α] [AddLeftMono α]
    (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
  have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ ≤ a := a2
      _ ≤ b := ab
  calc
    a + b ≤ b + b := add_le_add_right ab b
    _ = 2 * b := (two_mul b).symm
    _ ≤ a * b := (mul_le_mul_right this).mpr a2

-- Porting note: we used to not need the type annotation on `(0 : α)` at the start of the `calc`.
theorem add_le_mul_of_right_le_left [ZeroLEOneClass α] [NeZero (R := α) 1]
    [AddLeftMono α] [PosMulStrictMono α]
    (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
  have : 0 < a :=
    calc (0 : α)
      _ < 2 := zero_lt_two
      _ ≤ b := b2
      _ ≤ a := ba
  calc
    a + b ≤ a + a := add_le_add_left ba a
    _ = a * 2 := (mul_two a).symm
    _ ≤ a * b := (mul_le_mul_left this).mpr b2

theorem add_le_mul [ZeroLEOneClass α] [NeZero (R := α) 1]
    [MulPosStrictMono α] [PosMulStrictMono α] [AddLeftMono α]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
  if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_le hab)

theorem add_le_mul' [ZeroLEOneClass α] [NeZero (R := α) 1]
    [MulPosStrictMono α] [PosMulStrictMono α] [AddLeftMono α]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
  (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

theorem mul_nonneg_iff_right_nonneg_of_pos [PosMulStrictMono α]
    (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
  ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

theorem mul_nonneg_iff_left_nonneg_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
  ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩

theorem nonpos_of_mul_nonneg_left [PosMulStrictMono α]
    (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_le

theorem nonpos_of_mul_nonneg_right [MulPosStrictMono α]
    (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_le

@[simp]
theorem Units.inv_pos
    [ZeroLEOneClass α] [NeZero (R := α) 1] [PosMulStrictMono α]
    {u : αˣ} : (0 : α) < ↑u⁻¹ ↔ (0 : α) < u :=
  have : ∀ {u : αˣ}, (0 : α) < u → (0 : α) < ↑u⁻¹ := @fun u h =>
    (mul_pos_iff_of_pos_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]
theorem Units.inv_neg
    [ZeroLEOneClass α] [NeZero (R := α) 1] [MulPosMono α] [PosMulMono α]
    {u : αˣ} : ↑u⁻¹ < (0 : α) ↔ ↑u < (0 : α) :=
  have : ∀ {u : αˣ}, ↑u < (0 : α) → ↑u⁻¹ < (0 : α) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

theorem cmp_mul_pos_left [PosMulStrictMono α]
    (ha : 0 < a) (b c : α) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_mul_left_of_pos ha).cmp_map_eq b c

theorem cmp_mul_pos_right [MulPosStrictMono α]
    (ha : 0 < a) (b c : α) : cmp (b * a) (c * a) = cmp b c :=
  (strictMono_mul_right_of_pos ha).cmp_map_eq b c

theorem mul_max_of_nonneg [PosMulMono α]
    (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_max

theorem mul_min_of_nonneg [PosMulMono α]
    (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_min

theorem max_mul_of_nonneg [MulPosMono α]
    (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_max

theorem min_mul_of_nonneg [MulPosMono α]
    (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_min

theorem le_of_mul_le_of_one_le
    [ZeroLEOneClass α] [NeZero (R := α) 1] [MulPosStrictMono α] [PosMulMono α]
    {a b c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
  le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) <| zero_lt_one.trans_le hc

theorem nonneg_le_nonneg_of_sq_le_sq [PosMulStrictMono α] [MulPosMono α]
    {a b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
  le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_le h

theorem mul_self_le_mul_self_iff [PosMulStrictMono α] [MulPosMono α]
    {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
  ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

theorem mul_self_lt_mul_self_iff [PosMulStrictMono α] [MulPosMono α]
    {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
  ((@strictMonoOn_mul_self α _).lt_iff_lt h1 h2).symm

theorem mul_self_inj [PosMulStrictMono α] [MulPosMono α]
    {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  (@strictMonoOn_mul_self α _).eq_iff_eq h1 h2

lemma sign_cases_of_C_mul_pow_nonneg [PosMulStrictMono α]
    (h : ∀ n, 0 ≤ a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 ≤ b := by
  have : 0 ≤ a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_gt.imp_right fun ha ↦ ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1

theorem mul_pos_iff [ExistsAddOfLE α] [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftStrictMono α] [AddLeftReflectLT α] :
    0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

theorem mul_nonneg_iff [ExistsAddOfLE α] [MulPosStrictMono α] [PosMulStrictMono α]
    [AddLeftReflectLE α] [AddLeftMono α]:
    0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

/-- Out of three elements of a `LinearOrderedRing`, two must have the same sign. -/
theorem mul_nonneg_of_three [ExistsAddOfLE α] [MulPosStrictMono α] [PosMulStrictMono α]
    [AddLeftMono α] [AddLeftReflectLE α]
    (a b c : α) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  -- Porting note used to be by `itauto` from here
  exact Or.elim or_c
    (fun (h0 : 0 ≤ c) =>
      Or.elim or_b
        (fun (h1 : 0 ≤ b) =>
            Or.elim or_a (fun (h2 : 0 ≤ a) => Or.inl (Or.inl ⟨h2, h1⟩))
              (fun (_ : a ≤ 0) => Or.inr (Or.inl (Or.inl ⟨h1, h0⟩))))
        (fun (h1 : b ≤ 0) =>
            Or.elim or_a (fun (h3 : 0 ≤ a) => Or.inr (Or.inr (Or.inl ⟨h0, h3⟩)))
              (fun (h3 : a ≤ 0) => Or.inl (Or.inr ⟨h3, h1⟩))))
    (fun (h0 : c ≤ 0) =>
      Or.elim or_b
        (fun (h4 : 0 ≤ b) =>
            Or.elim or_a (fun (h5 : 0 ≤ a) => Or.inl (Or.inl ⟨h5, h4⟩))
              (fun (h5 : a ≤ 0) => Or.inr (Or.inr (Or.inr ⟨h0, h5⟩))))
        (fun (h4 : b ≤ 0) =>
            Or.elim or_a (fun (_ : 0 ≤ a) => Or.inr (Or.inl (Or.inr ⟨h4, h0⟩)))
              (fun (h6 : a ≤ 0) => Or.inl (Or.inr ⟨h6, h4⟩))))

lemma mul_nonneg_iff_pos_imp_nonneg [ExistsAddOfLE α] [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftMono α] [AddLeftReflectLE α] :
    0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

@[simp]
theorem mul_le_mul_left_of_neg [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
  (strictAnti_mul_left h).le_iff_le

@[simp]
theorem mul_le_mul_right_of_neg [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  (strictAnti_mul_right h).le_iff_le

@[simp]
theorem mul_lt_mul_left_of_neg [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
  (strictAnti_mul_left h).lt_iff_lt

@[simp]
theorem mul_lt_mul_right_of_neg [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightStrictMono α] [AddRightReflectLT α]
    {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
  (strictAnti_mul_right h).lt_iff_lt

theorem lt_of_mul_lt_mul_of_nonpos_left [ExistsAddOfLE α] [PosMulMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
  (antitone_mul_left hc).reflect_lt h

theorem lt_of_mul_lt_mul_of_nonpos_right [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
  (antitone_mul_right hc).reflect_lt h

theorem cmp_mul_neg_left [ExistsAddOfLE α] [PosMulStrictMono α]
    [AddRightReflectLT α] [AddRightStrictMono α]
    {a : α} (ha : a < 0) (b c : α) : cmp (a * b) (a * c) = cmp c b :=
  (strictAnti_mul_left ha).cmp_map_eq b c

theorem cmp_mul_neg_right [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightReflectLT α] [AddRightStrictMono α]
    {a : α} (ha : a < 0) (b c : α) : cmp (b * a) (c * a) = cmp c b :=
  (strictAnti_mul_right ha).cmp_map_eq b c

@[simp]
theorem mul_self_pos [ExistsAddOfLE α] [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftStrictMono α] [AddLeftReflectLT α]
    {a : α} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_lt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]

theorem nonneg_of_mul_nonpos_left [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_le

theorem nonneg_of_mul_nonpos_right [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_le

theorem pos_of_mul_neg_left [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
  lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt

theorem pos_of_mul_neg_right [ExistsAddOfLE α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
  lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt

theorem neg_iff_pos_of_mul_neg [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hab : a * b < 0) : a < 0 ↔ 0 < b :=
  ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

theorem pos_iff_neg_of_mul_neg [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α]
    [AddRightMono α] [AddRightReflectLE α]
    (hab : a * b < 0) : 0 < a ↔ b < 0 :=
  ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

lemma sq_nonneg [IsRightCancelAdd α]
    [ZeroLEOneClass α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftStrictMono α]
    (a : α) : 0 ≤ a ^ 2 := by
  obtain ha | ha := le_total 0 a
  · exact pow_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha
  calc
    0 ≤ b ^ 2 := pow_nonneg (not_lt.1 fun hb ↦ hab.not_gt <| add_neg_of_nonpos_of_neg ha hb) _
    _ = a ^ 2 := add_left_injective (a * b) ?_
  calc
    b ^ 2 + a * b = (a + b) * b := by rw [add_comm, sq, add_mul]
    _ = a * (a + b) := by simp [← hab]
    _ = a ^ 2 + a * b := by rw [sq, mul_add]

alias pow_two_nonneg := sq_nonneg

lemma mul_self_nonneg [IsRightCancelAdd α]
    [ZeroLEOneClass α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftStrictMono α]
    (a : α) : 0 ≤ a * a := by simpa only [sq] using sq_nonneg a

/-- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero [IsRightCancelAdd α] [NoZeroDivisors α]
    [ZeroLEOneClass α] [ExistsAddOfLE α] [PosMulMono α]
    [AddLeftMono α] [AddLeftStrictMono α] :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff_of_nonneg, mul_self_eq_zero (M₀ := α), mul_self_eq_zero (M₀ := α)] <;>
    apply mul_self_nonneg

lemma eq_zero_of_mul_self_add_mul_self_eq_zero [IsRightCancelAdd α] [NoZeroDivisors α]
    [ZeroLEOneClass α] [ExistsAddOfLE α] [PosMulMono α]
    [AddLeftMono α] [AddLeftStrictMono α]
    (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left

end LinearOrderedSemiring

section LinearOrderedCommSemiring

variable [CommSemiring α] [LinearOrder α] {a d : α}

lemma max_mul_mul_le_max_mul_max [PosMulMono α] [MulPosMono α] (b c : α) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    max (a * b) (d * c) ≤ max a c * max d b :=
  have ba : b * a ≤ max d b * max c a :=
    mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b))
  have cd : c * d ≤ max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

/-- Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
lemma two_mul_le_add_sq [ExistsAddOfLE α] [MulPosStrictMono α]
    [AddLeftReflectLE α] [AddLeftMono α]
    (a b : α) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  simpa [fn_min_add_fn_max (fun x ↦ x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

/-- Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
lemma four_mul_le_sq_add [ExistsAddOfLE α] [MulPosStrictMono α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] [CovariantClass α α (· + ·) (· ≤ ·)]
    (a b : α) : 4 * a * b ≤ (a + b) ^ 2 := by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

end LinearOrderedCommSemiring

section LinearOrderedRing

variable [Ring α] [LinearOrder α] {a b : α}

-- TODO: Can the following five lemmas be generalised to
-- `[Semiring α] [LinearOrder α] [ExistsAddOfLE α] ..`?

lemma mul_neg_iff [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftReflectLT α] [AddLeftStrictMono α] :
    a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff (α := α), neg_pos, neg_lt_zero]

lemma mul_nonpos_iff [MulPosStrictMono α] [PosMulStrictMono α]
    [AddLeftReflectLE α] [AddLeftMono α] :
    a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff (α := α), neg_nonneg, neg_nonpos]

lemma mul_nonneg_iff_neg_imp_nonpos [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftMono α] [AddLeftReflectLE α] :
    0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg (α := α)]; simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_pos_imp_nonpos [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftMono α] [AddLeftReflectLE α] :
    a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← mul_neg, mul_nonneg_iff_pos_imp_nonneg (α := α)]
  simp only [neg_pos, neg_nonneg]

lemma mul_nonpos_iff_neg_imp_nonneg [PosMulStrictMono α] [MulPosStrictMono α]
    [AddLeftMono α] [AddLeftReflectLE α] :
    a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_mul, mul_nonneg_iff_pos_imp_nonneg (α := α)]
  simp only [neg_pos, neg_nonneg]

lemma neg_one_lt_zero
    [ZeroLEOneClass α] [NeZero (R := α) 1] [AddLeftStrictMono α] :
    -1 < (0 : α) := neg_lt_zero.2 zero_lt_one

lemma sub_one_lt [ZeroLEOneClass α] [NeZero (R := α) 1]
    [AddLeftStrictMono α]
    (a : α) : a - 1 < a := sub_lt_iff_lt_add.2 <| lt_add_one a

lemma mul_self_le_mul_self_of_le_of_neg_le
    [MulPosMono α] [PosMulMono α] [AddLeftMono α]
    (h₁ : a ≤ b) (h₂ : -a ≤ b) : a * a ≤ b * b :=
  (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h ↦
    (neg_mul_neg a a).symm.trans_le <|
      mul_le_mul h₂ h₂ (neg_nonneg.2 h) <| (neg_nonneg.2 h).trans h₂

end LinearOrderedRing
end OrderedCommRing
