/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Data.Ordering.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`Mul` or `MulOneClass`.

-/


-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.
open Function

section Nat

instance Nat.instMulLeftMono : MulLeftMono ℕ where
  elim := fun _ _ _ h => mul_le_mul_left _ h

end Nat

section Int

instance Int.instAddLeftMono : AddLeftMono ℤ where
  elim := fun _ _ _ h => Int.add_le_add_left h _

end Int

variable {α β : Type*}

section Mul

variable [Mul α]

section LE

variable [LE α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive (attr := gcongr) add_le_add_left]
theorem mul_le_mul_left' [MulLeftMono α] {b c : α} (bc : b ≤ c) (a : α) :
    a * b ≤ a * c :=
  CovariantClass.elim _ bc

@[to_additive le_of_add_le_add_left]
theorem le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b c : α}
    (bc : a * b ≤ a * c) :
    b ≤ c :=
  ContravariantClass.elim _ bc

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive (attr := gcongr) add_le_add_right]
theorem mul_le_mul_right' [i : MulRightMono α] {b c : α} (bc : b ≤ c)
    (a : α) :
    b * a ≤ c * a :=
  i.elim a bc

@[to_additive le_of_add_le_add_right]
theorem le_of_mul_le_mul_right' [i : MulRightReflectLE α] {a b c : α}
    (bc : b * a ≤ c * a) :
    b ≤ c :=
  i.elim a bc

@[to_additive (attr := simp)]
theorem mul_le_mul_iff_left [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b c : α} :
    a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov α α (· * ·) (· ≤ ·) a

@[to_additive (attr := simp)]
theorem mul_le_mul_iff_right [MulRightMono α]
    [MulRightReflectLE α] (a : α) {b c : α} :
    b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a

end LE

section LT

variable [LT α]

@[to_additive (attr := simp)]
theorem mul_lt_mul_iff_left [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b c : α} :
    a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a

@[to_additive (attr := simp)]
theorem mul_lt_mul_iff_right [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b c : α} :
    b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a

@[to_additive (attr := gcongr) add_lt_add_left]
theorem mul_lt_mul_left' [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c :=
  CovariantClass.elim _ bc

@[to_additive lt_of_add_lt_add_left]
theorem lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b c : α}
    (bc : a * b < a * c) :
    b < c :=
  ContravariantClass.elim _ bc

@[to_additive (attr := gcongr) add_lt_add_right]
theorem mul_lt_mul_right' [i : MulRightStrictMono α] {b c : α} (bc : b < c)
    (a : α) :
    b * a < c * a :=
  i.elim a bc

@[to_additive lt_of_add_lt_add_right]
theorem lt_of_mul_lt_mul_right' [i : MulRightReflectLT α] {a b c : α}
    (bc : b * a < c * a) :
    b < c :=
  i.elim a bc

end LT

section Preorder

variable [Preorder α]

@[to_additive]
lemma mul_left_mono [MulLeftMono α] {a : α} : Monotone (a * ·) :=
  fun _ _ h ↦ mul_le_mul_left' h _

@[to_additive]
lemma mul_right_mono [MulRightMono α] {a : α} : Monotone (· * a) :=
  fun _ _ h ↦ mul_le_mul_right' h _

@[to_additive]
lemma mul_left_strictMono [MulLeftStrictMono α] {a : α} : StrictMono (a * ·) :=
  fun _ _ h ↦ mul_lt_mul_left' h _

@[to_additive]
lemma mul_right_strictMono [MulRightStrictMono α] {a : α} : StrictMono (· * a) :=
  fun _ _ h ↦ mul_lt_mul_right' h _

@[to_additive (attr := gcongr)]
theorem mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α]
    [MulRightStrictMono α]
    {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_left' h₂ a
    _ < b * d := mul_lt_mul_right' h₁ d

alias add_lt_add := add_lt_add_of_lt_of_lt

@[to_additive]
theorem mul_lt_mul_of_le_of_lt [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive]
theorem mul_lt_mul_of_lt_of_le [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d :=
  (mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)

/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
theorem Left.mul_lt_mul [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂

/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
theorem Right.mul_lt_mul [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive (attr := gcongr) add_le_add]
theorem mul_le_mul' [MulLeftMono α] [MulRightMono α]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d :=
  (mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
theorem mul_le_mul_three [MulLeftMono α]
    [MulRightMono α] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) :
    a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]
theorem mul_lt_of_mul_lt_left [MulLeftMono α] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) :
    a * d < c :=
  (mul_le_mul_left' hle a).trans_lt h

@[to_additive]
theorem mul_le_of_mul_le_left [MulLeftMono α] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) :
    a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ _ a _ _ _ hle h

@[to_additive]
theorem mul_lt_of_mul_lt_right [MulRightMono α] {a b c d : α}
    (h : a * b < c) (hle : d ≤ a) :
    d * b < c :=
  (mul_le_mul_right' hle b).trans_lt h

@[to_additive]
theorem mul_le_of_mul_le_right [MulRightMono α] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) :
    d * b ≤ c :=
  (mul_le_mul_right' hle b).trans h

@[to_additive]
theorem lt_mul_of_lt_mul_left [MulLeftMono α] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) :
    a < b * d :=
  h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
theorem le_mul_of_le_mul_left [MulLeftMono α] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) :
    a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ _ b _ _ _ hle h

@[to_additive]
theorem lt_mul_of_lt_mul_right [MulRightMono α] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) :
    a < d * c :=
  h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
theorem le_mul_of_le_mul_right [MulRightMono α] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) :
    a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c)

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
theorem mul_left_cancel'' [MulLeftReflectLE α] {a b c : α} (h : a * b = a * c) :
    b = c :=
  (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[to_additive]
theorem mul_right_cancel'' [MulRightReflectLE α] {a b c : α}
    (h : a * b = c * b) :
    a = c :=
  (le_of_mul_le_mul_right' h.le).antisymm (le_of_mul_le_mul_right' h.ge)

@[to_additive] lemma mul_le_mul_iff_of_ge [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  haveI := mulLeftMono_of_mulLeftStrictMono α
  haveI := mulRightMono_of_mulRightStrictMono α
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_gt ?_, fun hb ↦ h.not_gt ?_⟩
  exacts [mul_lt_mul_of_lt_of_le ha hb, mul_lt_mul_of_le_of_lt ha hb]

@[to_additive] theorem mul_eq_mul_iff_eq_and_eq [MulLeftStrictMono α]
    [MulRightStrictMono α] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d := by
  haveI := mulLeftMono_of_mulLeftStrictMono α
  haveI := mulRightMono_of_mulRightStrictMono α
  rw [le_antisymm_iff, eq_true (mul_le_mul' hac hbd), true_and, mul_le_mul_iff_of_ge hac hbd]

@[to_additive]
lemma mul_left_inj_of_comparable [MulRightStrictMono α] {a b c : α} (h : b ≤ c ∨ c ≤ b) :
    c * a = b * a ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
  · exact mul_lt_mul_right' (h.lt_of_ne' h') a |>.ne'
  · exact mul_lt_mul_right' (h.lt_of_ne h') a |>.ne

@[to_additive]
lemma mul_right_inj_of_comparable [MulLeftStrictMono α] {a b c : α} (h : b ≤ c ∨ c ≤ b) :
    a * c = a * b ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
  · exact mul_lt_mul_left' (h.lt_of_ne' h') a |>.ne'
  · exact mul_lt_mul_left' (h.lt_of_ne h') a |>.ne

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b c d : α}

@[to_additive]
theorem trichotomy_of_mul_eq_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b = c * d) : (a = c ∧ b = d) ∨ a < c ∨ b < d := by
  obtain hac | rfl | hca := lt_trichotomy a c
  · right; left; exact hac
  · left; simpa using mul_right_inj_of_comparable (LinearOrder.le_total d b)|>.1 h
  · obtain hbd | rfl | hdb := lt_trichotomy b d
    · right; right; exact hbd
    · exact False.elim <| ne_of_lt (mul_lt_mul_right' hca b) h.symm
    · exact False.elim <| ne_of_lt (mul_lt_mul_of_lt_of_lt hca hdb) h.symm

@[to_additive]
lemma mul_max [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    a * max b c = max (a * b) (a * c) := mul_left_mono.map_max

@[to_additive]
lemma max_mul [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a b c : α) :
    max a b * c = max (a * c) (b * c) := mul_right_mono.map_max

@[to_additive]
lemma mul_min [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    a * min b c = min (a * b) (a * c) := mul_left_mono.map_min

@[to_additive]
lemma min_mul [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a b c : α) :
    min a b * c = min (a * c) (b * c) := mul_right_mono.map_min

@[to_additive] lemma min_lt_max_of_mul_lt_mul
    [MulLeftMono α] [MulRightMono α]
    (h : a * b < c * d) : min a b < max c d := by
  simp_rw [min_lt_iff, lt_max_iff]; contrapose! h; exact mul_le_mul' h.1.1 h.2.2

@[to_additive] lemma Left.min_le_max_of_mul_le_mul
    [MulLeftStrictMono α] [MulRightMono α]
    (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_le_of_lt h.1.1.le h.2.2

@[to_additive] lemma Right.min_le_max_of_mul_le_mul
    [MulLeftMono α] [MulRightStrictMono α]
    (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_lt_of_le h.1.1 h.2.2.le

@[to_additive] lemma min_le_max_of_mul_le_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b ≤ c * d) : min a b ≤ max c d :=
  haveI := mulRightMono_of_mulRightStrictMono α
  Left.min_le_max_of_mul_le_mul h

/-- Not an instance, to avoid loops with `IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono`. -/
@[to_additive]
theorem MulLeftStrictMono.toIsLeftCancelMul [MulLeftStrictMono α] : IsLeftCancelMul α where
  mul_left_cancel _ _ _ h := mul_left_strictMono.injective h

/-- Not an instance, to avoid loops with `IsRightCancelMul.mulRightStrictMono_of_mulRightMono`. -/
@[to_additive]
theorem MulRightStrictMono.toIsRightCancelMul [MulRightStrictMono α] : IsRightCancelMul α where
  mul_right_cancel _ _ _ h := mul_right_strictMono.injective h

end LinearOrder

section LinearOrder
variable [LinearOrder α] [MulLeftMono α] [MulRightMono α] {a b c d : α}

@[to_additive max_add_add_le_max_add_max]
theorem max_mul_mul_le_max_mul_max' : max (a * b) (c * d) ≤ max a c * max b d :=
  max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _) <|
    mul_le_mul' (le_max_right _ _) <| le_max_right _ _

@[to_additive min_add_min_le_min_add_add]
theorem min_mul_min_le_min_mul_mul' : min a c * min b d ≤ min (a * b) (c * d) :=
  le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _) <|
    mul_le_mul' (min_le_right _ _) <| min_le_right _ _

end LinearOrder
end Mul

-- using one
section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

@[to_additive le_add_of_nonneg_right]
theorem le_mul_of_one_le_right' [MulLeftMono α] {a b : α} (h : 1 ≤ b) :
    a ≤ a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_right]
theorem mul_le_of_le_one_right' [MulLeftMono α] {a b : α} (h : b ≤ 1) :
    a * b ≤ a :=
  calc
    a * b ≤ a * 1 := mul_le_mul_left' h a
    _ = a := mul_one a

@[to_additive le_add_of_nonneg_left]
theorem le_mul_of_one_le_left' [MulRightMono α] {a b : α} (h : 1 ≤ b) :
    a ≤ b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ ≤ b * a := mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_left]
theorem mul_le_of_le_one_left' [MulRightMono α] {a b : α} (h : b ≤ 1) :
    b * a ≤ a :=
  calc
    b * a ≤ 1 * a := mul_le_mul_right' h a
    _ = a := one_mul a

@[to_additive]
theorem one_le_of_le_mul_right [MulLeftReflectLE α] {a b : α} (h : a ≤ a * b) :
    1 ≤ b :=
  le_of_mul_le_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
theorem le_one_of_mul_le_right [MulLeftReflectLE α] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 :=
  le_of_mul_le_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
theorem one_le_of_le_mul_left [MulRightReflectLE α] {a b : α}
    (h : b ≤ a * b) :
    1 ≤ a :=
  le_of_mul_le_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive]
theorem le_one_of_mul_le_left [MulRightReflectLE α] {a b : α}
    (h : a * b ≤ b) :
    a ≤ 1 :=
  le_of_mul_le_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive (attr := simp) le_add_iff_nonneg_right]
theorem le_mul_iff_one_le_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) le_add_iff_nonneg_left]
theorem le_mul_iff_one_le_left' [MulRightMono α]
    [MulRightReflectLE α] (a : α) {b : α} :
    a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)

@[to_additive (attr := simp) add_le_iff_nonpos_right]
theorem mul_le_iff_le_one_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) add_le_iff_nonpos_left]
theorem mul_le_iff_le_one_left' [MulRightMono α]
    [MulRightReflectLE α] {a b : α} :
    a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)

end LE

section LT

variable [LT α]

@[to_additive lt_add_of_pos_right]
theorem lt_mul_of_one_lt_right' [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b) :
    a < a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_left' h a

@[to_additive add_lt_of_neg_right]
theorem mul_lt_of_lt_one_right' [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1) :
    a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_left' h a
    _ = a := mul_one a

@[to_additive lt_add_of_pos_left]
theorem lt_mul_of_one_lt_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : 1 < b) :
    a < b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_right' h a

@[to_additive add_lt_of_neg_left]
theorem mul_lt_of_lt_one_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : b < 1) :
    b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_right' h a
    _ = a := one_mul a

@[to_additive]
theorem one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b : α} (h : a < a * b) :
    1 < b :=
  lt_of_mul_lt_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
theorem lt_one_of_mul_lt_right [MulLeftReflectLT α] {a b : α} (h : a * b < a) :
    b < 1 :=
  lt_of_mul_lt_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
theorem one_lt_of_lt_mul_left [MulRightReflectLT α] {a b : α}
    (h : b < a * b) :
    1 < a :=
  lt_of_mul_lt_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive]
theorem lt_one_of_mul_lt_left [MulRightReflectLT α] {a b : α}
    (h : a * b < b) :
    a < 1 :=
  lt_of_mul_lt_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive (attr := simp) lt_add_iff_pos_right]
theorem lt_mul_iff_one_lt_right' [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b : α} :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) lt_add_iff_pos_left]
theorem lt_mul_iff_one_lt_left' [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)

@[to_additive (attr := simp) add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [MulLeftStrictMono α]
    [MulLeftReflectLT α] {a b : α} :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) add_lt_iff_neg_right]
theorem mul_lt_iff_lt_one_right' [MulRightStrictMono α]
    [MulRightReflectLT α] {a : α} (b : α) : a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)

end LT

section Preorder

variable [Preorder α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/


@[to_additive]
theorem mul_le_of_le_of_le_one [MulLeftMono α] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) :
    b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc

@[to_additive]
theorem mul_lt_of_le_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc

@[to_additive]
theorem mul_lt_of_lt_of_le_one [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a ≤ 1) :
    b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]
theorem mul_lt_of_lt_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_le_one`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonpos`."]
theorem Left.mul_le_one [MulLeftMono α] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_nonpos_of_neg`."]
theorem Left.mul_lt_one_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : a ≤ 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_neg_of_nonpos`."]
theorem Left.mul_lt_one_of_lt_of_le [MulLeftMono α] {a b : α} (ha : a < 1)
    (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg`."]
theorem Left.mul_lt_one [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one'`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg'`."]
theorem Left.mul_lt_one' [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


@[to_additive]
theorem le_mul_of_le_of_one_le [MulLeftMono α] {a b c : α} (hbc : b ≤ c)
    (ha : 1 ≤ a) :
    b ≤ c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c

@[to_additive]
theorem lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b ≤ c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c

@[to_additive]
theorem lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 ≤ a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c

@[to_additive]
theorem lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c

@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_le_mul`. -/
@[to_additive Left.add_nonneg "Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonneg`."]
theorem Left.one_le_mul [MulLeftMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_nonneg_of_pos`."]
theorem Left.one_lt_mul_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : 1 ≤ a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_pos_of_nonneg`."]
theorem Left.one_lt_mul_of_lt_of_le [MulLeftMono α] {a b : α} (ha : 1 < a)
    (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul`. -/
@[to_additive Left.add_pos "Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos`."]
theorem Left.one_lt_mul [MulLeftStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul'`. -/
@[to_additive Left.add_pos' "Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos'`."]
theorem Left.one_lt_mul' [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


@[to_additive]
theorem mul_le_of_le_one_of_le [MulRightMono α] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) :
    a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc

@[to_additive]
theorem mul_lt_of_lt_one_of_le [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hbc : b ≤ c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc

@[to_additive]
theorem mul_lt_of_le_one_of_lt [MulRightMono α] {a b c : α} (ha : a ≤ 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]
theorem mul_lt_of_lt_one_of_lt [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [MulRightMono α] {a b c : α} (ha : a < 1)
    (hbc : b < c) :
    a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_le_one`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonpos`."]
theorem Right.mul_le_one [MulRightMono α] {a b : α} (ha : a ≤ 1)
    (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      "Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_neg_of_nonpos`."]
theorem Right.mul_lt_one_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      "Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_nonpos_of_neg`."]
theorem Right.mul_lt_one_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : a ≤ 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg`."]
theorem Right.mul_lt_one [MulRightStrictMono α] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one'`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg'`."]
theorem Right.mul_lt_one' [MulRightMono α] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


@[to_additive]
theorem le_mul_of_one_le_of_le [MulRightMono α] {a b c : α} (ha : 1 ≤ a)
    (hbc : b ≤ c) :
    b ≤ a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c

@[to_additive]
theorem lt_mul_of_one_lt_of_le [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b ≤ c) :
    b < a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c

@[to_additive]
theorem lt_mul_of_one_le_of_lt [MulRightMono α] {a b c : α} (ha : 1 ≤ a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c

@[to_additive]
theorem lt_mul_of_one_lt_of_lt [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c

@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [MulRightMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_le_mul`. -/
@[to_additive Right.add_nonneg "Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonneg`."]
theorem Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
"Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_pos_of_nonneg`."]
theorem Right.one_lt_mul_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
"Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_nonneg_of_pos`."]
theorem Right.one_lt_mul_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul`. -/
@[to_additive Right.add_pos "Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos`."]
theorem Right.one_lt_mul [MulRightStrictMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul'`. -/
@[to_additive Right.add_pos' "Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos'`."]
theorem Right.one_lt_mul' [MulRightMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt' ha hb

alias mul_le_one' := Left.mul_le_one

alias mul_lt_one_of_le_of_lt := Left.mul_lt_one_of_le_of_lt

alias mul_lt_one_of_lt_of_le := Left.mul_lt_one_of_lt_of_le

alias mul_lt_one := Left.mul_lt_one

alias mul_lt_one' := Left.mul_lt_one'

attribute [to_additive add_nonpos "**Alias** of `Left.add_nonpos`."] mul_le_one'

attribute [to_additive add_neg_of_nonpos_of_neg "**Alias** of `Left.add_neg_of_nonpos_of_neg`."]
  mul_lt_one_of_le_of_lt

attribute [to_additive add_neg_of_neg_of_nonpos "**Alias** of `Left.add_neg_of_neg_of_nonpos`."]
  mul_lt_one_of_lt_of_le

attribute [to_additive "**Alias** of `Left.add_neg`."] mul_lt_one

attribute [to_additive "**Alias** of `Left.add_neg'`."] mul_lt_one'

alias one_le_mul := Left.one_le_mul

alias one_lt_mul_of_le_of_lt' := Left.one_lt_mul_of_le_of_lt

alias one_lt_mul_of_lt_of_le' := Left.one_lt_mul_of_lt_of_le

alias one_lt_mul' := Left.one_lt_mul

alias one_lt_mul'' := Left.one_lt_mul'

attribute [to_additive add_nonneg "**Alias** of `Left.add_nonneg`."] one_le_mul

attribute [to_additive add_pos_of_nonneg_of_pos "**Alias** of `Left.add_pos_of_nonneg_of_pos`."]
  one_lt_mul_of_le_of_lt'

attribute [to_additive add_pos_of_pos_of_nonneg "**Alias** of `Left.add_pos_of_pos_of_nonneg`."]
  one_lt_mul_of_lt_of_le'

attribute [to_additive add_pos "**Alias** of `Left.add_pos`."] one_lt_mul'

attribute [to_additive add_pos' "**Alias** of `Left.add_pos'`."] one_lt_mul''

@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) :
    a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
theorem le_of_mul_le_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) :
    a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h

@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) :
    a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
theorem le_of_le_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) :
    a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) :
    b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
theorem le_of_mul_le_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) :
    b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h

@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) :
    a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
theorem le_of_le_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a ≤ b * c) (hle : b ≤ 1) :
    a ≤ c :=
  h.trans (mul_le_of_le_one_left' hle)

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
theorem mul_eq_one_iff_of_one_le [MulLeftMono α]
    [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 :=
  Iff.intro
    (fun hab : a * b = 1 =>
      have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, rfl⟩; rw [mul_one])

section Left

variable [MulLeftMono α] {a b : α}

@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_gt <| mul_lt_one_of_lt_of_le h hb

@[to_additive]
theorem eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 :=
  ha.eq_of_not_gt fun h => hab.not_gt <| one_lt_mul_of_lt_of_le' h hb

end Left

section Right

variable [MulRightMono α] {a b : α}

@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_gt <| Right.mul_lt_one_of_le_of_lt ha h

@[to_additive]
theorem eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 :=
  hb.eq_of_not_gt fun h => hab.not_gt <| Right.one_lt_mul_of_le_of_lt ha h

end Right

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem exists_square_le [MulLeftStrictMono α] (a : α) : ∃ b : α, b * b ≤ a := by
  by_cases h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_left' h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    push_neg at h
    rwa [mul_one]

end LinearOrder

end MulOneClass

section Semigroup

variable [Semigroup α]

section PartialOrder

variable [PartialOrder α]

/- This is not instance, since we want to have an instance from `LeftCancelSemigroup`s
to the appropriate covariant class. -/
/-- A semigroup with a partial order and satisfying `LeftCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `LeftCancelSemigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `AddLeftCancelSemigroup`
(i.e. `c + a < c + b → a < b`) is a `AddLeftCancelSemigroup`."]
def Contravariant.toLeftCancelSemigroup [MulLeftReflectLE α] :
    LeftCancelSemigroup α :=
  { ‹Semigroup α› with mul_left_cancel := fun _ _ _ => mul_left_cancel'' }

/- This is not instance, since we want to have an instance from `RightCancelSemigroup`s
to the appropriate covariant class. -/
/-- A semigroup with a partial order and satisfying `RightCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `RightCancelSemigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `AddRightCancelSemigroup`
(`a + c < b + c → a < b`) is a `AddRightCancelSemigroup`."]
def Contravariant.toRightCancelSemigroup [MulRightReflectLE α] :
    RightCancelSemigroup α :=
  { ‹Semigroup α› with mul_right_cancel := fun _ _ _ => mul_right_cancel'' }

end PartialOrder

end Semigroup

section Mono

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

@[to_additive const_add]
theorem Monotone.const_mul' [MulLeftMono α] (hf : Monotone f) (a : α) : Monotone fun x ↦ a * f x :=
  mul_left_mono.comp hf

@[to_additive const_add]
theorem MonotoneOn.const_mul' [MulLeftMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := mul_left_mono.comp_monotoneOn hf

@[to_additive const_add]
theorem Antitone.const_mul' [MulLeftMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ a * f x :=
  mul_left_mono.comp_antitone hf

@[to_additive const_add]
theorem AntitoneOn.const_mul' [MulLeftMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := mul_left_mono.comp_antitoneOn hf

@[to_additive add_const]
theorem Monotone.mul_const' [MulRightMono α] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := mul_right_mono.comp hf

@[to_additive add_const]
theorem MonotoneOn.mul_const' [MulRightMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => f x * a) s := mul_right_mono.comp_monotoneOn hf

@[to_additive add_const]
theorem Antitone.mul_const' [MulRightMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ f x * a :=
  mul_right_mono.comp_antitone hf

@[to_additive add_const]
theorem AntitoneOn.mul_const' [MulRightMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => f x * a) s := mul_right_mono.comp_antitoneOn hf

/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem Monotone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem MonotoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem Antitone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem AntitoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)

section Left

variable [MulLeftStrictMono α]

@[to_additive const_add]
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_left' (hf ab) c

@[to_additive const_add]
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_left' (hf ha hb ab) c

@[to_additive const_add]
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_left' (hf ab) c

@[to_additive const_add]
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_left' (hf ha hb ab) c

end Left

section Right

variable [MulRightStrictMono α]

@[to_additive add_const]
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_right' (hf ab) c

@[to_additive add_const]
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_right' (hf ha hb ab) c

@[to_additive add_const]
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_right' (hf ab) c

@[to_additive add_const]
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_right' (hf ha hb ab) c

end Right

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMono.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMonoOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAnti.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAntiOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono "The sum of a monotone function and a strictly monotone function is
strictly monotone."]
theorem Monotone.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : Monotone f)
    (hg : StrictMono g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono "The sum of a monotone function and a strictly monotone function is
strictly monotone."]
theorem MonotoneOn.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti "The sum of an antitone function and a strictly antitone function is
strictly antitone."]
theorem Antitone.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : Antitone f)
    (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti "The sum of an antitone function and a strictly antitone function is
strictly antitone."]
theorem AntitoneOn.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : AntitoneOn f s)
    (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

variable [MulLeftMono α] [MulRightStrictMono α]

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone "The sum of a strictly monotone function and a monotone function is
strictly monotone."]
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone "The sum of a strictly monotone function and a monotone function is
strictly monotone."]
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone "The sum of a strictly antitone function and an antitone function is
strictly antitone."]
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone "The sum of a strictly antitone function and an antitone function is
strictly antitone."]
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

@[to_additive (attr := simp) cmp_add_left]
theorem cmp_mul_left' {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictMono α]
    (a b c : α) :
    cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c

@[to_additive (attr := simp) cmp_add_right]
theorem cmp_mul_right' {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (a b c : α) :
    cmp (a * c) (b * c) = cmp a b :=
  (strictMono_id.mul_const' c).cmp_map_eq a b

end Mono

/-- An element `a : α` is `MulLECancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[MulLeftReflectLE α]` with
`MulLECancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ENNReal`, where we can replace the assumption `AddLECancellable x` by `x ≠ ∞`.
-/
@[to_additive
"An element `a : α` is `AddLECancellable` if `x ↦ a + x` is order-reflecting.
We will make a separate version of many lemmas that require `[MulLeftReflectLE α]` with
`AddLECancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ENNReal`, where we can replace the assumption `AddLECancellable x` by `x ≠ ∞`. "]
def MulLECancellable [Mul α] [LE α] (a : α) : Prop :=
  ∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c

@[to_additive]
theorem Contravariant.MulLECancellable [Mul α] [LE α] [MulLeftReflectLE α]
    {a : α} :
    MulLECancellable a :=
  fun _ _ => le_of_mul_le_mul_left'

@[to_additive (attr := simp)]
theorem mulLECancellable_one [MulOneClass α] [LE α] : MulLECancellable (1 : α) := fun a b => by
  simpa only [one_mul] using id

namespace MulLECancellable

@[to_additive]
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective (a * ·) :=
  fun _ _ h => le_antisymm (ha h.le) (ha h.ge)

@[to_additive]
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff

@[to_additive]
protected theorem injective_left [Mul α] [i : @Std.Commutative α (· * ·)] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) :
    Injective (· * a) := fun b c h => ha.Injective <| by dsimp; rwa [i.comm a, i.comm a]

@[to_additive]
protected theorem inj_left [Mul α] [@Std.Commutative α (· * ·)] [PartialOrder α] {a b c : α}
    (hc : MulLECancellable c) :
    a * c = b * c ↔ a = b :=
  hc.injective_left.eq_iff

variable [LE α]

@[to_additive]
protected theorem mul_le_mul_iff_left [Mul α] [MulLeftMono α] {a b c : α}
    (ha : MulLECancellable a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨fun h => ha h, fun h => mul_le_mul_left' h a⟩

@[to_additive]
protected theorem mul_le_mul_iff_right [Mul α] [i : @Std.Commutative α (· * ·)]
    [MulLeftMono α] {a b c : α} (ha : MulLECancellable a) :
    b * a ≤ c * a ↔ b ≤ c := by rw [i.comm b, i.comm c, ha.mul_le_mul_iff_left]

@[to_additive]
protected theorem le_mul_iff_one_le_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
protected theorem mul_le_iff_le_one_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
protected theorem le_mul_iff_one_le_left [MulOneClass α] [i : @Std.Commutative α (· * ·)]
    [MulLeftMono α] {a b : α} (ha : MulLECancellable a) :
    a ≤ b * a ↔ 1 ≤ b := by rw [i.comm, ha.le_mul_iff_one_le_right]

@[to_additive]
protected theorem mul_le_iff_le_one_left [MulOneClass α] [i : @Std.Commutative α (· * ·)]
    [MulLeftMono α] {a b : α} (ha : MulLECancellable a) :
    b * a ≤ a ↔ b ≤ 1 := by rw [i.comm, ha.mul_le_iff_le_one_right]

@[to_additive] lemma mul [Semigroup α] {a b : α} (ha : MulLECancellable a)
    (hb : MulLECancellable b) : MulLECancellable (a * b) :=
  fun c d hcd ↦ hb <| ha <| by rwa [← mul_assoc, ← mul_assoc]

@[to_additive] lemma of_mul_right [Semigroup α] [MulLeftMono α] {a b : α}
    (h : MulLECancellable (a * b)) : MulLECancellable b :=
  fun c d hcd ↦ h <| by rw [mul_assoc, mul_assoc]; exact mul_le_mul_left' hcd _

@[to_additive] lemma of_mul_left [CommSemigroup α] [MulLeftMono α] {a b : α}
    (h : MulLECancellable (a * b)) : MulLECancellable a := (mul_comm a b ▸ h).of_mul_right

end MulLECancellable

@[to_additive (attr := simp)]
lemma mulLECancellable_mul [LE α] [CommSemigroup α] [MulLeftMono α] {a b : α} :
    MulLECancellable (a * b) ↔ MulLECancellable a ∧ MulLECancellable b :=
  ⟨fun h ↦ ⟨h.of_mul_left, h.of_mul_right⟩, fun h ↦ h.1.mul h.2⟩
