/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Contrapose

#align_import algebra.order.monoid.lemmas from "leanprover-community/mathlib"@"3ba15165bd6927679be7c22d6091a87337e3cd0c"

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

variable {α β : Type*}

section Mul

variable [Mul α]

section LE

variable [LE α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive (attr := gcongr) add_le_add_left]
theorem mul_le_mul_left' [CovariantClass α α (· * ·) (· ≤ ·)] {b c : α} (bc : b ≤ c) (a : α) :
    a * b ≤ a * c :=
  CovariantClass.elim _ bc
#align mul_le_mul_left' mul_le_mul_left'
#align add_le_add_left add_le_add_left

@[to_additive le_of_add_le_add_left]
theorem le_of_mul_le_mul_left' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (bc : a * b ≤ a * c) :
    b ≤ c :=
  ContravariantClass.elim _ bc
#align le_of_mul_le_mul_left' le_of_mul_le_mul_left'
#align le_of_add_le_add_left le_of_add_le_add_left

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive (attr := gcongr) add_le_add_right]
theorem mul_le_mul_right' [i : CovariantClass α α (swap (· * ·)) (· ≤ ·)] {b c : α} (bc : b ≤ c)
    (a : α) :
    b * a ≤ c * a :=
  i.elim a bc
#align mul_le_mul_right' mul_le_mul_right'
#align add_le_add_right add_le_add_right

@[to_additive le_of_add_le_add_right]
theorem le_of_mul_le_mul_right' [i : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (bc : b * a ≤ c * a) :
    b ≤ c :=
  i.elim a bc
#align le_of_mul_le_mul_right' le_of_mul_le_mul_right'
#align le_of_add_le_add_right le_of_add_le_add_right

@[to_additive (attr := simp)]
theorem mul_le_mul_iff_left [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b c : α} :
    a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov α α (· * ·) (· ≤ ·) a
#align mul_le_mul_iff_left mul_le_mul_iff_left
#align add_le_add_iff_left add_le_add_iff_left

@[to_additive (attr := simp)]
theorem mul_le_mul_iff_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b c : α} :
    b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a
#align mul_le_mul_iff_right mul_le_mul_iff_right
#align add_le_add_iff_right add_le_add_iff_right

end LE

section LT

variable [LT α]

@[to_additive (attr := simp)]
theorem mul_lt_mul_iff_left [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] (a : α) {b c : α} :
    a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a
#align mul_lt_mul_iff_left mul_lt_mul_iff_left
#align add_lt_add_iff_left add_lt_add_iff_left

@[to_additive (attr := simp)]
theorem mul_lt_mul_iff_right [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b c : α} :
    b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a
#align mul_lt_mul_iff_right mul_lt_mul_iff_right
#align add_lt_add_iff_right add_lt_add_iff_right

@[to_additive (attr := gcongr) add_lt_add_left]
theorem mul_lt_mul_left' [CovariantClass α α (· * ·) (· < ·)] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c :=
  CovariantClass.elim _ bc
#align mul_lt_mul_left' mul_lt_mul_left'
#align add_lt_add_left add_lt_add_left

@[to_additive lt_of_add_lt_add_left]
theorem lt_of_mul_lt_mul_left' [ContravariantClass α α (· * ·) (· < ·)] {a b c : α}
    (bc : a * b < a * c) :
    b < c :=
  ContravariantClass.elim _ bc
#align lt_of_mul_lt_mul_left' lt_of_mul_lt_mul_left'
#align lt_of_add_lt_add_left lt_of_add_lt_add_left

@[to_additive (attr := gcongr) add_lt_add_right]
theorem mul_lt_mul_right' [i : CovariantClass α α (swap (· * ·)) (· < ·)] {b c : α} (bc : b < c)
    (a : α) :
    b * a < c * a :=
  i.elim a bc
#align mul_lt_mul_right' mul_lt_mul_right'
#align add_lt_add_right add_lt_add_right

@[to_additive lt_of_add_lt_add_right]
theorem lt_of_mul_lt_mul_right' [i : ContravariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}
    (bc : b * a < c * a) :
    b < c :=
  i.elim a bc
#align lt_of_mul_lt_mul_right' lt_of_mul_lt_mul_right'
#align lt_of_add_lt_add_right lt_of_add_lt_add_right

end LT

section Preorder

variable [Preorder α]

@[to_additive (attr := gcongr)]
theorem mul_lt_mul_of_lt_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)]
    {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_left' h₂ a
    _ < b * d := mul_lt_mul_right' h₁ d
#align mul_lt_mul_of_lt_of_lt mul_lt_mul_of_lt_of_lt
#align add_lt_add_of_lt_of_lt add_lt_add_of_lt_of_lt

alias add_lt_add := add_lt_add_of_lt_of_lt
#align add_lt_add add_lt_add

@[to_additive]
theorem mul_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)
#align mul_lt_mul_of_le_of_lt mul_lt_mul_of_le_of_lt
#align add_lt_add_of_le_of_lt add_lt_add_of_le_of_lt

@[to_additive]
theorem mul_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d :=
  (mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)
#align mul_lt_mul_of_lt_of_le mul_lt_mul_of_lt_of_le
#align add_lt_add_of_lt_of_le add_lt_add_of_lt_of_le

/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
theorem Left.mul_lt_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂
#align left.mul_lt_mul Left.mul_lt_mul
#align left.add_lt_add Left.add_lt_add

/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
theorem Right.mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le
#align right.mul_lt_mul Right.mul_lt_mul
#align right.add_lt_add Right.add_lt_add

@[to_additive (attr := gcongr) add_le_add]
theorem mul_le_mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d :=
  (mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)
#align mul_le_mul' mul_le_mul'
#align add_le_add add_le_add

@[to_additive]
theorem mul_le_mul_three [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) :
    a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃
#align mul_le_mul_three mul_le_mul_three
#align add_le_add_three add_le_add_three

@[to_additive]
theorem mul_lt_of_mul_lt_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) :
    a * d < c :=
  (mul_le_mul_left' hle a).trans_lt h
#align mul_lt_of_mul_lt_left mul_lt_of_mul_lt_left
#align add_lt_of_add_lt_left add_lt_of_add_lt_left

@[to_additive]
theorem mul_le_of_mul_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) :
    a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ _ a _ _ _ hle h
#align mul_le_of_mul_le_left mul_le_of_mul_le_left
#align add_le_of_add_le_left add_le_of_add_le_left

@[to_additive]
theorem mul_lt_of_mul_lt_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b < c) (hle : d ≤ a) :
    d * b < c :=
  (mul_le_mul_right' hle b).trans_lt h
#align mul_lt_of_mul_lt_right mul_lt_of_mul_lt_right
#align add_lt_of_add_lt_right add_lt_of_add_lt_right

@[to_additive]
theorem mul_le_of_mul_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) :
    d * b ≤ c :=
  (mul_le_mul_right' hle b).trans h
#align mul_le_of_mul_le_right mul_le_of_mul_le_right
#align add_le_of_add_le_right add_le_of_add_le_right

@[to_additive]
theorem lt_mul_of_lt_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) :
    a < b * d :=
  h.trans_le (mul_le_mul_left' hle b)
#align lt_mul_of_lt_mul_left lt_mul_of_lt_mul_left
#align lt_add_of_lt_add_left lt_add_of_lt_add_left

@[to_additive]
theorem le_mul_of_le_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) :
    a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ _ b _ _ _ hle h
#align le_mul_of_le_mul_left le_mul_of_le_mul_left
#align le_add_of_le_add_left le_add_of_le_add_left

@[to_additive]
theorem lt_mul_of_lt_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) :
    a < d * c :=
  h.trans_le (mul_le_mul_right' hle c)
#align lt_mul_of_lt_mul_right lt_mul_of_lt_mul_right
#align lt_add_of_lt_add_right lt_add_of_lt_add_right

@[to_additive]
theorem le_mul_of_le_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) :
    a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c)
#align le_mul_of_le_mul_right le_mul_of_le_mul_right
#align le_add_of_le_add_right le_add_of_le_add_right

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
theorem mul_left_cancel'' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b = a * c) :
    b = c :=
  (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)
#align mul_left_cancel'' mul_left_cancel''
#align add_left_cancel'' add_left_cancel''

@[to_additive]
theorem mul_right_cancel'' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b = c * b) :
    a = c :=
  (le_of_mul_le_mul_right' h.le).antisymm (le_of_mul_le_mul_right' h.ge)
#align mul_right_cancel'' mul_right_cancel''
#align add_right_cancel'' add_right_cancel''

@[to_additive] lemma mul_le_mul_iff_of_ge [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  haveI := covariantClass_le_of_lt α α (· * ·)
  haveI := covariantClass_le_of_lt α α (swap (· * ·))
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_lt ?_, fun hb ↦ h.not_lt ?_⟩
  exacts [mul_lt_mul_of_lt_of_le ha hb, mul_lt_mul_of_le_of_lt ha hb]
#align add_le_add_iff_of_ge add_le_add_iff_of_geₓ
#align mul_le_mul_iff_of_ge mul_le_mul_iff_of_geₓ

@[to_additive] theorem mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d := by
  haveI := covariantClass_le_of_lt α α (· * ·)
  haveI := covariantClass_le_of_lt α α (swap (· * ·))
  rw [le_antisymm_iff, eq_true (mul_le_mul' hac hbd), true_and, mul_le_mul_iff_of_ge hac hbd]
#align mul_eq_mul_iff_eq_and_eq mul_eq_mul_iff_eq_and_eqₓ
#align add_eq_add_iff_eq_and_eq add_eq_add_iff_eq_and_eqₓ

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b c d : α}

@[to_additive] lemma min_lt_max_of_mul_lt_mul
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    (h : a * b < c * d) : min a b < max c d := by
  simp_rw [min_lt_iff, lt_max_iff]; contrapose! h; exact mul_le_mul' h.1.1 h.2.2
#align min_lt_max_of_mul_lt_mul min_lt_max_of_mul_lt_mulₓ
#align min_lt_max_of_add_lt_add min_lt_max_of_add_lt_addₓ

@[to_additive] lemma Left.min_le_max_of_mul_le_mul
    [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_le_of_lt h.1.1.le h.2.2

@[to_additive] lemma Right.min_le_max_of_mul_le_mul
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_lt_of_le h.1.1 h.2.2.le

@[to_additive] lemma min_le_max_of_mul_le_mul
    [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    (h : a * b ≤ c * d) : min a b ≤ max c d :=
  let _ := covariantClass_le_of_lt α α (swap (· * ·))
  Left.min_le_max_of_mul_le_mul h
#align min_le_max_of_add_le_add min_le_max_of_add_le_add
#align min_le_max_of_mul_le_mul min_le_max_of_mul_le_mul

end LinearOrder

section LinearOrder
variable [LinearOrder α] [CovariantClass α α (· * ·) (· ≤ ·)]
  [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

@[to_additive max_add_add_le_max_add_max]
theorem max_mul_mul_le_max_mul_max' : max (a * b) (c * d) ≤ max a c * max b d :=
  max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _) <|
    mul_le_mul' (le_max_right _ _) <| le_max_right _ _
#align max_mul_mul_le_max_mul_max' max_mul_mul_le_max_mul_max'
#align max_add_add_le_max_add_max max_add_add_le_max_add_max

--TODO: Also missing `min_mul_min_le_min_mul_mul`
@[to_additive min_add_min_le_min_add_add]
theorem min_mul_min_le_min_mul_mul' : min a c * min b d ≤ min (a * b) (c * d) :=
  le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _) <|
    mul_le_mul' (min_le_right _ _) <| min_le_right _ _
#align min_mul_min_le_min_mul_mul' min_mul_min_le_min_mul_mul'
#align min_add_min_le_min_add_add min_add_min_le_min_add_add

end LinearOrder
end Mul

-- using one
section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

@[to_additive le_add_of_nonneg_right]
theorem le_mul_of_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : 1 ≤ b) :
    a ≤ a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_left' h a
#align le_mul_of_one_le_right' le_mul_of_one_le_right'
#align le_add_of_nonneg_right le_add_of_nonneg_right

@[to_additive add_le_of_nonpos_right]
theorem mul_le_of_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : b ≤ 1) :
    a * b ≤ a :=
  calc
    a * b ≤ a * 1 := mul_le_mul_left' h a
    _ = a := mul_one a
#align mul_le_of_le_one_right' mul_le_of_le_one_right'
#align add_le_of_nonpos_right add_le_of_nonpos_right

@[to_additive le_add_of_nonneg_left]
theorem le_mul_of_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : 1 ≤ b) :
    a ≤ b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ ≤ b * a := mul_le_mul_right' h a
#align le_mul_of_one_le_left' le_mul_of_one_le_left'
#align le_add_of_nonneg_left le_add_of_nonneg_left

@[to_additive add_le_of_nonpos_left]
theorem mul_le_of_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : b ≤ 1) :
    b * a ≤ a :=
  calc
    b * a ≤ 1 * a := mul_le_mul_right' h a
    _ = a := one_mul a
#align mul_le_of_le_one_left' mul_le_of_le_one_left'
#align add_le_of_nonpos_left add_le_of_nonpos_left

@[to_additive]
theorem one_le_of_le_mul_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a ≤ a * b) :
    1 ≤ b :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align one_le_of_le_mul_right one_le_of_le_mul_right
#align nonneg_of_le_add_right nonneg_of_le_add_right

@[to_additive]
theorem le_one_of_mul_le_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align le_one_of_mul_le_right le_one_of_mul_le_right
#align nonpos_of_add_le_right nonpos_of_add_le_right

@[to_additive]
theorem one_le_of_le_mul_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : b ≤ a * b) :
    1 ≤ a :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align one_le_of_le_mul_left one_le_of_le_mul_left
#align nonneg_of_le_add_left nonneg_of_le_add_left

@[to_additive]
theorem le_one_of_mul_le_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : a * b ≤ b) :
    a ≤ 1 :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align le_one_of_mul_le_left le_one_of_mul_le_left
#align nonpos_of_add_le_left nonpos_of_add_le_left

@[to_additive (attr := simp) le_add_iff_nonneg_right]
theorem le_mul_iff_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'
#align le_add_iff_nonneg_right le_add_iff_nonneg_right

@[to_additive (attr := simp) le_add_iff_nonneg_left]
theorem le_mul_iff_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b : α} :
    a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)
#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'
#align le_add_iff_nonneg_left le_add_iff_nonneg_left

@[to_additive (attr := simp) add_le_iff_nonpos_right]
theorem mul_le_iff_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'
#align add_le_iff_nonpos_right add_le_iff_nonpos_right

@[to_additive (attr := simp) add_le_iff_nonpos_left]
theorem mul_le_iff_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} :
    a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)
#align mul_le_iff_le_one_left' mul_le_iff_le_one_left'
#align add_le_iff_nonpos_left add_le_iff_nonpos_left

end LE

section LT

variable [LT α]

@[to_additive lt_add_of_pos_right]
theorem lt_mul_of_one_lt_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : 1 < b) :
    a < a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_left' h a
#align lt_mul_of_one_lt_right' lt_mul_of_one_lt_right'
#align lt_add_of_pos_right lt_add_of_pos_right

@[to_additive add_lt_of_neg_right]
theorem mul_lt_of_lt_one_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : b < 1) :
    a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_left' h a
    _ = a := mul_one a
#align mul_lt_of_lt_one_right' mul_lt_of_lt_one_right'
#align add_lt_of_neg_right add_lt_of_neg_right

@[to_additive lt_add_of_pos_left]
theorem lt_mul_of_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α}
    (h : 1 < b) :
    a < b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_right' h a
#align lt_mul_of_one_lt_left' lt_mul_of_one_lt_left'
#align lt_add_of_pos_left lt_add_of_pos_left

@[to_additive add_lt_of_neg_left]
theorem mul_lt_of_lt_one_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α}
    (h : b < 1) :
    b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_right' h a
    _ = a := one_mul a
#align mul_lt_of_lt_one_left' mul_lt_of_lt_one_left'
#align add_lt_of_neg_left add_lt_of_neg_left

@[to_additive]
theorem one_lt_of_lt_mul_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a < a * b) :
    1 < b :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align one_lt_of_lt_mul_right one_lt_of_lt_mul_right
#align pos_of_lt_add_right pos_of_lt_add_right

@[to_additive]
theorem lt_one_of_mul_lt_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a * b < a) :
    b < 1 :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align lt_one_of_mul_lt_right lt_one_of_mul_lt_right
#align neg_of_add_lt_right neg_of_add_lt_right

@[to_additive]
theorem one_lt_of_lt_mul_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : b < a * b) :
    1 < a :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align one_lt_of_lt_mul_left one_lt_of_lt_mul_left
#align pos_of_lt_add_left pos_of_lt_add_left

@[to_additive]
theorem lt_one_of_mul_lt_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : a * b < b) :
    a < 1 :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align lt_one_of_mul_lt_left lt_one_of_mul_lt_left
#align neg_of_add_lt_left neg_of_add_lt_left

@[to_additive (attr := simp) lt_add_iff_pos_right]
theorem lt_mul_iff_one_lt_right' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] (a : α) {b : α} :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'
#align lt_add_iff_pos_right lt_add_iff_pos_right

@[to_additive (attr := simp) lt_add_iff_pos_left]
theorem lt_mul_iff_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)
#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'
#align lt_add_iff_pos_left lt_add_iff_pos_left

@[to_additive (attr := simp) add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] {a b : α} :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'
#align add_lt_iff_neg_left add_lt_iff_neg_left

@[to_additive (attr := simp) add_lt_iff_neg_right]
theorem mul_lt_iff_lt_one_right' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] {a : α} (b : α) : a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)
#align mul_lt_iff_lt_one_right' mul_lt_iff_lt_one_right'
#align add_lt_iff_neg_right add_lt_iff_neg_right

end LT

section Preorder

variable [Preorder α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/


@[to_additive]
theorem mul_le_of_le_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) :
    b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc
#align mul_le_of_le_of_le_one mul_le_of_le_of_le_one
#align add_le_of_le_of_nonpos add_le_of_le_of_nonpos

@[to_additive]
theorem mul_lt_of_le_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc
#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_one
#align add_lt_of_le_of_neg add_lt_of_le_of_neg

@[to_additive]
theorem mul_lt_of_lt_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a ≤ 1) :
    b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc
#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_one
#align add_lt_of_lt_of_nonpos add_lt_of_lt_of_nonpos

@[to_additive]
theorem mul_lt_of_lt_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc
#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_one
#align add_lt_of_lt_of_neg add_lt_of_lt_of_neg

@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le
#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'
#align add_lt_of_lt_of_neg' add_lt_of_lt_of_neg'

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_le_one`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonpos`."]
theorem Left.mul_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb
#align left.mul_le_one Left.mul_le_one
#align left.add_nonpos Left.add_nonpos

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_nonpos_of_neg`."]
theorem Left.mul_lt_one_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a ≤ 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb
#align left.mul_lt_one_of_le_of_lt Left.mul_lt_one_of_le_of_lt
#align left.add_neg_of_nonpos_of_neg Left.add_neg_of_nonpos_of_neg

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_neg_of_nonpos`."]
theorem Left.mul_lt_one_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1)
    (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb
#align left.mul_lt_one_of_lt_of_le Left.mul_lt_one_of_lt_of_le
#align left.add_neg_of_neg_of_nonpos Left.add_neg_of_neg_of_nonpos

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg`."]
theorem Left.mul_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb
#align left.mul_lt_one Left.mul_lt_one
#align left.add_neg Left.add_neg

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one'`. -/
@[to_additive "Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg'`."]
theorem Left.mul_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb
#align left.mul_lt_one' Left.mul_lt_one'
#align left.add_neg' Left.add_neg'

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


@[to_additive]
theorem le_mul_of_le_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : 1 ≤ a) :
    b ≤ c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
#align le_mul_of_le_of_one_le le_mul_of_le_of_one_le
#align le_add_of_le_of_nonneg le_add_of_le_of_nonneg

@[to_additive]
theorem lt_mul_of_le_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c
#align lt_mul_of_le_of_one_lt lt_mul_of_le_of_one_lt
#align lt_add_of_le_of_pos lt_add_of_le_of_pos

@[to_additive]
theorem lt_mul_of_lt_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 ≤ a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
#align lt_mul_of_lt_of_one_le lt_mul_of_lt_of_one_le
#align lt_add_of_lt_of_nonneg lt_add_of_lt_of_nonneg

@[to_additive]
theorem lt_mul_of_lt_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c
#align lt_mul_of_lt_of_one_lt lt_mul_of_lt_of_one_lt
#align lt_add_of_lt_of_pos lt_add_of_lt_of_pos

@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le
#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'
#align lt_add_of_lt_of_pos' lt_add_of_lt_of_pos'

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_le_mul`. -/
@[to_additive Left.add_nonneg "Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonneg`."]
theorem Left.one_le_mul [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb
#align left.one_le_mul Left.one_le_mul
#align left.add_nonneg Left.add_nonneg

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_nonneg_of_pos`."]
theorem Left.one_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 ≤ a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb
#align left.one_lt_mul_of_le_of_lt Left.one_lt_mul_of_le_of_lt
#align left.add_pos_of_nonneg_of_pos Left.add_pos_of_nonneg_of_pos

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      "Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_pos_of_nonneg`."]
theorem Left.one_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a)
    (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb
#align left.one_lt_mul_of_lt_of_le Left.one_lt_mul_of_lt_of_le
#align left.add_pos_of_pos_of_nonneg Left.add_pos_of_pos_of_nonneg

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul`. -/
@[to_additive Left.add_pos "Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos`."]
theorem Left.one_lt_mul [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb
#align left.one_lt_mul Left.one_lt_mul
#align left.add_pos Left.add_pos

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul'`. -/
@[to_additive Left.add_pos' "Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos'`."]
theorem Left.one_lt_mul' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb
#align left.one_lt_mul' Left.one_lt_mul'
#align left.add_pos' Left.add_pos'

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


@[to_additive]
theorem mul_le_of_le_one_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) :
    a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc
#align mul_le_of_le_one_of_le mul_le_of_le_one_of_le
#align add_le_of_nonpos_of_le add_le_of_nonpos_of_le

@[to_additive]
theorem mul_lt_of_lt_one_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hbc : b ≤ c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc
#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_le
#align add_lt_of_neg_of_le add_lt_of_neg_of_le

@[to_additive]
theorem mul_lt_of_le_one_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb
#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_lt
#align add_lt_of_nonpos_of_lt add_lt_of_nonpos_of_lt

@[to_additive]
theorem mul_lt_of_lt_one_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb
#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_lt
#align add_lt_of_neg_of_lt add_lt_of_neg_of_lt

@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a < 1)
    (hbc : b < c) :
    a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc
#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'
#align add_lt_of_neg_of_lt' add_lt_of_neg_of_lt'

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_le_one`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonpos`."]
theorem Right.mul_le_one [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a ≤ 1)
    (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le ha hb
#align right.mul_le_one Right.mul_le_one
#align right.add_nonpos Right.add_nonpos

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      "Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_neg_of_nonpos`."]
theorem Right.mul_lt_one_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb
#align right.mul_lt_one_of_lt_of_le Right.mul_lt_one_of_lt_of_le
#align right.add_neg_of_neg_of_nonpos Right.add_neg_of_neg_of_nonpos

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      "Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_nonpos_of_neg`."]
theorem Right.mul_lt_one_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : a ≤ 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb
#align right.mul_lt_one_of_le_of_lt Right.mul_lt_one_of_le_of_lt
#align right.add_neg_of_nonpos_of_neg Right.add_neg_of_nonpos_of_neg

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg`."]
theorem Right.mul_lt_one [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb
#align right.mul_lt_one Right.mul_lt_one
#align right.add_neg Right.add_neg

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one'`. -/
@[to_additive "Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg'`."]
theorem Right.mul_lt_one' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb
#align right.mul_lt_one' Right.mul_lt_one'
#align right.add_neg' Right.add_neg'

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


@[to_additive]
theorem le_mul_of_one_le_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a)
    (hbc : b ≤ c) :
    b ≤ a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
#align le_mul_of_one_le_of_le le_mul_of_one_le_of_le
#align le_add_of_nonneg_of_le le_add_of_nonneg_of_le

@[to_additive]
theorem lt_mul_of_one_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a)
    (hbc : b ≤ c) :
    b < a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c
#align lt_mul_of_one_lt_of_le lt_mul_of_one_lt_of_le
#align lt_add_of_pos_of_le lt_add_of_pos_of_le

@[to_additive]
theorem lt_mul_of_one_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
#align lt_mul_of_one_le_of_lt lt_mul_of_one_le_of_lt
#align lt_add_of_nonneg_of_lt lt_add_of_nonneg_of_lt

@[to_additive]
theorem lt_mul_of_one_lt_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c
#align lt_mul_of_one_lt_of_lt lt_mul_of_one_lt_of_lt
#align lt_add_of_pos_of_lt lt_add_of_pos_of_lt

@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc
#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'
#align lt_add_of_pos_of_lt' lt_add_of_pos_of_lt'

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_le_mul`. -/
@[to_additive Right.add_nonneg "Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonneg`."]
theorem Right.one_le_mul [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb
#align right.one_le_mul Right.one_le_mul
#align right.add_nonneg Right.add_nonneg

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
"Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_pos_of_nonneg`."]
theorem Right.one_lt_mul_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb
#align right.one_lt_mul_of_lt_of_le Right.one_lt_mul_of_lt_of_le
#align right.add_pos_of_pos_of_nonneg Right.add_pos_of_pos_of_nonneg

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
"Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_nonneg_of_pos`."]
theorem Right.one_lt_mul_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb
#align right.one_lt_mul_of_le_of_lt Right.one_lt_mul_of_le_of_lt
#align right.add_pos_of_nonneg_of_pos Right.add_pos_of_nonneg_of_pos

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul`. -/
@[to_additive Right.add_pos "Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos`."]
theorem Right.one_lt_mul [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb
#align right.one_lt_mul Right.one_lt_mul
#align right.add_pos Right.add_pos

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul'`. -/
@[to_additive Right.add_pos' "Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos'`."]
theorem Right.one_lt_mul' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt' ha hb
#align right.one_lt_mul' Right.one_lt_mul'
#align right.add_pos' Right.add_pos'

alias mul_le_one' := Left.mul_le_one
#align mul_le_one' mul_le_one'

alias mul_lt_one_of_le_of_lt := Left.mul_lt_one_of_le_of_lt
#align mul_lt_one_of_le_of_lt mul_lt_one_of_le_of_lt

alias mul_lt_one_of_lt_of_le := Left.mul_lt_one_of_lt_of_le
#align mul_lt_one_of_lt_of_le mul_lt_one_of_lt_of_le

alias mul_lt_one := Left.mul_lt_one
#align mul_lt_one mul_lt_one

alias mul_lt_one' := Left.mul_lt_one'
#align mul_lt_one' mul_lt_one'

attribute [to_additive add_nonpos "**Alias** of `Left.add_nonpos`."] mul_le_one'
#align add_nonpos add_nonpos

attribute [to_additive add_neg_of_nonpos_of_neg "**Alias** of `Left.add_neg_of_nonpos_of_neg`."]
  mul_lt_one_of_le_of_lt
#align add_neg_of_nonpos_of_neg add_neg_of_nonpos_of_neg

attribute [to_additive add_neg_of_neg_of_nonpos "**Alias** of `Left.add_neg_of_neg_of_nonpos`."]
  mul_lt_one_of_lt_of_le
#align add_neg_of_neg_of_nonpos add_neg_of_neg_of_nonpos

attribute [to_additive "**Alias** of `Left.add_neg`."] mul_lt_one
#align add_neg add_neg

attribute [to_additive "**Alias** of `Left.add_neg'`."] mul_lt_one'
#align add_neg' add_neg'

alias one_le_mul := Left.one_le_mul
#align one_le_mul one_le_mul

alias one_lt_mul_of_le_of_lt' := Left.one_lt_mul_of_le_of_lt
#align one_lt_mul_of_le_of_lt' one_lt_mul_of_le_of_lt'

alias one_lt_mul_of_lt_of_le' := Left.one_lt_mul_of_lt_of_le
#align one_lt_mul_of_lt_of_le' one_lt_mul_of_lt_of_le'

alias one_lt_mul' := Left.one_lt_mul
#align one_lt_mul' one_lt_mul'

alias one_lt_mul'' := Left.one_lt_mul'
#align one_lt_mul'' one_lt_mul''

attribute [to_additive add_nonneg "**Alias** of `Left.add_nonneg`."] one_le_mul
#align add_nonneg add_nonneg

attribute [to_additive add_pos_of_nonneg_of_pos "**Alias** of `Left.add_pos_of_nonneg_of_pos`."]
  one_lt_mul_of_le_of_lt'
#align add_pos_of_nonneg_of_pos add_pos_of_nonneg_of_pos

attribute [to_additive add_pos_of_pos_of_nonneg "**Alias** of `Left.add_pos_of_pos_of_nonneg`."]
  one_lt_mul_of_lt_of_le'
#align add_pos_of_pos_of_nonneg add_pos_of_pos_of_nonneg

attribute [to_additive add_pos "**Alias** of `Left.add_pos`."] one_lt_mul'
#align add_pos add_pos

attribute [to_additive add_pos' "**Alias** of `Left.add_pos'`."] one_lt_mul''
#align add_pos' add_pos'

@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) :
    a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_left
#align lt_of_add_lt_of_nonneg_left lt_of_add_lt_of_nonneg_left

@[to_additive]
theorem le_of_mul_le_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) :
    a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h
#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_left
#align le_of_add_le_of_nonneg_left le_of_add_le_of_nonneg_left

@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) :
    a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)
#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_left
#align lt_of_lt_add_of_nonpos_left lt_of_lt_add_of_nonpos_left

@[to_additive]
theorem le_of_le_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) :
    a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)
#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_left
#align le_of_le_add_of_nonpos_left le_of_le_add_of_nonpos_left

@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) :
    b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_right
#align lt_of_add_lt_of_nonneg_right lt_of_add_lt_of_nonneg_right

@[to_additive]
theorem le_of_mul_le_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) :
    b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h
#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_right
#align le_of_add_le_of_nonneg_right le_of_add_le_of_nonneg_right

@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) :
    a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)
#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_right
#align lt_of_lt_add_of_nonpos_right lt_of_lt_add_of_nonpos_right

@[to_additive]
theorem le_of_le_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a ≤ b * c) (hle : b ≤ 1) :
    a ≤ c :=
  h.trans (mul_le_of_le_one_left' hle)
#align le_of_le_mul_of_le_one_right le_of_le_mul_of_le_one_right
#align le_of_le_add_of_nonpos_right le_of_le_add_of_nonpos_right

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
theorem mul_eq_one_iff' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 :=
  Iff.intro
    (fun hab : a * b = 1 =>
      have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, rfl⟩; rw [mul_one])
    -- Porting note: original proof of the second implication,
    -- `fun ⟨ha', hb'⟩ => by rw [ha', hb', mul_one]`,
    -- had its `to_additive`-ization fail due to some bug
#align mul_eq_one_iff' mul_eq_one_iff'
#align add_eq_zero_iff' add_eq_zero_iff'

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}

@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_lt <| mul_lt_one_of_lt_of_le h hb
#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_left
#align eq_zero_of_add_nonneg_left eq_zero_of_add_nonneg_left

@[to_additive]
theorem eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 :=
  ha.eq_of_not_gt fun h => hab.not_lt <| one_lt_mul_of_lt_of_le' h hb
#align eq_one_of_mul_le_one_left eq_one_of_mul_le_one_left
#align eq_zero_of_add_nonpos_left eq_zero_of_add_nonpos_left

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}

@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_lt <| Right.mul_lt_one_of_le_of_lt ha h
#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_right
#align eq_zero_of_add_nonneg_right eq_zero_of_add_nonneg_right

@[to_additive]
theorem eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 :=
  hb.eq_of_not_gt fun h => hab.not_lt <| Right.one_lt_mul_of_le_of_lt ha h
#align eq_one_of_mul_le_one_right eq_one_of_mul_le_one_right
#align eq_zero_of_add_nonpos_right eq_zero_of_add_nonpos_right

end Right

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem exists_square_le [CovariantClass α α (· * ·) (· < ·)] (a : α) : ∃ b : α, b * b ≤ a := by
  by_cases h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_left' h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    push_neg at h
    rwa [mul_one]
#align exists_square_le exists_square_le

end LinearOrder

end MulOneClass

section Semigroup

variable [Semigroup α]

section PartialOrder

variable [PartialOrder α]

/- This is not instance, since we want to have an instance from `LeftCancelSemigroup`s
to the appropriate `CovariantClass`. -/
/-- A semigroup with a partial order and satisfying `LeftCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel Semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `AddLeftCancelSemigroup`
(i.e. `c + a < c + b → a < b`) is a `left_cancel AddSemigroup`."]
def Contravariant.toLeftCancelSemigroup [ContravariantClass α α (· * ·) (· ≤ ·)] :
    LeftCancelSemigroup α :=
  { ‹Semigroup α› with mul_left_cancel := fun a b c => mul_left_cancel'' }
#align contravariant.to_left_cancel_semigroup Contravariant.toLeftCancelSemigroup
#align contravariant.to_left_cancel_add_semigroup Contravariant.toAddLeftCancelSemigroup

/- This is not instance, since we want to have an instance from `RightCancelSemigroup`s
to the appropriate `CovariantClass`. -/
/-- A semigroup with a partial order and satisfying `RightCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel Semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `AddRightCancelSemigroup`
(`a + c < b + c → a < b`) is a `right_cancel AddSemigroup`."]
def Contravariant.toRightCancelSemigroup [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    RightCancelSemigroup α :=
  { ‹Semigroup α› with mul_right_cancel := fun a b c => mul_right_cancel'' }
#align contravariant.to_right_cancel_semigroup Contravariant.toRightCancelSemigroup
#align contravariant.to_right_cancel_add_semigroup Contravariant.toAddRightCancelSemigroup

#noalign eq_and_eq_of_le_of_le_of_mul_le
#noalign eq_and_eq_of_le_of_le_of_add_le
#noalign left.mul_eq_mul_iff_eq_and_eq
#noalign left.add_eq_add_iff_eq_and_eq
#noalign right.mul_eq_mul_iff_eq_and_eq
#noalign right.add_eq_add_iff_eq_and_eq

end PartialOrder

end Semigroup

section Mono

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun _ _ h => mul_le_mul_left' (hf h) a
#align monotone.const_mul' Monotone.const_mul'
#align monotone.const_add Monotone.const_add

@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun _ hx _ hy h => mul_le_mul_left' (hf hx hy h) a
#align monotone_on.const_mul' MonotoneOn.const_mul'
#align monotone_on.const_add MonotoneOn.const_add

@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun _ _ h => mul_le_mul_left' (hf h) a
#align antitone.const_mul' Antitone.const_mul'
#align antitone.const_add Antitone.const_add

@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun _ hx _ hy h => mul_le_mul_left' (hf hx hy h) a
#align antitone_on.const_mul' AntitoneOn.const_mul'
#align antitone_on.const_add AntitoneOn.const_add

@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun _ _ h => mul_le_mul_right' (hf h) a
#align monotone.mul_const' Monotone.mul_const'
#align monotone.add_const Monotone.add_const

@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s)
    (a : α) :
    MonotoneOn (fun x => f x * a) s := fun _ hx _ hy h => mul_le_mul_right' (hf hx hy h) a
#align monotone_on.mul_const' MonotoneOn.mul_const'
#align monotone_on.add_const MonotoneOn.add_const

@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun _ _ h => mul_le_mul_right' (hf h) a
#align antitone.mul_const' Antitone.mul_const'
#align antitone.add_const Antitone.add_const

@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s)
    (a : α) :
    AntitoneOn (fun x => f x * a) s := fun _ hx _ hy h => mul_le_mul_right' (hf hx hy h) a
#align antitone_on.mul_const' AntitoneOn.mul_const'
#align antitone_on.add_const AntitoneOn.add_const

/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem Monotone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)
#align monotone.mul' Monotone.mul'
#align monotone.add Monotone.add

/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem MonotoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)
#align monotone_on.mul' MonotoneOn.mul'
#align monotone_on.add MonotoneOn.add

/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem Antitone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)
#align antitone.mul' Antitone.mul'
#align antitone.add Antitone.add

/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem AntitoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)
#align antitone_on.mul' AntitoneOn.mul'
#align antitone_on.add AntitoneOn.add

section Left

variable [CovariantClass α α (· * ·) (· < ·)]

@[to_additive const_add]
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_left' (hf ab) c
#align strict_mono.const_mul' StrictMono.const_mul'
#align strict_mono.const_add StrictMono.const_add

@[to_additive const_add]
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_mono_on.const_mul' StrictMonoOn.const_mul'
#align strict_mono_on.const_add StrictMonoOn.const_add

@[to_additive const_add]
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_left' (hf ab) c
#align strict_anti.const_mul' StrictAnti.const_mul'
#align strict_anti.const_add StrictAnti.const_add

@[to_additive const_add]
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_anti_on.const_mul' StrictAntiOn.const_mul'
#align strict_anti_on.const_add StrictAntiOn.const_add

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)]

@[to_additive add_const]
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_right' (hf ab) c
#align strict_mono.mul_const' StrictMono.mul_const'
#align strict_mono.add_const StrictMono.add_const

@[to_additive add_const]
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_mono_on.mul_const' StrictMonoOn.mul_const'
#align strict_mono_on.add_const StrictMonoOn.add_const

@[to_additive add_const]
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_right' (hf ab) c
#align strict_anti.mul_const' StrictAnti.mul_const'
#align strict_anti.add_const StrictAnti.add_const

@[to_additive add_const]
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_anti_on.mul_const' StrictAntiOn.mul_const'
#align strict_anti_on.add_const StrictAntiOn.add_const

end Right

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMono.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_mono.mul' StrictMono.mul'
#align strict_mono.add StrictMono.add

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMonoOn.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)
#align strict_mono_on.mul' StrictMonoOn.mul'
#align strict_mono_on.add StrictMonoOn.add

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAnti.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_anti.mul' StrictAnti.mul'
#align strict_anti.add StrictAnti.add

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAntiOn.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)
#align strict_anti_on.mul' StrictAntiOn.mul'
#align strict_anti_on.add StrictAntiOn.add

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono "The sum of a monotone function and a strictly monotone function is
strictly monotone."]
theorem Monotone.mul_strictMono' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : Monotone f)
    (hg : StrictMono g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
#align monotone.mul_strict_mono' Monotone.mul_strictMono'
#align monotone.add_strict_mono Monotone.add_strictMono

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono "The sum of a monotone function and a strictly monotone function is
strictly monotone."]
theorem MonotoneOn.mul_strictMono' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)
#align monotone_on.mul_strict_mono' MonotoneOn.mul_strictMono'
#align monotone_on.add_strict_mono MonotoneOn.add_strictMono

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti "The sum of an antitone function and a strictly antitone function is
strictly antitone."]
theorem Antitone.mul_strictAnti' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : Antitone f)
    (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
#align antitone.mul_strict_anti' Antitone.mul_strictAnti'
#align antitone.add_strict_anti Antitone.add_strictAnti

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti "The sum of an antitone function and a strictly antitone function is
strictly antitone."]
theorem AntitoneOn.mul_strictAnti' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : AntitoneOn f s)
    (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)
#align antitone_on.mul_strict_anti' AntitoneOn.mul_strictAnti'
#align antitone_on.add_strict_anti AntitoneOn.add_strictAnti

variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone "The sum of a strictly monotone function and a monotone function is
strictly monotone."]
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_mono.mul_monotone' StrictMono.mul_monotone'
#align strict_mono.add_monotone StrictMono.add_monotone

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone "The sum of a strictly monotone function and a monotone function is
strictly monotone."]
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_mono_on.mul_monotone' StrictMonoOn.mul_monotone'
#align strict_mono_on.add_monotone StrictMonoOn.add_monotone

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone "The sum of a strictly antitone function and an antitone function is
strictly antitone."]
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_anti.mul_antitone' StrictAnti.mul_antitone'
#align strict_anti.add_antitone StrictAnti.add_antitone

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone "The sum of a strictly antitone function and an antitone function is
strictly antitone."]
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_anti_on.mul_antitone' StrictAntiOn.mul_antitone'
#align strict_anti_on.add_antitone StrictAntiOn.add_antitone

@[to_additive (attr := simp) cmp_add_left]
theorem cmp_mul_left' {α : Type*} [Mul α] [LinearOrder α] [CovariantClass α α (· * ·) (· < ·)]
    (a b c : α) :
    cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c
#align cmp_mul_left' cmp_mul_left'
#align cmp_add_left cmp_add_left

@[to_additive (attr := simp) cmp_add_right]
theorem cmp_mul_right' {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (a b c : α) :
    cmp (a * c) (b * c) = cmp a b :=
  (strictMono_id.mul_const' c).cmp_map_eq a b
#align cmp_mul_right' cmp_mul_right'
#align cmp_add_right cmp_add_right

end Mono

/-- An element `a : α` is `MulLECancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[ContravariantClass α α (*) (≤)]` with
`MulLECancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ENNReal`, where we can replace the assumption `AddLECancellable x` by `x ≠ ∞`.
-/
@[to_additive
"An element `a : α` is `AddLECancellable` if `x ↦ a + x` is order-reflecting.
We will make a separate version of many lemmas that require `[ContravariantClass α α (+) (≤)]` with
`AddLECancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ENNReal`, where we can replace the assumption `AddLECancellable x` by `x ≠ ∞`. "]
def MulLECancellable [Mul α] [LE α] (a : α) : Prop :=
  ∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c
#align mul_le_cancellable MulLECancellable
#align add_le_cancellable AddLECancellable

@[to_additive]
theorem Contravariant.MulLECancellable [Mul α] [LE α] [ContravariantClass α α (· * ·) (· ≤ ·)]
    {a : α} :
    MulLECancellable a :=
  fun _ _ => le_of_mul_le_mul_left'
#align contravariant.mul_le_cancellable Contravariant.MulLECancellable
#align contravariant.add_le_cancellable Contravariant.AddLECancellable

@[to_additive]
theorem mulLECancellable_one [Monoid α] [LE α] : MulLECancellable (1 : α) := fun a b => by
  simpa only [one_mul] using id
#align mul_le_cancellable_one mulLECancellable_one
#align add_le_cancellable_zero addLECancellable_zero

namespace MulLECancellable

@[to_additive]
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective (a * ·) :=
  fun _ _ h => le_antisymm (ha h.le) (ha h.ge)
#align mul_le_cancellable.injective MulLECancellable.Injective
#align add_le_cancellable.injective AddLECancellable.Injective

@[to_additive]
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff
#align mul_le_cancellable.inj MulLECancellable.inj
#align add_le_cancellable.inj AddLECancellable.inj

@[to_additive]
protected theorem injective_left [Mul α] [i : IsSymmOp α α (· * ·)] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) :
    Injective (· * a) := fun b c h => ha.Injective <| by dsimp; rwa [i.symm_op a, i.symm_op a]
#align mul_le_cancellable.injective_left MulLECancellable.injective_leftₓ
#align add_le_cancellable.injective_left AddLECancellable.injective_leftₓ

@[to_additive]
protected theorem inj_left [Mul α] [IsSymmOp α α (· * ·)] [PartialOrder α] {a b c : α}
    (hc : MulLECancellable c) :
    a * c = b * c ↔ a = b :=
  hc.injective_left.eq_iff
#align mul_le_cancellable.inj_left MulLECancellable.inj_leftₓ
#align add_le_cancellable.inj_left AddLECancellable.inj_leftₓ

variable [LE α]

@[to_additive]
protected theorem mul_le_mul_iff_left [Mul α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (ha : MulLECancellable a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨fun h => ha h, fun h => mul_le_mul_left' h a⟩
#align mul_le_cancellable.mul_le_mul_iff_left MulLECancellable.mul_le_mul_iff_left
#align add_le_cancellable.add_le_add_iff_left AddLECancellable.add_le_add_iff_left

@[to_additive]
protected theorem mul_le_mul_iff_right [Mul α] [i : IsSymmOp α α (· * ·)]
    [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (ha : MulLECancellable a) :
    b * a ≤ c * a ↔ b ≤ c := by rw [i.symm_op b, i.symm_op c, ha.mul_le_mul_iff_left]
#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_rightₓ
#align add_le_cancellable.add_le_add_iff_right AddLECancellable.add_le_add_iff_rightₓ

@[to_additive]
protected theorem le_mul_iff_one_le_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_right
#align add_le_cancellable.le_add_iff_nonneg_right AddLECancellable.le_add_iff_nonneg_right

@[to_additive]
protected theorem mul_le_iff_le_one_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_right
#align add_le_cancellable.add_le_iff_nonpos_right AddLECancellable.add_le_iff_nonpos_right

@[to_additive]
protected theorem le_mul_iff_one_le_left [MulOneClass α] [i : IsSymmOp α α (· * ·)]
    [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : MulLECancellable a) :
    a ≤ b * a ↔ 1 ≤ b := by rw [i.symm_op, ha.le_mul_iff_one_le_right]
#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_leftₓ
#align add_le_cancellable.le_add_iff_nonneg_left AddLECancellable.le_add_iff_nonneg_leftₓ

@[to_additive]
protected theorem mul_le_iff_le_one_left [MulOneClass α] [i : IsSymmOp α α (· * ·)]
    [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : MulLECancellable a) :
    b * a ≤ a ↔ b ≤ 1 := by rw [i.symm_op, ha.mul_le_iff_le_one_right]
#align mul_le_cancellable.mul_le_iff_le_one_left MulLECancellable.mul_le_iff_le_one_leftₓ
#align add_le_cancellable.add_le_iff_nonpos_left AddLECancellable.add_le_iff_nonpos_leftₓ

end MulLECancellable

#noalign bit0_mono
#noalign bit0_strict_mono
