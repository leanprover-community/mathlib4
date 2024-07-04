/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Defs

#align_import algebra.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"

/-!
# Invertible elements

This file defines a typeclass `Invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `IsUnit`.

For constructions of the invertible element given a characteristic, see
`Algebra/CharP/Invertible` and other lemmas in that file.

## Notation

 * `⅟a` is `Invertible.invOf a`, the inverse of `a`

## Implementation notes

The `Invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `Invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `Invertible a` is not a `Prop` (but it is a `Subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `Invertible a` in the
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `Invertible 1` instance:
```lean
variable {α : Type*} [Monoid α]

def something_that_needs_inverses (x : α) [Invertible x] := sorry

section
attribute [local instance] invertibleOne
def something_one := something_that_needs_inverses 1
end
```

### Typeclass search vs. unification for `simp` lemmas

Note that since typeclass search searches the local context first, an instance argument like
`[Invertible a]` might sometimes be filled by a different term than the one we'd find by
unification (i.e., the one that's used as an implicit argument to `⅟`).

This can cause issues with `simp`. Therefore, some lemmas are duplicated, with the `@[simp]`
versions using unification and the user-facing ones using typeclass search.

Since unification can make backwards rewriting (e.g. `rw [← mylemma]`) impractical, we still want
the instance-argument versions; therefore the user-facing versions retain the instance arguments
and the original lemma name, whereas the `@[simp]`/unification ones acquire a `'` at the end of
their name.

We modify this file according to the above pattern only as needed; therefore, most `@[simp]` lemmas
here are not part of such a duplicate pair. This is not (yet) intended as a permanent solution.

See Zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Invertible.201.20simps/near/320558233]

## Tags

invertible, inverse element, invOf, a half, one half, a third, one third, ½, ⅓

-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

universe u

variable {α : Type u}

/-- `Invertible a` gives a two-sided multiplicative inverse of `a`. -/
class Invertible [Mul α] [One α] (a : α) : Type u where
  /-- The inverse of an `Invertible` element -/
  invOf : α
  /-- `invOf a` is a left inverse of `a` -/
  invOf_mul_self : invOf * a = 1
  /-- `invOf a` is a right inverse of `a` -/
  mul_invOf_self : a * invOf = 1
#align invertible Invertible

/-- The inverse of an `Invertible` element -/
prefix:max
  "⅟" =>-- This notation has the same precedence as `Inv.inv`.
  Invertible.invOf

@[simp]
theorem invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟ a * a = 1 :=
  Invertible.invOf_mul_self

theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟ a * a = 1 :=
  Invertible.invOf_mul_self
#align inv_of_mul_self invOf_mul_self

@[simp]
theorem mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟ a = 1 :=
  Invertible.mul_invOf_self

theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟ a = 1 :=
  Invertible.mul_invOf_self
#align mul_inv_of_self mul_invOf_self

@[simp]
theorem invOf_mul_self_assoc' [Monoid α] (a b : α) {_ : Invertible a} : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]

theorem invOf_mul_self_assoc [Monoid α] (a b : α) [Invertible a] : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
#align inv_of_mul_self_assoc invOf_mul_self_assoc

@[simp]
theorem mul_invOf_self_assoc' [Monoid α] (a b : α) {_ : Invertible a} : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]

theorem mul_invOf_self_assoc [Monoid α] (a b : α) [Invertible a] : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
#align mul_inv_of_self_assoc mul_invOf_self_assoc

@[simp]
theorem mul_invOf_mul_self_cancel' [Monoid α] (a b : α) {_ : Invertible b} : a * ⅟ b * b = a := by
  simp [mul_assoc]

theorem mul_invOf_mul_self_cancel [Monoid α] (a b : α) [Invertible b] : a * ⅟ b * b = a := by
  simp [mul_assoc]
#align mul_inv_of_mul_self_cancel mul_invOf_mul_self_cancel

@[simp]
theorem mul_mul_invOf_self_cancel' [Monoid α] (a b : α) {_ : Invertible b} : a * b * ⅟ b = a := by
  simp [mul_assoc]

theorem mul_mul_invOf_self_cancel [Monoid α] (a b : α) [Invertible b] : a * b * ⅟ b = a := by
  simp [mul_assoc]
#align mul_mul_inv_of_self_cancel mul_mul_invOf_self_cancel

theorem invOf_eq_right_inv [Monoid α] {a b : α} [Invertible a] (hac : a * b = 1) : ⅟ a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac
#align inv_of_eq_right_inv invOf_eq_right_inv

theorem invOf_eq_left_inv [Monoid α] {a b : α} [Invertible a] (hac : b * a = 1) : ⅟ a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm
#align inv_of_eq_left_inv invOf_eq_left_inv

theorem invertible_unique {α : Type u} [Monoid α] (a b : α) [Invertible a] [Invertible b]
    (h : a = b) : ⅟ a = ⅟ b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]
#align invertible_unique invertible_unique

instance Invertible.subsingleton [Monoid α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩
#align invertible.subsingleton Invertible.subsingleton

/-- If `a` is invertible and `a = b`, then `⅟a = ⅟b`. -/
@[congr]
theorem Invertible.congr [Monoid α] (a b : α) [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b := by subst h; congr; apply Subsingleton.allEq

/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟ r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]
#align invertible.copy' Invertible.copy'

/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
abbrev Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl
#align invertible.copy Invertible.copy

/-- Each element of a group is invertible. -/
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩
#align invertible_of_group invertibleOfGroup

@[simp]
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_self a)
#align inv_of_eq_group_inv invOf_eq_group_inv

/-- `1` is the inverse of itself -/
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩
#align invertible_one invertibleOne

@[simp]
theorem invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟ (1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)

theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟ (1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)
#align inv_of_one invOf_one

/-- `a` is the inverse of `⅟a`. -/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟ a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩
#align invertible_inv_of invertibleInvOf

@[simp]
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟ a)] : ⅟ (⅟ a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)
#align inv_of_inv_of invOf_invOf

@[simp]
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟ a = ⅟ b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩
#align inv_of_inj invOf_inj

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟ b * ⅟ a, by simp [← mul_assoc], by simp [← mul_assoc]⟩
#align invertible_mul invertibleMul

@[simp]
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟ (a * b) = ⅟ b * ⅟ a :=
  invOf_eq_right_inv (by simp [← mul_assoc])
#align inv_of_mul invOf_mul

/-- A copy of `invertibleMul` for dot notation. -/
abbrev Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _
#align invertible.mul Invertible.mul

section
variable [Monoid α] {a b c : α} [Invertible c]

variable (c) in
theorem mul_right_inj_of_invertible : a * c = b * c ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

variable (c) in
theorem mul_left_inj_of_invertible : c * a = c * b ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_left_inj_of_invertible (c := c), mul_invOf_self_assoc]

theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), invOf_mul_self_assoc]

theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_mul_self_cancel]

theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), mul_mul_invOf_self_cancel]

end
