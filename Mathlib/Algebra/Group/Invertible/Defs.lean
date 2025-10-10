/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Defs

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

assert_not_exists MonoidWithZero DenselyOrdered

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

/-- The inverse of an `Invertible` element -/
-- This notation has the same precedence as `Inv.inv`.
prefix:max "⅟" => Invertible.invOf

@[simp]
theorem invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟a * a = 1 :=
  Invertible.invOf_mul_self

theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟a * a = 1 := invOf_mul_self' _

@[simp]
theorem mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟a = 1 :=
  Invertible.mul_invOf_self

theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟a = 1 := mul_invOf_self' _

@[simp]
theorem invOf_mul_cancel_left' [Monoid α] (a b : α) {_ : Invertible a} : ⅟a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

theorem invOf_mul_cancel_left [Monoid α] (a b : α) [Invertible a] : ⅟a * (a * b) = b :=
  invOf_mul_cancel_left' _ _

@[simp]
theorem mul_invOf_cancel_left' [Monoid α] (a b : α) {_ : Invertible a} : a * (⅟a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

theorem mul_invOf_cancel_left [Monoid α] (a b : α) [Invertible a] : a * (⅟a * b) = b :=
  mul_invOf_cancel_left' a b

@[simp]
theorem invOf_mul_cancel_right' [Monoid α] (a b : α) {_ : Invertible b} : a * ⅟b * b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b

theorem invOf_mul_cancel_right [Monoid α] (a b : α) [Invertible b] : a * ⅟b * b = a :=
  invOf_mul_cancel_right' _ _

@[simp]
theorem mul_invOf_cancel_right' [Monoid α] (a b : α) {_ : Invertible b} : a * b * ⅟b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b

theorem mul_invOf_cancel_right [Monoid α] (a b : α) [Invertible b] : a * b * ⅟b = a :=
  mul_invOf_cancel_right' _ _

theorem invOf_eq_right_inv [Monoid α] {a b : α} [Invertible a] (hac : a * b = 1) : ⅟a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac

theorem invOf_eq_left_inv [Monoid α] {a b : α} [Invertible a] (hac : b * a = 1) : ⅟a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm

theorem invertible_unique {α : Type u} [Monoid α] (a b : α) [Invertible a] [Invertible b]
    (h : a = b) : ⅟a = ⅟b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]

instance Invertible.subsingleton [Monoid α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩

/-- If `a` is invertible and `a = b`, then `⅟a = ⅟b`. -/
@[congr]
theorem Invertible.congr [Monoid α] (a b : α) [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b :=
  invertible_unique a b h

/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]

/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
abbrev Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl

/-- Each element of a group is invertible. -/
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel a, mul_inv_cancel a⟩

@[simp]
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel a)

/-- `1` is the inverse of itself -/
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩

@[simp]
theorem invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)

theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟(1 : α) = 1 := invOf_one'

/-- `a` is the inverse of `⅟a`. -/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩

@[simp]
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)] : ⅟(⅟a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)

@[simp]
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟a = ⅟b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟b * ⅟a, by simp [← mul_assoc], by simp [← mul_assoc]⟩

@[simp]
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟(a * b) = ⅟b * ⅟a :=
  invOf_eq_right_inv (by simp [← mul_assoc])

/-- A copy of `invertibleMul` for dot notation. -/
abbrev Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _

section
variable [Monoid α] {a b c : α} [Invertible c]

variable (c) in
theorem mul_left_inj_of_invertible : a * c = b * c ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

variable (c) in
theorem mul_right_inj_of_invertible : c * a = c * b ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_cancel_left]

theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), invOf_mul_cancel_left]

theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_left_inj_of_invertible (c := c), invOf_mul_cancel_right]

theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), mul_invOf_cancel_right]

end
