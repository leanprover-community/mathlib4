/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.Defs

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
`Algebra/Char_P/Invertible` and other lemmas in that file.

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
variables {α : Type*} [Monoid α]

def something_that_needs_inverses (x : α) [Invertible x] := sorry

section
local attribute [instance] invertibleOne
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

set_option autoImplicit true


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
  -- 🎉 no goals

theorem invOf_mul_self_assoc [Monoid α] (a b : α) [Invertible a] : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
  -- 🎉 no goals
#align inv_of_mul_self_assoc invOf_mul_self_assoc

@[simp]
theorem mul_invOf_self_assoc' [Monoid α] (a b : α) {_ : Invertible a} : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
  -- 🎉 no goals

theorem mul_invOf_self_assoc [Monoid α] (a b : α) [Invertible a] : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
  -- 🎉 no goals
#align mul_inv_of_self_assoc mul_invOf_self_assoc

@[simp]
theorem mul_invOf_mul_self_cancel' [Monoid α] (a b : α) {_ : Invertible b} : a * ⅟ b * b = a := by
  simp [mul_assoc]
  -- 🎉 no goals

theorem mul_invOf_mul_self_cancel [Monoid α] (a b : α) [Invertible b] : a * ⅟ b * b = a := by
  simp [mul_assoc]
  -- 🎉 no goals
#align mul_inv_of_mul_self_cancel mul_invOf_mul_self_cancel

@[simp]
theorem mul_mul_invOf_self_cancel' [Monoid α] (a b : α) {_ : Invertible b} : a * b * ⅟ b = a := by
  simp [mul_assoc]
  -- 🎉 no goals

theorem mul_mul_invOf_self_cancel [Monoid α] (a b : α) [Invertible b] : a * b * ⅟ b = a := by
  simp [mul_assoc]
  -- 🎉 no goals
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
  -- ⊢ a * ⅟b = 1
  rw [h, mul_invOf_self]
  -- 🎉 no goals
#align invertible_unique invertible_unique

instance Invertible.subsingleton [Monoid α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    -- ⊢ b = c
    exact left_inv_eq_right_inv hba hac⟩
    -- 🎉 no goals
#align invertible.subsingleton Invertible.subsingleton

/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟ r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
                       -- 🎉 no goals
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]
                       -- 🎉 no goals
#align invertible.copy' Invertible.copy'

/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
@[reducible]
def Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl
#align invertible.copy Invertible.copy

/-- If `a` is invertible and `a = b`, then `⅟a = ⅟b`. -/
@[congr]
theorem Invertible.congr [Ring α] (a b : α) [Invertible a] [Invertible b] (h : a = b) :
  ⅟a = ⅟b := by subst h; congr; apply Subsingleton.allEq
                -- ⊢ ⅟a = ⅟a
                         -- ⊢ inst✝¹ = inst✝
                                -- 🎉 no goals

/-- An `Invertible` element is a unit. -/
@[simps]
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟ a
  val_inv := by simp
                -- 🎉 no goals
  inv_val := by simp
                -- 🎉 no goals
#align unit_of_invertible unitOfInvertible
#align coe_unit_of_invertible val_unitOfInvertible
#align coe_inv_unit_of_invertible val_inv_unitOfInvertible

theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩
#align is_unit_of_invertible isUnit_of_invertible

/-- Units are invertible in their associated monoid. -/
def Units.invertible [Monoid α] (u : αˣ) :
    Invertible (u : α) where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv
#align units.invertible Units.invertible

@[simp]
theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟ (u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv
#align inv_of_units invOf_units

theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩
#align is_unit.nonempty_invertible IsUnit.nonempty_invertible

/-- Convert `IsUnit` to `Invertible` using `Classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible
#align is_unit.invertible IsUnit.invertible

@[simp]
theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.rec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩
#align nonempty_invertible_iff_is_unit nonempty_invertible_iff_isUnit

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

/-- `-⅟a` is the inverse of `-a` -/
def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by simp, by simp⟩
            -- 🎉 no goals
                     -- 🎉 no goals
#align invertible_neg invertibleNeg

@[simp]
theorem invOf_neg [Monoid α] [HasDistribNeg α] (a : α) [Invertible a] [Invertible (-a)] :
    ⅟ (-a) = -⅟ a :=
  invOf_eq_right_inv (by simp)
                         -- 🎉 no goals
#align inv_of_neg invOf_neg

@[simp]
theorem one_sub_invOf_two [Ring α] [Invertible (2 : α)] : 1 - (⅟ 2 : α) = ⅟ 2 :=
  (isUnit_of_invertible (2 : α)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, ← one_add_one_eq_two, add_sub_cancel]
    -- 🎉 no goals
#align one_sub_inv_of_two one_sub_invOf_two

@[simp]
theorem invOf_two_add_invOf_two [NonAssocSemiring α] [Invertible (2 : α)] :
    (⅟ 2 : α) + (⅟ 2 : α) = 1 := by rw [← two_mul, mul_invOf_self]
                                    -- 🎉 no goals
#align inv_of_two_add_inv_of_two invOf_two_add_invOf_two

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
                 -- 🎉 no goals
                                        -- 🎉 no goals
#align invertible_mul invertibleMul

@[simp]
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟ (a * b) = ⅟ b * ⅟ a :=
  invOf_eq_right_inv (by simp [← mul_assoc])
                         -- 🎉 no goals
#align inv_of_mul invOf_mul

/-- A copy of `invertibleMul` for dot notation. -/
@[reducible]
def Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _
#align invertible.mul Invertible.mul

theorem mul_right_inj_of_invertible [Monoid α] (c : α) [Invertible c] :
    a * c = b * c ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩
               -- 🎉 no goals

theorem mul_left_inj_of_invertible [Monoid α] (c : α) [Invertible c] :
    c * a = c * b ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩
               -- 🎉 no goals

theorem invOf_mul_eq_iff_eq_mul_left [Monoid α] [Invertible (c : α)] :
    ⅟c * a = b ↔ a = c * b := by
  rw [← mul_left_inj_of_invertible (c := c), mul_invOf_self_assoc]
  -- 🎉 no goals

theorem mul_left_eq_iff_eq_invOf_mul [Monoid α] [Invertible (c : α)] :
    c * a = b ↔ a = ⅟c * b := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), invOf_mul_self_assoc]
  -- 🎉 no goals

theorem mul_invOf_eq_iff_eq_mul_right [Monoid α] [Invertible (c : α)] :
    a * ⅟c = b ↔ a = b * c := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_mul_self_cancel]
  -- 🎉 no goals

theorem mul_right_eq_iff_eq_mul_invOf [Monoid α] [Invertible (c : α)] :
    a * c = b ↔ a = b * ⅟c := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), mul_mul_invOf_self_cancel]
  -- 🎉 no goals

theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟ b) :=
  calc
    a * ⅟ b = ⅟ b * (b * a * ⅟ b) := by simp [mul_assoc]
                                        -- 🎉 no goals
    _ = ⅟ b * (a * b * ⅟ b) := by rw [h.eq]
                                  -- 🎉 no goals
    _ = ⅟ b * a := by simp [mul_assoc]
                      -- 🎉 no goals
#align commute.inv_of_right Commute.invOf_right

theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟ b) a :=
  calc
    ⅟ b * a = ⅟ b * (a * b * ⅟ b) := by simp [mul_assoc]
                                        -- 🎉 no goals
    _ = ⅟ b * (b * a * ⅟ b) := by rw [h.eq]
                                  -- 🎉 no goals
    _ = a * ⅟ b := by simp [mul_assoc]
                      -- 🎉 no goals
#align commute.inv_of_left Commute.invOf_left

theorem commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟ m) :=
  calc
    m * ⅟ m = 1 := mul_invOf_self m
    _ = ⅟ m * m := (invOf_mul_self m).symm
#align commute_inv_of commute_invOf

theorem nonzero_of_invertible [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟ a * a := by simp [ha]
                        -- 🎉 no goals
      _ = 1 := invOf_mul_self a
#align nonzero_of_invertible nonzero_of_invertible

theorem pos_of_invertible_cast [Semiring α] [Nontrivial α] (n : ℕ) [Invertible (n : α)] : 0 < n :=
  Nat.zero_lt_of_ne_zero fun h => nonzero_of_invertible (n : α) (h ▸ Nat.cast_zero)

instance (priority := 100) Invertible.ne_zero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨nonzero_of_invertible a⟩
#align invertible.ne_zero Invertible.ne_zero

section Monoid

variable [Monoid α]

/-- This is the `Invertible` version of `Units.isUnit_units_mul` -/
@[reducible]
def invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b where
  invOf := ⅟ (a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
                       -- 🎉 no goals
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj, ← mul_assoc, ← mul_assoc, mul_invOf_self, mul_one,
      one_mul]
#align invertible_of_invertible_mul invertibleOfInvertibleMul

/-- This is the `Invertible` version of `Units.isUnit_mul_units` -/
@[reducible]
def invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a where
  invOf := b * ⅟ (a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc, invOf_mul_self, mul_one,
      one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]
                       -- 🎉 no goals
#align invertible_of_mul_invertible invertibleOfMulInvertible

/-- `invertibleOfInvertibleMul` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
def Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.mul_left Invertible.mulLeft
#align invertible.mul_left_apply Invertible.mulLeft_apply
#align invertible.mul_left_symm_apply Invertible.mulLeft_symm_apply

/-- `invertibleOfMulInvertible` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
def Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible.mul_right Invertible.mulRight
#align invertible.mul_right_apply Invertible.mulRight_apply
#align invertible.mul_right_symm_apply Invertible.mulRight_symm_apply

end Monoid

section MonoidWithZero

variable [MonoidWithZero α]

/-- A variant of `Ring.inverse_unit`. -/
@[simp]
theorem Ring.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  Ring.inverse_unit (unitOfInvertible _)
#align ring.inverse_invertible Ring.inverse_invertible

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩
#align invertible_of_nonzero invertibleOfNonzero

@[simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))
#align inv_of_eq_inv invOf_eq_inv

@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)
#align inv_mul_cancel_of_invertible inv_mul_cancel_of_invertible

@[simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)
#align mul_inv_cancel_of_invertible mul_inv_cancel_of_invertible

@[simp]
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel a (nonzero_of_invertible b)
#align div_mul_cancel_of_invertible div_mul_cancel_of_invertible

@[simp]
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel a (nonzero_of_invertible b)
#align mul_div_cancel_of_invertible mul_div_cancel_of_invertible

@[simp]
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (nonzero_of_invertible a)
#align div_self_of_invertible div_self_of_invertible

/-- `b / a` is the inverse of `a / b` -/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩
             -- 🎉 no goals
                                        -- 🎉 no goals
#align invertible_div invertibleDiv

-- Porting note: removed `simp` attribute as `simp` can prove it
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟ (a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])
                         -- 🎉 no goals
#align inv_of_div invOf_div

/-- `a` is the inverse of `a⁻¹` -/
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩
         -- 🎉 no goals
                  -- 🎉 no goals
#align invertible_inv invertibleInv

end GroupWithZero

/-- Monoid homs preserve invertibility. -/
def Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
    [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
    Invertible (f r) where
  invOf := f (⅟ r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
                       -- 🎉 no goals
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]
                       -- 🎉 no goals
#align invertible.map Invertible.map

/-- Note that the `Invertible (f r)` argument can be satisfied by using `letI := Invertible.map f r`
before applying this lemma. -/
theorem map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
    [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] [ifr : Invertible (f r)] :
    f (⅟ r) = ⅟ (f r) :=
  have h : ifr = Invertible.map f r := Subsingleton.elim _ _
  by subst h; rfl
     -- ⊢ ↑f ⅟r = ⅟(↑f r)
              -- 🎉 no goals
#align map_inv_of map_invOf

/-- If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))` -/
@[simps! (config := .lemmasOnly)]
def Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
    [MonoidHomClass G S R] (f : R → S) (g : G) (r : R) (h : Function.LeftInverse g f)
    [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm
#align invertible.of_left_inverse Invertible.ofLeftInverse
#align invertible.of_left_inverse_inv_of Invertible.ofLeftInverse_invOf

/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
def invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
    [MonoidHomClass F R S] [MonoidHomClass G S R] (f : F) (g : G) (r : R)
    (h : Function.LeftInverse g f) :
    Invertible (f r) ≃
      Invertible r where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
#align invertible_equiv_of_left_inverse invertibleEquivOfLeftInverse
#align invertible_equiv_of_left_inverse_symm_apply invertibleEquivOfLeftInverse_symm_apply
#align invertible_equiv_of_left_inverse_apply invertibleEquivOfLeftInverse_apply
