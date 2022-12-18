/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen

! This file was ported from Lean 3 source module algebra.order.absolute_value
! leanprover-community/mathlib commit fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Regular

/-!
# Absolute values

This file defines a bundled type of absolute values `AbsoluteValue R S`.

## Main definitions

 * `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`.
 * `AbsoluteValue.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
 * `AbsoluteValue.to_monoid_with_zero_hom`: absolute values mapping to a
   linear ordered field preserve `0`, `*` and `1`
 * `IsAbsoluteValue`: a type class stating that `f : β → α` satisfies the axioms of an absolute
   value
-/


/-- `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle equality. -/
structure AbsoluteValue (R S : Type _) [Semiring R] [OrderedSemiring S] extends R →ₙ* S where
  /-- The absolute value is nonnegative -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- The absolute value is positive definitive -/
  eq_zero' : ∀ x, toFun x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  add_le' : ∀ x y, toFun (x + y) ≤ toFun x + toFun y
#align absolute_value AbsoluteValue

namespace AbsoluteValue

-- Porting note: Removing nolints.
-- attribute [nolint doc_blame] AbsoluteValue.toMulHom

-- initialize_simps_projections AbsoluteValue (to_mul_hom_to_fun → apply)

section OrderedSemiring

section Semiring

variable {R S : Type _} [Semiring R] [OrderedSemiring S] (abv : AbsoluteValue R S)

instance zeroHomClass : ZeroHomClass (AbsoluteValue R S) R S where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_zero f := (f.eq_zero' _).2 rfl
#align absolute_value.zero_hom_class AbsoluteValue.zeroHomClass

instance mulHomClass : MulHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass with map_mul := fun f => f.map_mul' }
#align absolute_value.mul_hom_class AbsoluteValue.mulHomClass

instance nonnegHomClass : NonNegHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass with map_nonneg := fun f => f.nonneg' }
#align absolute_value.nonneg_hom_class AbsoluteValue.nonnegHomClass

instance subadditiveHomClass : SubAdditiveHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass with map_add_le_add := fun f => f.add_le' }
#align absolute_value.subadditive_hom_class AbsoluteValue.subadditiveHomClass

@[simp]
theorem coe_mk (f : R →ₙ* S) {h₁ h₂ h₃} : (AbsoluteValue.mk f h₁ h₂ h₃ : R → S) = f :=
  rfl
#align absolute_value.coe_mk AbsoluteValue.coe_mk

@[ext]
theorem ext ⦃f g : AbsoluteValue R S⦄ : (∀ x, f x = g x) → f = g :=
  FunLike.ext _ _
#align absolute_value.ext AbsoluteValue.ext

-- Porting note:
-- These helper instances are unhelpful in Lean 4, so omitting:
-- /-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
-- directly. -/
-- instance : CoeFun (AbsoluteValue R S) fun f => R → S :=
--   FunLike.hasCoeToFun

@[simp]
theorem coe_toMulHom : abv.toMulHom = abv :=
  rfl
#align absolute_value.coe_to_mul_hom AbsoluteValue.coe_toMulHom

protected theorem nonneg (x : R) : 0 ≤ abv x :=
  abv.nonneg' x
#align absolute_value.nonneg AbsoluteValue.nonneg

@[simp]
protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 :=
  abv.eq_zero' x
#align absolute_value.eq_zero AbsoluteValue.eq_zero

protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y :=
  abv.add_le' x y
#align absolute_value.add_le AbsoluteValue.add_le

-- Porting note: Removed since `map_mul` proves the theorem
--@[simp]
--protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y := map_mul _ _ _
  --abv.map_mul' x y
#align absolute_value.map_mul map_mul

protected theorem ne_zero_iff {x : R} : abv x ≠ 0 ↔ x ≠ 0 :=
  abv.eq_zero.not
#align absolute_value.ne_zero_iff AbsoluteValue.ne_zero_iff

protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x :=
  lt_of_le_of_ne (abv.nonneg x) (Ne.symm <| mt abv.eq_zero.mp hx)
#align absolute_value.pos AbsoluteValue.pos

@[simp]
protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
  ⟨fun h₁ => mt abv.eq_zero.mpr h₁.ne', abv.pos⟩
#align absolute_value.pos_iff AbsoluteValue.pos_iff

protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 :=
  (abv.pos hx).ne'
#align absolute_value.ne_zero AbsoluteValue.ne_zero

theorem map_one_of_is_regular (h : IsLeftRegular (abv 1)) : abv 1 = 1 :=
  h <| by simp [← map_mul]
#align absolute_value.map_one_of_is_regular AbsoluteValue.map_one_of_is_regular

-- Porting note: Removed since `map_zero` proves the theorem
--@[simp]
--protected theorem map_zero : abv 0 = 0 := map_zero _
  --abv.eq_zero.2 rfl
#align absolute_value.map_zero map_zero

end Semiring

section Ring

variable {R S : Type _} [Ring R] [OrderedSemiring S] (abv : AbsoluteValue R S)

protected theorem sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)
#align absolute_value.sub_le AbsoluteValue.sub_le

@[simp (high)]
theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
  abv.eq_zero.trans sub_eq_zero
#align absolute_value.map_sub_eq_zero_iff AbsoluteValue.map_sub_eq_zero_iff

end Ring

end OrderedSemiring

section OrderedRing

section Semiring

section IsDomain

-- all of these are true for `NoZeroDivisors S`; but it doesn't work smoothly with the
-- `IsDomain`/`CancelMonoidWithZero` API
variable {R S : Type _} [Semiring R] [OrderedRing S] (abv : AbsoluteValue R S)

variable [IsDomain S] [Nontrivial R]

@[simp (high)]
protected theorem map_one : abv 1 = 1 :=
  abv.map_one_of_is_regular (isRegular_of_ne_zero <| abv.ne_zero one_ne_zero).left
#align absolute_value.map_one AbsoluteValue.map_one

instance : MonoidWithZeroHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.mulHomClass with map_zero := fun f => map_zero f, map_one := fun f => f.map_one }

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0` and `1`. -/
def toMonoidWithZeroHom : R →*₀ S :=
  abv
#align absolute_value.to_monoid_with_zero_hom AbsoluteValue.toMonoidWithZeroHom

@[simp]
theorem coe_toMonoidWithZeroHom : ⇑abv.toMonoidWithZeroHom = abv :=
  rfl
#align absolute_value.coe_to_monoid_with_zero_hom AbsoluteValue.coe_toMonoidWithZeroHom

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and `1`. -/
def toMonoidHom : R →* S :=
  abv
#align absolute_value.to_monoid_hom AbsoluteValue.toMonoidHom

@[simp]
theorem coe_toMonoidHom : ⇑abv.toMonoidHom = abv :=
  rfl
#align absolute_value.coe_to_monoid_hom AbsoluteValue.coe_toMonoidHom

-- Porting note: Removed since `map_zero` proves the theorem
--@[simp]
--protected theorem map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n := map_pow _ _ _
  --abv.toMonoidHom.map_pow a n
#align absolute_value.map_pow map_pow

end IsDomain

end Semiring

section Ring

variable {R S : Type _} [Ring R] [OrderedRing S] (abv : AbsoluteValue R S)

protected theorem le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  sub_le_iff_le_add.2 <| by simpa using abv.add_le (a - b) b
#align absolute_value.le_sub AbsoluteValue.le_sub

end Ring

end OrderedRing

section OrderedCommRing

variable {R S : Type _} [Ring R] [OrderedCommRing S] (abv : AbsoluteValue R S)

variable [NoZeroDivisors S]

@[simp]
protected theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases ha : a = 0; · simp [ha]
  refine'
    (mul_self_eq_mul_self_iff.mp (by rw [← map_mul abv, neg_mul_neg, map_mul abv])).resolve_right _
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'
#align absolute_value.map_neg AbsoluteValue.map_neg

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by rw [← neg_sub, abv.map_neg]
#align absolute_value.map_sub AbsoluteValue.map_sub

end OrderedCommRing

section LinearOrderedRing

variable {R S : Type _} [Semiring R] [LinearOrderedRing S] (abv : AbsoluteValue R S)

/-- `AbsoluteValue.abs` is `abs` as a bundled `AbsoluteValue`. -/
--@[simps] -- Porting note: Removed simps lemma
protected def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add
  map_mul' := abs_mul
#align absolute_value.abs AbsoluteValue.abs

instance : Inhabited (AbsoluteValue S S) :=
  ⟨AbsoluteValue.abs⟩

end LinearOrderedRing

section LinearOrderedCommRing

variable {R S : Type _} [Ring R] [LinearOrderedCommRing S] (abv : AbsoluteValue R S)

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw [abv.map_sub]; apply abv.le_sub⟩
#align absolute_value.abs_abv_sub_le_abv_sub AbsoluteValue.abs_abv_sub_le_abv_sub

end LinearOrderedCommRing

end AbsoluteValue

-- Porting note: Removed [] in fields, see
-- leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Infer.20kinds.20are.20unsupported

/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative.
See also the type `AbsoluteValue` which represents a bundled version of absolute values.
-/
class IsAbsoluteValue {S} [OrderedSemiring S] {R} [Semiring R] (f : R → S) : Prop where
  /-- The absolute value is nonnegative -/
  abv_nonneg : ∀ x, 0 ≤ f x
  /-- The absolute value is positive definitive -/
  abv_eq_zero : ∀ {x}, f x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  abv_add : ∀ x y, f (x + y) ≤ f x + f y
  /-- The absolute value is multiplicative -/
  abv_mul : ∀ x y, f (x * y) = f x * f y
#align is_absolute_value IsAbsoluteValue

namespace IsAbsoluteValue

section OrderedSemiring

variable {S : Type _} [OrderedSemiring S]

variable {R : Type _} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

/-- A bundled absolute value is an absolute value. -/
instance _root_.AbsoluteValue.isAbsoluteValue (abv : AbsoluteValue R S) :
    IsAbsoluteValue abv where
  abv_nonneg := abv.nonneg
  abv_eq_zero := abv.eq_zero
  abv_add := abv.add_le
  abv_mul := abv.map_mul
#align absolute_value.is_absolute_value AbsoluteValue.isAbsoluteValue

/-- Convert an unbundled `IsAbsoluteValue` to a bundled `AbsoluteValue`. -/
--@[simps] -- Porting note: Removed simps lemma
def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add
  eq_zero' _ := abv_eq_zero
  nonneg' := abv_nonneg
  map_mul' := abv_mul
#align is_absolute_value.to_absolute_value IsAbsoluteValue.toAbsoluteValue

theorem abv_zero : abv 0 = 0 :=
  map_zero (toAbsoluteValue abv)
#align is_absolute_value.abv_zero IsAbsoluteValue.abv_zero

theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 :=
  (toAbsoluteValue abv).pos_iff
#align is_absolute_value.abv_pos IsAbsoluteValue.abv_pos

end OrderedSemiring

section LinearOrderedRing

variable {S : Type _} [LinearOrderedRing S]

instance abs_isAbsoluteValue : IsAbsoluteValue (abs : S → S) :=
  AbsoluteValue.abs.isAbsoluteValue
#align is_absolute_value.abs_is_absolute_value IsAbsoluteValue.abs_isAbsoluteValue

end LinearOrderedRing

section OrderedRing

variable {S : Type _} [OrderedRing S]

section Semiring

variable {R : Type _} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

variable [IsDomain S]

theorem abv_one [Nontrivial R] : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one
#align is_absolute_value.abv_one IsAbsoluteValue.abv_one

/-- `abv` as a `monoid_with_zero_hom`. -/
def abvHom [Nontrivial R] : R →*₀ S :=
  (toAbsoluteValue abv).toMonoidWithZeroHom
#align is_absolute_value.abv_hom IsAbsoluteValue.abvHom

theorem abv_pow [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv] (a : R) (n : ℕ) :
    abv (a ^ n) = abv a ^ n :=
  map_pow (toAbsoluteValue abv) a n
#align is_absolute_value.abv_pow IsAbsoluteValue.abv_pow

end Semiring

section Ring

variable {R : Type _} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv_add (a - b) (b - c)
#align is_absolute_value.abv_sub_le IsAbsoluteValue.abv_sub_le

theorem sub_abv_le_abv_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  (toAbsoluteValue abv).le_sub a b
#align is_absolute_value.sub_abv_le_abv_sub IsAbsoluteValue.sub_abv_le_abv_sub

end Ring

end OrderedRing

section OrderedCommRing

variable {S : Type _} [OrderedCommRing S]

section Ring

variable {R : Type _} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

variable [NoZeroDivisors S]

theorem abv_neg (a : R) : abv (-a) = abv a :=
  (toAbsoluteValue abv).map_neg a
#align is_absolute_value.abv_neg IsAbsoluteValue.abv_neg

theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) :=
  (toAbsoluteValue abv).map_sub a b
#align is_absolute_value.abv_sub IsAbsoluteValue.abv_sub

end Ring

end OrderedCommRing

section LinearOrderedCommRing

variable {S : Type _} [LinearOrderedCommRing S]

section Ring

variable {R : Type _} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b
#align is_absolute_value.abs_abv_sub_le_abv_sub IsAbsoluteValue.abs_abv_sub_le_abv_sub

end Ring

end LinearOrderedCommRing

section LinearOrderedField

variable {S : Type _} [LinearOrderedSemifield S]

section Semiring

variable {R : Type _} [Semiring R] [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_one' : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one_of_is_regular <|
    (isRegular_of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left
#align is_absolute_value.abv_one' IsAbsoluteValue.abv_one'

/-- An absolute value as a monoid with zero homomorphism, assuming the target is a semifield. -/
def abvHom' : R →*₀ S :=
  ⟨⟨abv, abv_zero abv⟩, abv_one' abv, abv_mul⟩
#align is_absolute_value.abv_hom' IsAbsoluteValue.abvHom'

end Semiring

section DivisionSemiring

variable {R : Type _} [DivisionSemiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  map_inv₀ (abvHom' abv) a
#align is_absolute_value.abv_inv IsAbsoluteValue.abv_inv

theorem abv_div (a b : R) : abv (a / b) = abv a / abv b :=
  map_div₀ (abvHom' abv) a b
#align is_absolute_value.abv_div IsAbsoluteValue.abv_div

end DivisionSemiring

end LinearOrderedField

end IsAbsoluteValue
