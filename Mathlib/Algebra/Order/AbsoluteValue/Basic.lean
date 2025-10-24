/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Positivity.Core

/-!
# Absolute values

This file defines a bundled type of absolute values `AbsoluteValue R S`.

## Main definitions

* `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`.
* `AbsoluteValue.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
* `AbsoluteValue.toMonoidWithZeroHom`: absolute values mapping to a
  linear ordered field preserve `0`, `*` and `1`
* `IsAbsoluteValue`: a type class stating that `f : β → α` satisfies the axioms of an absolute
  value
-/

variable {ι α R S : Type*}

/-- `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy
the triangle inequality. -/
structure AbsoluteValue (R S : Type*) [Semiring R] [Semiring S] [PartialOrder S]
    extends R →ₙ* S where
  /-- The absolute value is nonnegative -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- The absolute value is positive definitive -/
  eq_zero' : ∀ x, toFun x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  add_le' : ∀ x y, toFun (x + y) ≤ toFun x + toFun y

namespace AbsoluteValue

attribute [nolint docBlame] AbsoluteValue.toMulHom

section OrderedSemiring

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

instance funLike : FunLike (AbsoluteValue R S) R S where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance zeroHomClass : ZeroHomClass (AbsoluteValue R S) R S where
  map_zero f := (f.eq_zero' _).2 rfl

instance mulHomClass : MulHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_mul := fun f => f.map_mul' }

instance nonnegHomClass : NonnegHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with apply_nonneg := fun f => f.nonneg' }

instance subadditiveHomClass : SubadditiveHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_add_le_add := fun f => f.add_le' }

@[simp]
theorem coe_mk (f : R →ₙ* S) {h₁ h₂ h₃} : (AbsoluteValue.mk f h₁ h₂ h₃ : R → S) = f :=
  rfl

@[ext]
theorem ext ⦃f g : AbsoluteValue R S⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

/-- See Note [custom simps projection]. -/
def Simps.apply (f : AbsoluteValue R S) : R → S :=
  f

initialize_simps_projections AbsoluteValue (toFun → apply)

@[simp]
theorem coe_toMulHom : ⇑abv.toMulHom = abv :=
  rfl

@[bound]
protected theorem nonneg (x : R) : 0 ≤ abv x :=
  abv.nonneg' x

@[simp]
protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 :=
  abv.eq_zero' x

@[bound]
protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y :=
  abv.add_le' x y

/-- The triangle inequality for an `AbsoluteValue` applied to a list. -/
lemma listSum_le [AddLeftMono S] (l : List R) : abv l.sum ≤ (l.map abv).sum := by
  induction l with
  | nil => simp
  | cons head tail ih => exact (abv.add_le ..).trans <| add_le_add_left ih (abv head)

@[simp]
protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y :=
  abv.map_mul' x y

protected theorem ne_zero_iff {x : R} : abv x ≠ 0 ↔ x ≠ 0 :=
  abv.eq_zero.not
protected alias ⟨_, ne_zero⟩ := AbsoluteValue.ne_zero_iff

@[simp]
protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
  (abv.nonneg x).lt_iff_ne'.trans abv.ne_zero_iff
protected alias ⟨_, pos⟩ := AbsoluteValue.pos_iff

@[simp]
protected theorem nonpos_iff {x : R} : abv x ≤ 0 ↔ x = 0 := by
  simp only [← abv.eq_zero, le_antisymm_iff, abv.nonneg, and_true]

theorem map_one_of_isLeftRegular (h : IsLeftRegular (abv 1)) : abv 1 = 1 :=
  h <| by simp [← abv.map_mul]

@[simp]
protected theorem map_zero : abv 0 = 0 :=
  abv.eq_zero.2 rfl

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

protected theorem sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

@[simp high] -- added `high` to apply it before `AbsoluteValue.eq_zero`
theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
  abv.eq_zero.trans sub_eq_zero

end Ring

section Semiring

section IsDomain

-- all of these are true for `NoZeroDivisors S`; but it doesn't work smoothly with the
-- `IsDomain`/`CancelMonoidWithZero` API
variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)
variable [IsDomain S] [Nontrivial R]

@[simp]
protected theorem map_one : abv 1 = 1 :=
  abv.map_one_of_isLeftRegular (isRegular_of_ne_zero <| abv.ne_zero one_ne_zero).left

instance monoidWithZeroHomClass : MonoidWithZeroHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.mulHomClass with
    map_zero := fun f => f.map_zero
    map_one := fun f => f.map_one }

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0` and `1`. -/
def toMonoidWithZeroHom : R →*₀ S :=
  abv

@[simp]
theorem coe_toMonoidWithZeroHom : ⇑abv.toMonoidWithZeroHom = abv :=
  rfl

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and `1`. -/
def toMonoidHom : R →* S :=
  abv

@[simp]
theorem coe_toMonoidHom : ⇑abv.toMonoidHom = abv :=
  rfl

@[simp]
protected theorem map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  abv.toMonoidHom.map_pow a n

omit [Nontrivial R] in
/-- An absolute value satisfies `f (n : R) ≤ n` for every `n : ℕ`. -/
lemma apply_nat_le_self [IsOrderedRing S] (n : ℕ) : abv n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
  cases subsingleton_or_nontrivial R
  · simp [-Nat.cast_add, Subsingleton.eq_zero (↑(n + 1) : R)]
  · grw [Nat.cast_succ, Nat.cast_succ, abv.add_le, abv.map_one, ih]

end IsDomain

end Semiring

end OrderedSemiring

section OrderedRing

section Ring

variable {R S : Type*} [Ring R] [Ring S] [PartialOrder S] [IsOrderedRing S]
  (abv : AbsoluteValue R S)

@[bound]
protected theorem le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  sub_le_iff_le_add.2 <| by simpa using abv.add_le (a - b) b

end Ring

end OrderedRing

section OrderedCommRing

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

@[simp]
protected theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases ha : a = 0; · simp [ha]
  refine
    (mul_self_eq_mul_self_iff.mp (by rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right ?_
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by rw [← neg_sub, abv.map_neg]

/-- Bound `abv (a + b)` from below -/
@[bound]
protected theorem le_add (a b : R) : abv a - abv b ≤ abv (a + b) := by
  simpa only [tsub_le_iff_right, add_neg_cancel_right, abv.map_neg] using abv.add_le (a + b) (-b)

/-- Bound `abv (a - b)` from above -/
@[bound]
lemma sub_le_add (a b : R) : abv (a - b) ≤ abv a + abv b := by
  simpa only [← sub_eq_add_neg, AbsoluteValue.map_neg] using abv.add_le a (-b)

instance [Nontrivial R] [IsDomain S] : MulRingNormClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.subadditiveHomClass,
    AbsoluteValue.monoidWithZeroHomClass with
    map_neg_eq_map := fun f => f.map_neg
    eq_zero_of_map_eq_zero := fun f _ => f.eq_zero.1 }

open Int in
lemma apply_natAbs_eq (x : ℤ) : abv (natAbs x) = abv x := by
  obtain ⟨_, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

open Int in
/-- Values of an absolute value coincide on the image of `ℕ` in `R`
if and only if they coincide on the image of `ℤ` in `R`. -/
lemma eq_on_nat_iff_eq_on_int {f g : AbsoluteValue R S} :
    (∀ n : ℕ, f n = g n) ↔ ∀ n : ℤ, f n = g n := by
  refine ⟨fun h z ↦ ?_, fun a n ↦ mod_cast a n⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp [h n]

end OrderedCommRing

section LinearOrderedRing

variable {R S : Type*} [Semiring R] [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

/-- `AbsoluteValue.abs` is `abs` as a bundled `AbsoluteValue`. -/
@[simps]
protected def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add_le
  map_mul' := abs_mul

instance : Inhabited (AbsoluteValue S S) :=
  ⟨AbsoluteValue.abs⟩

end LinearOrderedRing

section LinearOrderedCommRing

variable {R S : Type*} [Ring R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

@[bound]
theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw [abv.map_sub]; apply abv.le_sub⟩

end LinearOrderedCommRing

section trivial

variable {R : Type*} [Semiring R] [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [Nontrivial S]

/-- The *trivial* absolute value takes the value `1` on all nonzero elements. -/
protected
def trivial : AbsoluteValue R S where
  toFun x := if x = 0 then 0 else 1
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp [hx, hy]
  nonneg' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  eq_zero' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  add_le' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp only [hx, ↓reduceIte, hy, one_add_one_eq_two]
    rcases eq_or_ne (x + y) 0 with hxy | hxy <;> simp [hxy, one_le_two]

@[simp]
lemma trivial_apply {x : R} (hx : x ≠ 0) : AbsoluteValue.trivial (S := S) x = 1 :=
  if_neg hx

end trivial

section nontrivial

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

/-- An absolute value on a semiring `R` without zero divisors is *nontrivial* if it takes
a value `≠ 1` on a nonzero element.

This has the advantage over `v ≠ .trivial` that it does not require decidability
of `· = 0` in `R`. -/
def IsNontrivial (v : AbsoluteValue R S) : Prop :=
  ∃ x ≠ 0, v x ≠ 1

lemma isNontrivial_iff_ne_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [Nontrivial S] (v : AbsoluteValue R S) :
    v.IsNontrivial ↔ v ≠ .trivial := by
  refine ⟨fun ⟨x, hx₀, hx₁⟩ h ↦ hx₁ <| h.symm ▸ trivial_apply hx₀, fun H ↦ ?_⟩
  simp only [IsNontrivial]
  contrapose! H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

omit [IsOrderedRing S] in
lemma not_isNontrivial_iff (v : AbsoluteValue R S) :
    ¬ v.IsNontrivial ↔ ∀ x ≠ 0, v x = 1 := by
  simp only [IsNontrivial]
  push_neg
  rfl

omit [IsOrderedRing S] in
@[simp]
lemma not_isNontrivial_apply {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x : R} (hx : x ≠ 0) :
    v x = 1 :=
  v.not_isNontrivial_iff.mp hv _ hx

end OrderedSemiring

section LinearOrderedSemifield

variable [Field R] [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] [ExistsAddOfLE S]
  {v : AbsoluteValue R S}

lemma IsNontrivial.exists_abv_gt_one (h : v.IsNontrivial) : ∃ x, 1 < v x := by
  obtain ⟨x, hx₀, hx₁⟩ := h
  rcases hx₁.lt_or_gt with h | h
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ <| v.pos hx₀).mpr h
  · exact ⟨x, h⟩

lemma IsNontrivial.exists_abv_lt_one (h : v.IsNontrivial) : ∃ x ≠ 0, v x < 1 := by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
  have hy₀ := v.ne_zero_iff.mp <| (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

end LinearOrderedSemifield

end nontrivial

end AbsoluteValue

/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative.

See also the type `AbsoluteValue` which represents a bundled version of absolute values.
-/
class IsAbsoluteValue {S} [Semiring S] [PartialOrder S] {R} [Semiring R] (f : R → S) : Prop where
  /-- The absolute value is nonnegative -/
  abv_nonneg' : ∀ x, 0 ≤ f x
  /-- The absolute value is positive definitive -/
  abv_eq_zero' : ∀ {x}, f x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  abv_add' : ∀ x y, f (x + y) ≤ f x + f y
  /-- The absolute value is multiplicative -/
  abv_mul' : ∀ x y, f (x * y) = f x * f y

namespace IsAbsoluteValue

section OrderedSemiring

variable {S : Type*} [Semiring S] [PartialOrder S]
variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

lemma abv_nonneg (x) : 0 ≤ abv x := abv_nonneg' x

open Lean Meta Mathlib Meta Positivity Qq in
/-- The `positivity` extension which identifies expressions of the form `abv a`. -/
@[positivity _]
def Mathlib.Meta.Positivity.evalAbv : PositivityExt where eval {_ _α} _zα _pα e := do
  let (.app f a) ← whnfR e | throwError "not abv ·"
  let pa' ← mkAppM ``abv_nonneg #[f, a]
  pure (.nonnegative pa')

lemma abv_eq_zero {x} : abv x = 0 ↔ x = 0 := abv_eq_zero'

lemma abv_add (x y) : abv (x + y) ≤ abv x + abv y := abv_add' x y

lemma abv_mul (x y) : abv (x * y) = abv x * abv y := abv_mul' x y

/-- A bundled absolute value is an absolute value. -/
instance _root_.AbsoluteValue.isAbsoluteValue (abv : AbsoluteValue R S) : IsAbsoluteValue abv where
  abv_nonneg' := abv.nonneg
  abv_eq_zero' := abv.eq_zero
  abv_add' := abv.add_le
  abv_mul' := abv.map_mul

/-- Convert an unbundled `IsAbsoluteValue` to a bundled `AbsoluteValue`. -/
@[simps]
def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add'
  eq_zero' _ := abv_eq_zero'
  nonneg' := abv_nonneg'
  map_mul' := abv_mul'

theorem abv_zero : abv 0 = 0 :=
  (toAbsoluteValue abv).map_zero

theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 :=
  (toAbsoluteValue abv).pos_iff

end OrderedSemiring

section LinearOrderedRing

variable {S : Type*} [Ring S] [LinearOrder S] [IsStrictOrderedRing S]

instance abs_isAbsoluteValue : IsAbsoluteValue (abs : S → S) :=
  AbsoluteValue.abs.isAbsoluteValue

end LinearOrderedRing

section OrderedRing

variable {S : Type*} [Ring S] [PartialOrder S]

section Semiring

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]
variable [IsDomain S]

theorem abv_one [Nontrivial R] : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one

/-- `abv` as a `MonoidWithZeroHom`. -/
def abvHom [Nontrivial R] : R →*₀ S :=
  (toAbsoluteValue abv).toMonoidWithZeroHom

theorem abv_pow [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv] (a : R) (n : ℕ) :
    abv (a ^ n) = abv a ^ n :=
  (toAbsoluteValue abv).map_pow a n

end Semiring

section Ring

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv_add abv (a - b) (b - c)

theorem sub_abv_le_abv_sub [IsOrderedRing S] (a b : R) : abv a - abv b ≤ abv (a - b) :=
  (toAbsoluteValue abv).le_sub a b

end Ring

end OrderedRing

section OrderedCommRing
variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [NoZeroDivisors S] [Ring R]
  (abv : R → S) [IsAbsoluteValue abv]

theorem abv_neg (a : R) : abv (-a) = abv a :=
  (toAbsoluteValue abv).map_neg a

theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) :=
  (toAbsoluteValue abv).map_sub a b

end OrderedCommRing

section LinearOrderedCommRing

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

section Ring

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b

end Ring

end LinearOrderedCommRing

section IsCancelMulZero

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [IsCancelMulZero S]

section Semiring

variable {R : Type*} [Semiring R] [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv]

omit [IsOrderedRing S] in
theorem abv_one' : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one_of_isLeftRegular <|
    (isRegular_of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left

/-- An absolute value as a monoid with zero homomorphism, assuming the target is a semifield. -/
def abvHom' : R →*₀ S where
  toFun := abv; map_zero' := abv_zero abv; map_one' := abv_one' abv; map_mul' := abv_mul abv

end Semiring

end IsCancelMulZero

section LinearOrderedSemifield

variable {S : Type*} [Semifield S] [LinearOrder S]

section DivisionSemiring

variable {R : Type*} [DivisionSemiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  map_inv₀ (abvHom' abv) a

theorem abv_div (a b : R) : abv (a / b) = abv a / abv b :=
  map_div₀ (abvHom' abv) a b

end DivisionSemiring

end LinearOrderedSemifield

end IsAbsoluteValue
