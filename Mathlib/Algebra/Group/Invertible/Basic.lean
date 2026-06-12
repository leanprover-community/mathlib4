/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Logic.Equiv.Defs
/-!
# Theorems about invertible elements

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u

variable {α : Type u}

/-- An `Invertible` element is a unit. -/
@[simps]
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟a
  val_inv := by simp
  inv_val := by simp

theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩

/-- Units are invertible in their associated monoid. -/
instance Units.invertible [Monoid α] (u : αˣ) :
    Invertible (u : α) where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv

@[simp]
theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv

theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

/-- Convert `IsUnit` to `Invertible` using `Classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
@[implicit_reducible]
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible

@[simp]
theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.rec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟b) :=
  calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]

theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟b) a :=
  calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]

theorem commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟m) :=
  calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

section Monoid

variable [Monoid α]

/-- This is the `Invertible` version of `Units.isUnit_units_mul` -/
abbrev invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b where
  invOf := ⅟(a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj, ← mul_assoc, ← mul_assoc, mul_invOf_self, mul_one,
      one_mul]

/-- This is the `Invertible` version of `Units.isUnit_mul_units` -/
abbrev invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a where
  invOf := b * ⅟(a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc, invOf_mul_self, mul_one,
      one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]

/-- `invertibleOfInvertibleMul` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
def Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- `invertibleOfMulInvertible` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
def Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

instance invertiblePow (m : α) [Invertible m] (n : ℕ) : Invertible (m ^ n) where
  invOf := ⅟m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]

lemma invOf_pow (m : α) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟(m ^ n) = ⅟m ^ n :=
  @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
@[implicit_reducible]
def invertibleOfPowEqOne (x : α) (n : ℕ) (hx : x ^ n = 1) (hn : n ≠ 0) : Invertible x :=
  inferInstanceAs <| Invertible (Units.ofPowEqOne x n hx hn : α)

end Monoid


/-- Monoid homs preserve invertibility. -/
@[implicit_reducible]
def Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
    Invertible (f r) where
  invOf := f (⅟r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]

/-- Note that the `Invertible (f r)` argument can be satisfied by using `letI := Invertible.map f r`
before applying this lemma. -/
theorem map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R)
    [Invertible r] [ifr : Invertible (f r)] :
    f (⅟r) = ⅟(f r) := by
  obtain rfl : ifr = Invertible.map f r := Subsingleton.elim _ _; rfl

/-- If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))` -/
@[simps! -isSimp, implicit_reducible]
def Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike G S R] [MonoidHomClass G S R] (f : R → S) (g : G) (r : R)
    (h : Function.LeftInverse g f) [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm

/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
def invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] [FunLike G S R] [MonoidHomClass G S R]
    (f : F) (g : G) (r : R) (h : Function.LeftInverse g f) : Invertible (f r) ≃ Invertible r where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
