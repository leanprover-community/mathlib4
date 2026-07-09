/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.PPow.Defs
public import Mathlib.Data.PNat.Basic

/-!
# TODO : Fill in module docstring
-/

public section

variable {M : Type*}

section Semigroup

variable [Semigroup M]

@[to_additive (reorder := n x m) add_psmul]
lemma ppow_add (x : M) (n m : ℕ+) : x ^ (n + m) = x ^ n * x ^ m :=
  m.recOn (by simp [ppow_succ]) fun k hk => by
    rw [← add_assoc, ppow_succ, ppow_succ, hk, mul_assoc]

@[to_additive (reorder := n x m) mul_comm_psmul]
lemma ppow_mul_comm (x : M) (n m : ℕ+) : x ^ n * x ^ m = x ^ m * x ^ n := by
  simp only [← ppow_add, add_comm]

@[to_additive (reorder := n x) rmul_comm_psmul']
lemma ppow_mul_comm' (x : M) (n : ℕ+) : x ^ n * x = x * x ^ n := by
  simpa only [ppow_one] using ppow_mul_comm x n 1

@[to_additive (reorder := n x m) mul_psmul]
lemma ppow_mul (x : M) (n m : ℕ+) : x ^ (n * m) = (x ^ n) ^ m :=
  m.recOn (by simp) fun k hk => by simp [mul_add, ppow_add, hk]

end Semigroup

section CommSemigroup

variable [CommSemigroup M]

/-- `(· ^ (n : ℕ+))` as a `MulHom`. -/
@[to_additive
  /-- `((n : ℕ+) • ·)` as an `AddHom`. -/]
def ppowMulHom (n : ℕ+) : M →ₙ* M where
  toFun x := x ^ n
  map_mul' := mul_ppow (n := n)

-- unclear why `simps` doesn't work, nor `rfl`
@[to_additive (attr := simp)]
lemma ppowMulHom_apply (n : ℕ+) (x : M) : ppowMulHom n x = x ^ n := by
  rw [ppowMulHom]
  rfl

end CommSemigroup

@[to_additive]
theorem pow_mul_comm'' [Monoid M] (a : M) (n : ℕ+) : a ^ n * a = a * a ^ n := by
  exact ppow_mul_comm' a n
