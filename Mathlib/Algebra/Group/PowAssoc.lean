/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with one binary operation. The
classes are named `(Pos)?(Pow|Smul)Assoc`, where `Pos` means that the class is non-unital and `Smul`
means that the class uses additive notation.

We also produce the following instances:

- `Pow M ℕ+`, for nonunital `Mul` classes, and `Pow M ℕ` for unital classes;
- `SMul ℕ+ M` for nonunital `Add` classes, and `SMul ℕ M` for unital classes.

## Todo

* to_additive and simp tags

-/

universe u

variable {M : Type u}

section PNatPowAssoc

variable [Mul M] [Pow M ℕ+]

/-- A `Prop`-valued mixin for power-associative multiplication in the non-unital setting. -/
class PNatPowAssoc (M : Type u) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : ∀ (k n : ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x

theorem ppow_add [PNatPowAssoc M] (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

theorem ppow_one [PNatPowAssoc M] (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x

theorem ppow_assoc [PNatPowAssoc M] (k m n : ℕ+) (x : M) :
    x ^ k * (x ^ m * x ^ n) = (x ^ k * x ^ m) * x ^ n := by
  simp only [← ppow_add, add_assoc]

theorem ppow_comm [PNatPowAssoc M] (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

theorem ppow_mul [PNatPowAssoc M] (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  refine PNat.recOn n ?_ ?_
  rw [ppow_one, mul_one]
  intro k hk
  rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

end PNatPowAssoc

section ppowRec

variable [Mul M]

/-- A strictly positive integer power operation. `ppowRec n a = a*(a*(⋯*a)⋯)` n times. -/
def ppowRec : ℕ+ → M → M :=
  fun n => PNat.recOn n (fun x ↦ x) (fun _ y => fun x => x * y x)

theorem ppowRec_one (x : M) : ppowRec 1 x = x := rfl

theorem ppowRec_succ (x : M) (n : ℕ+) : ppowRec (n + 1) x = x * ppowRec n x := by
  refine PNat.recOn n rfl ?_
  intro k _
  exact rfl

end ppowRec

theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  refine PNat.recOn n ?_ ?_
  rw [ppow_one, PNat.one_coe, pow_one]
  intro k hk
  rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

section NatPowAssoc

variable [MulOneClass M] [Pow M ℕ]

/-- A mixin for power-associative multiplication. -/
class NatPowAssoc (M : Type u) [MulOneClass M] [Pow M ℕ] : Prop where
  /-- Multiplication is power-associative. -/
  protected npow_add : ∀ (k n: ℕ) (x : M), x^(k + n) = x^k * x^n
  /-- Exponent zero is one. -/
  protected npow_zero : ∀ (x : M), x ^ 0 = 1
  /-- Exponent one is identity. -/
  protected npow_one : ∀ (x : M), x ^ 1 = x

theorem npow_add [NatPowAssoc M] (k n : ℕ) (x : M) : x^(k+n) = x^k * x^n  :=
  NatPowAssoc.npow_add k n x

theorem npow_zero [NatPowAssoc M] (x : M) : x ^ 0 = 1 :=
  NatPowAssoc.npow_zero x

theorem npow_one [NatPowAssoc M] (x : M) : x ^ 1 = x :=
  NatPowAssoc.npow_one x

theorem npow_assoc [NatPowAssoc M] (k m n : ℕ) (x : M) :
    x^k * (x^m * x^n) = (x^k * x^m) * x^n := by
  simp only [← npow_add, add_assoc]

end NatPowAssoc

section Monoid

variable [Monoid M]

instance Monoid.PowAssoc [Monoid M] : NatPowAssoc M :=
  {
  npow_add := by
    intro k n x
    rw [pow_add]
  npow_zero := by
    intro x
    rw [pow_zero]
  npow_one := by
    intro x
    rw [pow_one]
  }

end Monoid
