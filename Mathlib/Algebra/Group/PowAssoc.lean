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

section NonUnital

/-- A mixin for power-associative multiplication in the non-unital setting. -/
class PosPowAssoc (M : Type u) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected mul_ppow : ∀ (k n: ℕ+) (x : M), x ^ k * x ^ n = x^(k + n)
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1:ℕ+) = x

/-- A mixin for scalar-associative addition in the non-unital setting. -/
class PosSmulAssoc (M : Type u) [Add M] [SMul ℕ+ M]: Prop where
  /-- Addition is Scalar-associative. -/
  protected add_psmul : ∀ (k n: ℕ+) (x : M), k • x + n • x = (k + n) • x
  /-- Scalar multiplication by one is identity. -/
  protected one_psmul : ∀ (x : M), (1:ℕ+) • x = x

theorem mul_ppow [Mul M] [Pow M ℕ+] [PosPowAssoc M] (k n : ℕ+) (x : M) : x^k * x^n = x^(k+n) :=
  PosPowAssoc.mul_ppow k n x

theorem ppow_one [Mul M] [Pow M ℕ+] [PosPowAssoc M] (x : M) : x ^ (1:ℕ+) = x :=
  PosPowAssoc.ppow_one x

theorem add_psmul [Add M] [SMul ℕ+ M] [PosSmulAssoc M] (k n : ℕ+) (x : M) : k • x + n • x = (k+n) • x :=
  PosSmulAssoc.add_psmul k n x

theorem one_psmul [Add M] [SMul ℕ+ M] [PosSmulAssoc M] (x : M) : (1:ℕ+) • x = x :=
  PosSmulAssoc.one_psmul x

theorem ppow_assoc [Mul M] [Pow M ℕ+] [PosPowAssoc M] (k m n : ℕ+) (x : M) :
    x^k * (x^m * x^n) = (x^k * x^m) * x^n := by
  simp only [mul_ppow, add_assoc]

theorem psmul_assoc [Add M] [SMul ℕ+ M] [PosSmulAssoc M] (k m n : ℕ+) (x : M) :
    k • x + (m • x + n • x) = (k • x + m • x) + n • x := by
  simp only [add_psmul, add_assoc]

end NonUnital

section Unital

/-- A mixin for power-associative multiplication. -/
class PowAssoc (M : Type u) [MulOneClass M] [Pow M ℕ] : Prop where
  /-- Multiplication is power-associative. -/
  protected mul_pow : ∀ (k n: ℕ) (x : M), x^k * x^n = x^(k + n)
  /-- Exponent zero is one. -/
  protected pow_zero : ∀ (x : M), x ^ 0 = 1
  /-- Exponent one is identity. -/
  protected pow_one : ∀ (x : M), x ^ 1 = x

/-- A mixin for power-associative multiplication. -/
class NsmulAssoc (M : Type u) [AddZeroClass M] [SMul ℕ M] : Prop where
  /-- Addition is scalar-associative. -/
  protected add_smul : ∀ (k n: ℕ) (x : M), k • x + n • x = (k + n) • x
  /-- Scalar multiplication by zero is zero. -/
  protected zero_smul : ∀ (x : M), 0 • x = 0
  /-- Exponent one is identity. -/
  protected one_smul : ∀ (x : M), 1 • x = x


instance Monoid.PowAssoc [Monoid M] : PowAssoc M :=
  {
  mul_pow := by
    intro k n x
    rw [pow_add]
  pow_zero := by
    intro x
    rw [pow_zero]
  pow_one := by
    intro x
    rw [pow_one]
  }

instance AddMonoid.NsmulAssoc [AddMonoid M] : NsmulAssoc M :=
  {
  add_smul := by
    intro k n x
    rw [add_nsmul]
  zero_smul := by
    intro x
    rw [zero_smul]
  one_smul := by
    intro x
    rw [one_nsmul]
  }

theorem mul_npow [MulOneClass M] [Pow M ℕ] [PowAssoc M] (k n : ℕ) (x : M) : x^k * x^n = x^(k+n) :=
  PowAssoc.mul_pow k n x

theorem npow_zero [MulOneClass M] [Pow M ℕ] [PowAssoc M] (x : M) : x ^ 0 = 1 :=
  PowAssoc.pow_zero x

theorem npow_one [MulOneClass M] [Pow M ℕ] [PowAssoc M] (x : M) : x ^ 1 = x :=
  PowAssoc.pow_one x

theorem add_nsmul' [AddZeroClass M] [SMul ℕ M] [NsmulAssoc M] (k n : ℕ) (x : M) :
    k • x + n • x = (k+n) • x :=
  NsmulAssoc.add_smul k n x

theorem zero_nsmul' [AddZeroClass M] [SMul ℕ M] [NsmulAssoc M] (x : M) : 0 • x = 0 :=
  NsmulAssoc.zero_smul x

theorem one_nsmul' [AddZeroClass M] [SMul ℕ M] [NsmulAssoc M] (x : M) : 1 • x = x :=
  NsmulAssoc.one_smul x

theorem npow_assoc [MulOneClass M] [Pow M ℕ] [PowAssoc M] (k m n : ℕ) (x : M) :
    x^k * (x^m * x^n) = (x^k * x^m) * x^n := by
  simp only [PowAssoc.mul_pow, add_assoc]

theorem nsmul_assoc [AddZeroClass M] [SMul ℕ M] [NsmulAssoc M] (k m n : ℕ) (x : M) :
    k • x + (m • x + n • x) = (k • x + m • x) + n • x := by
  simp only [NsmulAssoc.add_smul, add_assoc]

end Unital
