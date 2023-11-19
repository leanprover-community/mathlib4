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

/-- A power operation. `ppowRec n a = a*(a*(⋯*a)⋯)` n times. -/
def ppowRec [Mul M] : ℕ+ → M → M :=
  let rec
  /-- An auxiliary function for easy induction on ℕ. -/
    loop : ℕ → M → M
    | 0 => fun x ↦ x
    | n + 1 => fun x ↦ x * loop n x
  fun n x => loop (PNat.natPred n) x

theorem ppowRec_one [Mul M] (x : M) : ppowRec 1 x = x := rfl

theorem ppowRec_succ [Mul M] (x : M) (n: ℕ+) : ppowRec (n+1) x = x * ppowRec n x := by
  unfold ppowRec
  rw [show (PNat.natPred (n + 1) = PNat.natPred n + 1) from (PNat.natPred_add_one n).symm]
  exact rfl

/-- A scalar multiplication. `psmulRec n a = a+(a+(⋯+a)⋯)` n times. -/
def psmulRec [Add M] : ℕ+ → M → M :=
  let rec
    /-- An auxiliary function for easy induction on ℕ. -/
    loop : ℕ → M → M
    | 0 => fun x ↦ x
    | n + 1 => fun x ↦ x + loop n x
  fun n x => loop (PNat.natPred n) x

/-!
def psmulRec [Add M] : ℕ+ → M → M
  | 1 => fun x ↦ x
  | ⟨k+2, h⟩ => fun x ↦ x + psmulRec ⟨k + 1, (Nat.succ_pos k)⟩ x
termination_by psmulRec x n => PNat.natPred n
decreasing_by sorry -- what should go here???
-/

theorem psmulRec_one [Add M] (x : M) : psmulRec 1 x = x := rfl

theorem psmulRec_succ [Add M] (x : M) (n: ℕ+) : psmulRec (n+1) x = x + psmulRec n x := by
  unfold psmulRec
  rw [show (PNat.natPred (n + 1) = PNat.natPred n + 1) from (PNat.natPred_add_one n).symm]
  exact rfl

/-- A mixin for power-associative multiplication in the non-unital setting. -/
class PosPowAssoc (M : Type u) [Mul M] : Prop where
  /-- Multiplication is power-associative. -/
  protected mul_ppow : ∀ (k n: ℕ+) (x : M), ppowRec k x * ppowRec n x = ppowRec (k + n) x

/-- A mixin for scalar-associative addition in the non-unital setting. -/
class PosSmulAssoc (M : Type u) [Add M] : Prop where
  /-- Addition is Scalar-associative. -/
  protected add_psmul : ∀ (k n: ℕ+) (x : M), psmulRec k x + psmulRec n x = psmulRec (k + n) x

@[default_instance high] instance PosPowAssoc.Pow {M : Type*} [Mul M] [PosPowAssoc M]: Pow M ℕ+ :=
  ⟨fun x n ↦ ppowRec n x⟩

instance PosSmulAssoc.SMul {M : Type*} [Add M] [PosSmulAssoc M] : SMul ℕ+ M :=
  ⟨fun x n ↦ psmulRec x n⟩

theorem ppowRec_eq_pow [Mul M] [PosPowAssoc M] (n : ℕ+) (x : M) : ppowRec n x = x ^ n := rfl

theorem psmulRec_eq_smul [Add M] [PosSmulAssoc M] (n : ℕ+) (x : M) : psmulRec n x = n • x := rfl

theorem ppow_one [Mul M] [PosPowAssoc M] (x : M) : x ^ (1:ℕ+) = x := by
  rw [← ppowRec_eq_pow]
  exact rfl

theorem psmul_one [Add M] [PosSmulAssoc M] (x : M) : (1:ℕ+) • x = x := by
  rw [← psmulRec_eq_smul]
  exact rfl

theorem mul_ppow [Mul M] [PosPowAssoc M] (k n : ℕ+) (x : M) : x^k * x^n = x^(k+n) :=
  PosPowAssoc.mul_ppow k n x

theorem add_psmul [Add M] [PosSmulAssoc M] (k n : ℕ+) (x : M) : k • x + n • x = (k+n) • x :=
  PosSmulAssoc.add_psmul k n x

theorem ppow_assoc [Mul M] [PosPowAssoc M] (k m n : ℕ+) (x : M) :
    x^k * (x^m * x^n) = (x^k * x^m) * x^n := by
  simp only [mul_ppow, add_assoc]

theorem psmul_assoc [Add M] [PosSmulAssoc M] (k m n : ℕ+) (x : M) :
    k • x + (m • x + n • x) = (k • x + m • x) + n • x := by
  simp only [add_psmul, add_assoc]

end NonUnital

section Unital

/-- A mixin for power-associative multiplication. -/
class PowAssoc (M : Type u) [MulOneClass M] : Prop where
  /-- Multiplication is power-associative. -/
  protected mul_pow : ∀ (k n: ℕ) (x : M), npowRec k x * npowRec n x = npowRec (k + n) x

/-- A mixin for power-associative multiplication. -/
class NsmulAssoc (M : Type u) [AddZeroClass M] : Prop where
  /-- Addition is scalar-associative. -/
  protected add_smul : ∀ (k n: ℕ) (x : M), nsmulRec k x + nsmulRec n x = nsmulRec (k + n) x

@[default_instance high] instance PowAssoc.Pow {M : Type*} [MulOneClass M] [PowAssoc M]: Pow M ℕ :=
  ⟨fun x n ↦ npowRec n x⟩

instance SmulAssoc.SMul {M : Type*} [AddZeroClass M] [NsmulAssoc M] : SMul ℕ M :=
  ⟨fun x n ↦ nsmulRec x n⟩

/-!
theorem npowRec_eq_pow_monoid [Monoid M] (x : M) : ∀(n : ℕ), npowRec n x = x^n
  | 0 => by
    unfold npowRec
    exact (pow_zero x).symm
  | n + 1 => by
    unfold npowRec
    rw [pow_succ, Nat.add_eq, Nat.add_zero, npowRec_eq_pow_monoid x n]

instance Semiring.PowAssoc [Semiring M] : PowAssoc M := by
  refine { mul_pow := ?mul_pow }
  intro k n x
  simp only [npowRec_eq_pow_monoid, pow_add]
-/

theorem npowRec_eq_pow [MulOneClass M] [PowAssoc M] (n : ℕ) (x : M) : npowRec n x = x ^ n := rfl

theorem nsmulRec_eq_smul [AddZeroClass M] [NsmulAssoc M] (n : ℕ) (x : M) :
    nsmulRec n x = n • x := rfl

theorem npow_zero [MulOneClass M] [PowAssoc M] (x : M) : x ^ 0 = 1 := rfl

theorem zero_nsmul' [AddZeroClass M] [NsmulAssoc M] (x : M) : 0 • x = 0 := rfl

theorem npow_one [MulOneClass M] [PowAssoc M] (x : M) : x ^ 1 = x := by
  rw [← @npowRec_eq_pow]
  unfold npowRec
  rw [npowRec_eq_pow, npow_zero, mul_one]

theorem mul_pow' [MulOneClass M] [PowAssoc M] (k n : ℕ) (x : M) : x^k * x^n = x^(k+n) :=
  PowAssoc.mul_pow k n x

theorem npow_succ [MulOneClass M] [PowAssoc M] (x : M) (n : ℕ) : x ^ (n+1) = x^n * x := by
  rw [← mul_pow' n 1, npow_one]

theorem add_nsmul' [AddZeroClass M] [NsmulAssoc M] (k n : ℕ) (x : M) : k • x + n • x = (k+n) • x :=
  NsmulAssoc.add_smul k n x

theorem npow_assoc [MulOneClass M] [PowAssoc M] (k m n : ℕ) (x : M) :
    x^k * (x^m * x^n) = (x^k * x^m) * x^n := by
  simp only [mul_pow', add_assoc]

theorem nsmul_assoc [AddZeroClass M] [NsmulAssoc M] (k m n : ℕ) (x : M) :
    k • x + (m • x + n • x) = (k • x + m • x) + n • x := by
  simp only [add_nsmul', add_assoc]

end Unital
