/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `PNatPowAssoc`, where `PNat` means only strictly positive
powers are used.

We also produce the following instance:

- `PNatPowAssoc` for semigroups.

## Todo

* `NatPowAssoc` for `MulWithOne` classes.
* It seems unlikely that anyone will want `NatSMulAssoc` and `PNatSmulAssoc` as additive versions of
power-associativity, but it is not hard to write.
* simp tags?

-/

universe u

variable {G M : Type u}

section PNatPowAssoc

variable [Mul M] [Pow M ℕ+]

/-- A mixin for power-associative multiplication in the non-unital setting. -/
class PNatPowAssoc (M : Type u) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : ∀ (k n: ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x

theorem ppow_add [PNatPowAssoc M] (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

theorem ppow_one [PNatPowAssoc M] (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x

theorem ppow_assoc [PNatPowAssoc M] (k m n : ℕ+) (x : M) :
    x ^ k * (x ^ m * x ^ n) = (x ^ k * x ^ m) * x ^ n := by
  simp only [← ppow_add, add_assoc]

theorem ppow_mul [PNatPowAssoc M] (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  refine PNat.recOn n ?_ ?_
  rw [ppow_one, mul_one]
  intro k hk
  rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

end PNatPowAssoc

section ppowRec

variable [Mul G]

/-- A power operation. `ppowRec n a = a*(a*(⋯*a)⋯)` n times. -/
def ppowRec : ℕ+ → G → G :=
  let rec
  /-- Auxiliary function because ℕ-recursion is easier. -/
    loop : ℕ → G → G
    | 0 => fun x ↦ x
    | n + 1 => fun x ↦ x * loop n x
  fun n x => loop (PNat.natPred n) x

theorem ppowRec_loop_zero (x : G) : ppowRec.loop 0 x = x := rfl

theorem ppowRec_loop_succ (x : G) (n : ℕ) : ppowRec.loop (n + 1) x = x * ppowRec.loop n x :=
  rfl

theorem ppowRec_one (x : G) : ppowRec 1 x = x := rfl

theorem ppowRec_succ (x : G) (n: ℕ+) : ppowRec (n+1) x = x * ppowRec n x := by
  unfold ppowRec
  rw [show (PNat.natPred (n + 1) = PNat.natPred n + 1) from (PNat.natPred_add_one n).symm]
  exact rfl

end ppowRec

section Semigroup

variable [Semigroup G]

instance (G: Type u) [Semigroup G] : Pow G ℕ+ :=
  {
    pow := fun x ⟨k, h⟩ => ppowRec ⟨k, h⟩ x
  }

theorem ppow_eq_ppowRec (x : G) (n : ℕ+) : x^n = ppowRec n x := rfl

theorem ppowRec_loop_add (x : G) (k n : ℕ) :
    ppowRec.loop (k + n + 1) x = ppowRec.loop k x * ppowRec.loop n x := by
  induction k with
  | zero =>
    rw [Nat.zero_add, ppowRec_loop_zero, ppowRec_loop_succ]
  | succ n ih =>
    rw [ppowRec_loop_succ, ppowRec_loop_succ, Nat.succ_add, ih, mul_assoc]

theorem semigroup_ppow_add (x : G) (k n : ℕ+) : x^(k+n) = x^k * x^n := by
  simp only [ppow_eq_ppowRec]
  unfold ppowRec
  rw [← ppowRec_loop_add, PNat.natPred_add]

instance (G: Type u) [Semigroup G] : PNatPowAssoc G :=
  {
    ppow_add := by
      intro k n x
      exact semigroup_ppow_add x k n
    ppow_one := by
      exact ppowRec_one
  }

end Semigroup
