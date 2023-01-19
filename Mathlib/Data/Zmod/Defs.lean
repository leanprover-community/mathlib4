/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.zmod.defs
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.NeZero
import Mathbin.Data.Nat.Modeq
import Mathbin.Data.Fintype.Lattice

/-!
# Definition of `zmod n` + basic results.

This file provides the basic details of `zmod n`, including its commutative ring structure.

## Implementation details

This used to be inlined into data/zmod/basic.lean. This file imports `char_p/basic`, which is an
issue; all `char_p` instances create an `algebra (zmod p) R` instance; however, this instance may
not be definitionally equal to other `algebra` instances (for example, `galois_field` also has an
`algebra` instance as it is defined as a `splitting_field`). The way to fix this is to use the
forgetful inheritance pattern, and make `char_p` carry the data of what the `smul` should be (so
for example, the `smul` on the `galois_field` `char_p` instance should be equal to the `smul` from
its `splitting_field` structure); there is only one possible `zmod p` algebra for any `p`, so this
is not an issue mathematically. For this to be possible, however, we need `char_p/basic` to be
able to import some part of `zmod`.

-/


namespace Fin

/-!
## Ring structure on `fin n`

We define a commutative ring structure on `fin n`, but we do not register it as instance.
Afterwords, when we define `zmod n` in terms of `fin n`, we use these definitions
to register the ring structure on `zmod n` as type class instance.
-/


open Nat.ModEq Int

/-- Multiplicative commutative semigroup structure on `fin n`. -/
instance (n : ℕ) : CommSemigroup (Fin n) :=
  {
    Fin.hasMul with
    mul_assoc := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
      Fin.eq_of_veq
        (calc
          a * b % n * c ≡ a * b * c [MOD n] := (Nat.mod_modEq _ _).mul_right _
          _ ≡ a * (b * c) [MOD n] := by rw [mul_assoc]
          _ ≡ a * (b * c % n) [MOD n] := (Nat.mod_modEq _ _).symm.mul_left _
          )
    mul_comm := Fin.mul_comm }

private theorem left_distrib_aux (n : ℕ) : ∀ a b c : Fin n, a * (b + c) = a * b + a * c :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
  Fin.eq_of_veq
    (calc
      a * ((b + c) % n) ≡ a * (b + c) [MOD n] := (Nat.mod_modEq _ _).mul_left _
      _ ≡ a * b + a * c [MOD n] := by rw [mul_add]
      _ ≡ a * b % n + a * c % n [MOD n] := (Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _).symm
      )
#align fin.left_distrib_aux fin.left_distrib_aux

/-- Commutative ring structure on `fin n`. -/
instance (n : ℕ) [NeZero n] : CommRing (Fin n) :=
  { Fin.addMonoidWithOne, Fin.addCommGroup n,
    Fin.commSemigroup n with
    one_mul := Fin.one_mul
    mul_one := Fin.mul_one
    left_distrib := left_distrib_aux n
    right_distrib := fun a b c => by
      rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm] <;> rfl }

end Fin

/-- The integers modulo `n : ℕ`. -/
def Zmod : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)
#align zmod Zmod

instance Zmod.decidableEq : ∀ n : ℕ, DecidableEq (Zmod n)
  | 0 => Int.decidableEq
  | n + 1 => Fin.decidableEq _
#align zmod.decidable_eq Zmod.decidableEq

instance Zmod.hasRepr : ∀ n : ℕ, Repr (Zmod n)
  | 0 => Int.hasRepr
  | n + 1 => Fin.hasRepr _
#align zmod.has_repr Zmod.hasRepr

namespace Zmod

instance fintype : ∀ (n : ℕ) [NeZero n], Fintype (Zmod n)
  | 0, h => (NeZero.ne 0 rfl).elim
  | n + 1, _ => Fin.fintype (n + 1)
#align zmod.fintype Zmod.fintype

instance infinite : Infinite (Zmod 0) :=
  Int.infinite
#align zmod.infinite Zmod.infinite

@[simp]
theorem card (n : ℕ) [Fintype (Zmod n)] : Fintype.card (Zmod n) = n :=
  by
  cases n
  · exact (not_finite (Zmod 0)).elim
  · convert Fintype.card_fin (n + 1)
#align zmod.card Zmod.card

/- We define each field by cases, to ensure that the eta-expanded `zmod.comm_ring` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `comm_ring` such as
field. -/
instance commRing (n : ℕ) : CommRing (Zmod n)
    where
  add := Nat.casesOn n (@Add.add Int _) fun n => @Add.add (Fin n.succ) _
  add_assoc := Nat.casesOn n (@add_assoc Int _) fun n => @add_assoc (Fin n.succ) _
  zero := Nat.casesOn n (0 : Int) fun n => (0 : Fin n.succ)
  zero_add := Nat.casesOn n (@zero_add Int _) fun n => @zero_add (Fin n.succ) _
  add_zero := Nat.casesOn n (@add_zero Int _) fun n => @add_zero (Fin n.succ) _
  neg := Nat.casesOn n (@Neg.neg Int _) fun n => @Neg.neg (Fin n.succ) _
  sub := Nat.casesOn n (@Sub.sub Int _) fun n => @Sub.sub (Fin n.succ) _
  sub_eq_add_neg := Nat.casesOn n (@sub_eq_add_neg Int _) fun n => @sub_eq_add_neg (Fin n.succ) _
  zsmul := Nat.casesOn n (@CommRing.zsmul Int _) fun n => @CommRing.zsmul (Fin n.succ) _
  zsmul_zero' :=
    Nat.casesOn n (@CommRing.zsmul_zero' Int _) fun n => @CommRing.zsmul_zero' (Fin n.succ) _
  zsmul_succ' :=
    Nat.casesOn n (@CommRing.zsmul_succ' Int _) fun n => @CommRing.zsmul_succ' (Fin n.succ) _
  zsmul_neg' :=
    Nat.casesOn n (@CommRing.zsmul_neg' Int _) fun n => @CommRing.zsmul_neg' (Fin n.succ) _
  nsmul := Nat.casesOn n (@CommRing.nsmul Int _) fun n => @CommRing.nsmul (Fin n.succ) _
  nsmul_zero' :=
    Nat.casesOn n (@CommRing.nsmul_zero' Int _) fun n => @CommRing.nsmul_zero' (Fin n.succ) _
  nsmul_succ' :=
    Nat.casesOn n (@CommRing.nsmul_succ' Int _) fun n => @CommRing.nsmul_succ' (Fin n.succ) _
  add_left_neg := by
    cases n
    exacts[@add_left_neg Int _, @add_left_neg (Fin n.succ) _]
  add_comm := Nat.casesOn n (@add_comm Int _) fun n => @add_comm (Fin n.succ) _
  mul := Nat.casesOn n (@Mul.mul Int _) fun n => @Mul.mul (Fin n.succ) _
  mul_assoc := Nat.casesOn n (@mul_assoc Int _) fun n => @mul_assoc (Fin n.succ) _
  one := Nat.casesOn n (1 : Int) fun n => (1 : Fin n.succ)
  one_mul := Nat.casesOn n (@one_mul Int _) fun n => @one_mul (Fin n.succ) _
  mul_one := Nat.casesOn n (@mul_one Int _) fun n => @mul_one (Fin n.succ) _
  natCast := Nat.casesOn n (coe : ℕ → ℤ) fun n => (coe : ℕ → Fin n.succ)
  nat_cast_zero := Nat.casesOn n (@Nat.cast_zero Int _) fun n => @Nat.cast_zero (Fin n.succ) _
  nat_cast_succ := Nat.casesOn n (@Nat.cast_succ Int _) fun n => @Nat.cast_succ (Fin n.succ) _
  intCast := Nat.casesOn n (coe : ℤ → ℤ) fun n => (coe : ℤ → Fin n.succ)
  int_cast_of_nat := Nat.casesOn n (@Int.cast_of_nat Int _) fun n => @Int.cast_of_nat (Fin n.succ) _
  int_cast_neg_succ_of_nat :=
    Nat.casesOn n (@Int.cast_negSucc Int _) fun n => @Int.cast_negSucc (Fin n.succ) _
  left_distrib := Nat.casesOn n (@left_distrib Int _ _ _) fun n => @left_distrib (Fin n.succ) _ _ _
  right_distrib :=
    Nat.casesOn n (@right_distrib Int _ _ _) fun n => @right_distrib (Fin n.succ) _ _ _
  mul_comm := Nat.casesOn n (@mul_comm Int _) fun n => @mul_comm (Fin n.succ) _
#align zmod.comm_ring Zmod.commRing

instance inhabited (n : ℕ) : Inhabited (Zmod n) :=
  ⟨0⟩
#align zmod.inhabited Zmod.inhabited

end Zmod

