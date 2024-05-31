/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Algebra.Group.Fin
import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card

#align_import data.zmod.defs from "leanprover-community/mathlib"@"3a2b5524a138b5d0b818b858b516d4ac8a484b03"

/-!
# Definition of `ZMod n` + basic results.

This file provides the basic details of `ZMod n`, including its commutative ring structure.

## Implementation details

This used to be inlined into `Data.ZMod.Basic`. This file imports `CharP.Basic`, which is an
issue; all `CharP` instances create an `Algebra (ZMod p) R` instance; however, this instance may
not be definitionally equal to other `Algebra` instances (for example, `GaloisField` also has an
`Algebra` instance as it is defined as a `SplittingField`). The way to fix this is to use the
forgetful inheritance pattern, and make `CharP` carry the data of what the `smul` should be (so
for example, the `smul` on the `GaloisField` `CharP` instance should be equal to the `smul` from
its `SplittingField` structure); there is only one possible `ZMod p` algebra for any `p`, so this
is not an issue mathematically. For this to be possible, however, we need `CharP.Basic` to be
able to import some part of `ZMod`.

-/


namespace Fin

/-!
## Ring structure on `Fin n`

We define a commutative ring structure on `Fin n`.
Afterwards, when we define `ZMod n` in terms of `Fin n`, we use these definitions
to register the ring structure on `ZMod n` as type class instance.
-/


open Nat.ModEq Int

/-- Multiplicative commutative semigroup structure on `Fin n`. -/
instance instCommSemigroup (n : ℕ) : CommSemigroup (Fin n) :=
  { inferInstanceAs (Mul (Fin n)) with
    mul_assoc := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
      Fin.eq_of_val_eq <|
        calc
          a * b % n * c ≡ a * b * c [MOD n] := (Nat.mod_modEq _ _).mul_right _
          _ ≡ a * (b * c) [MOD n] := by rw [mul_assoc]
          _ ≡ a * (b * c % n) [MOD n] := (Nat.mod_modEq _ _).symm.mul_left _
    mul_comm := Fin.mul_comm }
#align fin.comm_semigroup Fin.instCommSemigroup

private theorem left_distrib_aux (n : ℕ) : ∀ a b c : Fin n, a * (b + c) = a * b + a * c :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
  Fin.eq_of_val_eq <|
    calc
      a * ((b + c) % n) ≡ a * (b + c) [MOD n] := (Nat.mod_modEq _ _).mul_left _
      _ ≡ a * b + a * c [MOD n] := by rw [mul_add]
      _ ≡ a * b % n + a * c % n [MOD n] := (Nat.mod_modEq _ _).symm.add (Nat.mod_modEq _ _).symm

/-- Commutative ring structure on `Fin n`. -/
instance instDistrib (n : ℕ) : Distrib (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instCommSemigroup n with
    left_distrib := left_distrib_aux n
    right_distrib := fun a b c => by
      rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm] }
#align fin.distrib Fin.instDistrib

/-- Commutative ring structure on `Fin n`. -/
instance instCommRing (n : ℕ) [NeZero n] : CommRing (Fin n) :=
  { Fin.instAddMonoidWithOne n, Fin.addCommGroup n, Fin.instCommSemigroup n, Fin.instDistrib n with
    one_mul := Fin.one_mul'
    mul_one := Fin.mul_one',
    -- Porting note: new, see
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/ring.20vs.20Ring/near/322876462
    zero_mul := Fin.zero_mul'
    mul_zero := Fin.mul_zero' }
#align fin.comm_ring Fin.instCommRing

/-- Note this is more general than `Fin.instCommRing` as it applies (vacuously) to `Fin 0` too. -/
instance instHasDistribNeg (n : ℕ) : HasDistribNeg (Fin n) :=
  { toInvolutiveNeg := Fin.instInvolutiveNeg n
    mul_neg := Nat.casesOn n finZeroElim fun _i => mul_neg
    neg_mul := Nat.casesOn n finZeroElim fun _i => neg_mul }
#align fin.has_distrib_neg Fin.instHasDistribNeg

end Fin

/-- The integers modulo `n : ℕ`. -/
def ZMod : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)
#align zmod ZMod

instance ZMod.decidableEq : ∀ n : ℕ, DecidableEq (ZMod n)
  | 0 => inferInstanceAs (DecidableEq ℤ)
  | n + 1 => inferInstanceAs (DecidableEq (Fin (n + 1)))
#align zmod.decidable_eq ZMod.decidableEq

instance ZMod.repr : ∀ n : ℕ, Repr (ZMod n)
  | 0 => by dsimp [ZMod]; infer_instance
  | n + 1 => by dsimp [ZMod]; infer_instance
#align zmod.has_repr ZMod.repr

namespace ZMod

instance instUnique : Unique (ZMod 1) := Fin.uniqueFinOne

instance fintype : ∀ (n : ℕ) [NeZero n], Fintype (ZMod n)
  | 0, h => (h.ne rfl).elim
  | n + 1, _ => Fin.fintype (n + 1)
#align zmod.fintype ZMod.fintype

instance infinite : Infinite (ZMod 0) :=
  Int.infinite
#align zmod.infinite ZMod.infinite

@[simp]
theorem card (n : ℕ) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n := by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert Fintype.card_fin (n + 1) using 2
#align zmod.card ZMod.card

/- We define each field by cases, to ensure that the eta-expanded `ZMod.commRing` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `CommRing` such as
field. -/
instance commRing (n : ℕ) : CommRing (ZMod n) where
  add := Nat.casesOn n (@Add.add Int _) fun n => @Add.add (Fin n.succ) _
  add_assoc := Nat.casesOn n (@add_assoc Int _) fun n => @add_assoc (Fin n.succ) _
  zero := Nat.casesOn n (0 : Int) fun n => (0 : Fin n.succ)
  zero_add := Nat.casesOn n (@zero_add Int _) fun n => @zero_add (Fin n.succ) _
  add_zero := Nat.casesOn n (@add_zero Int _) fun n => @add_zero (Fin n.succ) _
  neg := Nat.casesOn n (@Neg.neg Int _) fun n => @Neg.neg (Fin n.succ) _
  sub := Nat.casesOn n (@Sub.sub Int _) fun n => @Sub.sub (Fin n.succ) _
  sub_eq_add_neg := Nat.casesOn n (@sub_eq_add_neg Int _) fun n => @sub_eq_add_neg (Fin n.succ) _
  zsmul := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).zsmul fun n => (inferInstanceAs (CommRing (Fin n.succ))).zsmul
  zsmul_zero' := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).zsmul_zero'
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).zsmul_zero'
  zsmul_succ' := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).zsmul_succ'
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).zsmul_succ'
  zsmul_neg' := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).zsmul_neg'
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).zsmul_neg'
  nsmul := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).nsmul fun n => (inferInstanceAs (CommRing (Fin n.succ))).nsmul
  nsmul_zero := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).nsmul_zero
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).nsmul_zero
  nsmul_succ := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).nsmul_succ
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).nsmul_succ
  -- Porting note: `match` didn't work here
  add_left_neg := Nat.casesOn n (@add_left_neg Int _) fun n => @add_left_neg (Fin n.succ) _
  add_comm := Nat.casesOn n (@add_comm Int _) fun n => @add_comm (Fin n.succ) _
  mul := Nat.casesOn n (@Mul.mul Int _) fun n => @Mul.mul (Fin n.succ) _
  mul_assoc := Nat.casesOn n (@mul_assoc Int _) fun n => @mul_assoc (Fin n.succ) _
  one := Nat.casesOn n (1 : Int) fun n => (1 : Fin n.succ)
  one_mul := Nat.casesOn n (@one_mul Int _) fun n => @one_mul (Fin n.succ) _
  mul_one := Nat.casesOn n (@mul_one Int _) fun n => @mul_one (Fin n.succ) _
  natCast := Nat.casesOn n ((↑) : ℕ → ℤ) fun n => ((↑) : ℕ → Fin n.succ)
  natCast_zero := Nat.casesOn n (@Nat.cast_zero Int _) fun n => @Nat.cast_zero (Fin n.succ) _
  natCast_succ := Nat.casesOn n (@Nat.cast_succ Int _) fun n => @Nat.cast_succ (Fin n.succ) _
  intCast := Nat.casesOn n ((↑) : ℤ → ℤ) fun n => ((↑) : ℤ → Fin n.succ)
  intCast_ofNat := Nat.casesOn n (@Int.cast_natCast Int _) fun n => @Int.cast_natCast (Fin n.succ) _
  intCast_negSucc :=
    Nat.casesOn n (@Int.cast_negSucc Int _) fun n => @Int.cast_negSucc (Fin n.succ) _
  left_distrib := Nat.casesOn n (@left_distrib Int _ _ _) fun n => @left_distrib (Fin n.succ) _ _ _
  right_distrib :=
    Nat.casesOn n (@right_distrib Int _ _ _) fun n => @right_distrib (Fin n.succ) _ _ _
  mul_comm := Nat.casesOn n (@mul_comm Int _) fun n => @mul_comm (Fin n.succ) _
  -- Porting note: new, see
  -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/ring.20vs.20Ring/near/322876462
  zero_mul := Nat.casesOn n (@zero_mul Int _) fun n => @zero_mul (Fin n.succ) _
  mul_zero := Nat.casesOn n (@mul_zero Int _) fun n => @mul_zero (Fin n.succ) _
  -- Porting note: all npow fields are new, but probably should be backported
  npow := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).npow fun n => (inferInstanceAs (CommRing (Fin n.succ))).npow
  npow_zero := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).npow_zero
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).npow_zero
  npow_succ := Nat.casesOn n
    (inferInstanceAs (CommRing ℤ)).npow_succ
    fun n => (inferInstanceAs (CommRing (Fin n.succ))).npow_succ
#align zmod.comm_ring ZMod.commRing

instance inhabited (n : ℕ) : Inhabited (ZMod n) :=
  ⟨0⟩
#align zmod.inhabited ZMod.inhabited

end ZMod
