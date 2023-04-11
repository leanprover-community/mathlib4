/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.num.prime
! leanprover-community/mathlib commit 58581d0fe523063f5651df0619be2bf65012a94a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Num.Lemmas
import Mathbin.Data.Nat.Prime
import Mathbin.Tactic.Ring

/-!
# Primality for binary natural numbers

This file defines versions of `nat.min_fac` and `nat.prime` for `num` and `pos_num`. As with other
`num` definitions, they are not intended for general use (`nat` should be used instead of `num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `dec_trivial`, as well as in `#reduce`.

The default decidable instance for `nat.prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`num` implements algorithms directly on binary natural numbers for this purpose.
-/


namespace PosNum

/-- Auxiliary function for computing the smallest prime factor of a `pos_num`. Unlike
`nat.min_fac_aux`, we use a natural number `fuel` variable that is set to an upper bound on the
number of iterations. It is initialized to the number `n` we are determining primality for. Even
though this is exponential in the input (since it is a `nat`, not a `num`), it will get lazily
evaluated during kernel reduction, so we will only require about `sqrt n` unfoldings, for the
`sqrt n` iterations of the loop. -/
def minFacAux (n : PosNum) : ℕ → PosNum → PosNum
  | 0, _ => n
  | fuel + 1, k =>
    if h : n < k.bit1 * k.bit1 then n else if k.bit1 ∣ n then k.bit1 else min_fac_aux fuel k.succ
#align pos_num.min_fac_aux PosNum.minFacAux

theorem minFacAux_to_nat {fuel : ℕ} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1) :
    (minFacAux n fuel k : ℕ) = Nat.minFacAux n k.bit1 :=
  by
  induction' fuel with fuel ih generalizing k <;> rw [min_fac_aux, Nat.minFacAux]
  · rw [if_pos]
    rwa [zero_add, Nat.sqrt_lt] at h
  rw [← mul_to_nat]; simp only [cast_lt, dvd_to_nat, ite_cast]
  congr 2
  rw [ih] <;> [congr , convert Nat.lt_succ_of_lt h using 1] <;>
    simp only [_root_.bit1, _root_.bit0, cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
      add_left_comm]
#align pos_num.min_fac_aux_to_nat PosNum.minFacAux_to_nat

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac : PosNum → PosNum
  | 1 => 1
  | bit0 n => 2
  | bit1 n => minFacAux (bit1 n) n 1
#align pos_num.min_fac PosNum.minFac

@[simp]
theorem minFac_to_nat (n : PosNum) : (minFac n : ℕ) = Nat.minFac n :=
  by
  cases n; · rfl
  · rw [min_fac, Nat.minFac_eq, if_neg]
    swap
    · simp
    rw [min_fac_aux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    rw [Nat.sqrt_lt]
    convert lt_add_of_pos_right _ (by decide : (0 : ℕ) < (n + 4) * n + 8)
    unfold _root_.bit1 _root_.bit0
    ring
  · rw [min_fac, Nat.minFac_eq, if_pos]
    · rfl
    simp
#align pos_num.min_fac_to_nat PosNum.minFac_to_nat

/-- Primality predicate for a `pos_num`. -/
@[simp]
def Prime (n : PosNum) : Prop :=
  Nat.Prime n
#align pos_num.prime PosNum.Prime

instance decidablePrime : DecidablePred PosNum.Prime
  | 1 => Decidable.isFalse Nat.not_prime_one
  | bit0 n =>
    decidable_of_iff' (n = 1)
      (by
        refine' nat.prime_def_min_fac.trans ((and_iff_right _).trans <| eq_comm.trans _)
        · exact bit0_le_bit0.2 (to_nat_pos _)
        rw [← min_fac_to_nat, to_nat_inj]
        exact ⟨bit0.inj, congr_arg _⟩)
  | bit1 n =>
    decidable_of_iff' (minFacAux (bit1 n) n 1 = bit1 n)
      (by
        refine' nat.prime_def_min_fac.trans ((and_iff_right _).trans _)
        · exact Nat.bit0_le_bit1_iff.2 (to_nat_pos _)
        rw [← min_fac_to_nat, to_nat_inj]; rfl)
#align pos_num.decidable_prime PosNum.decidablePrime

end PosNum

namespace Num

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac : Num → PosNum
  | 0 => 2
  | Pos n => n.minFac
#align num.min_fac Num.minFac

@[simp]
theorem minFac_to_nat : ∀ n : Num, (minFac n : ℕ) = Nat.minFac n
  | 0 => rfl
  | Pos n => PosNum.minFac_to_nat _
#align num.min_fac_to_nat Num.minFac_to_nat

/-- Primality predicate for a `num`. -/
@[simp]
def Prime (n : Num) : Prop :=
  Nat.Prime n
#align num.prime Num.Prime

instance decidablePrime : DecidablePred Num.Prime
  | 0 => Decidable.isFalse Nat.not_prime_zero
  | Pos n => PosNum.decidablePrime n
#align num.decidable_prime Num.decidablePrime

end Num

