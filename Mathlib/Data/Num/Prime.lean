/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Num.Lemmas
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Ring

#align_import data.num.prime from "leanprover-community/mathlib"@"58581d0fe523063f5651df0619be2bf65012a94a"

/-!
# Primality for binary natural numbers

This file defines versions of `Nat.minFac` and `Nat.Prime` for `Num` and `PosNum`. As with other
`Num` definitions, they are not intended for general use (`Nat` should be used instead of `Num` in
most cases) but they can be used in contexts where kernel computation is required, such as proofs
by `rfl` and `decide`, as well as in `#reduce`.

The default decidable instance for `Nat.Prime` is optimized for VM evaluation, so it should be
preferred within `#eval` or in tactic execution, while for proofs the `norm_num` tactic can be used
to construct primality and non-primality proofs more efficiently than kernel computation.

Nevertheless, sometimes proof by computational reflection requires natural number computations, and
`Num` implements algorithms directly on binary natural numbers for this purpose.
-/


namespace PosNum

/-- Auxiliary function for computing the smallest prime factor of a `PosNum`. Unlike
`Nat.minFacAux`, we use a natural number `fuel` variable that is set to an upper bound on the
number of iterations. It is initialized to the number `n` we are determining primality for. Even
though this is exponential in the input (since it is a `Nat`, not a `Num`), it will get lazily
evaluated during kernel reduction, so we will only require about `sqrt n` unfoldings, for the
`sqrt n` iterations of the loop. -/
def minFacAux (n : PosNum) : ℕ → PosNum → PosNum
  | 0, _ => n
  | fuel + 1, k =>
    if n < k.bit1 * k.bit1 then n else if k.bit1 ∣ n then k.bit1 else minFacAux n fuel k.succ
#align pos_num.min_fac_aux PosNum.minFacAux

set_option linter.deprecated false in
theorem minFacAux_to_nat {fuel : ℕ} {n k : PosNum} (h : Nat.sqrt n < fuel + k.bit1) :
    (minFacAux n fuel k : ℕ) = Nat.minFacAux n k.bit1 := by
  induction' fuel with fuel ih generalizing k <;> rw [minFacAux, Nat.minFacAux]
  · rw [Nat.zero_add, Nat.sqrt_lt] at h
    simp only [h, ite_true]
  simp_rw [← mul_to_nat]
  simp only [cast_lt, dvd_to_nat]
  split_ifs <;> try rfl
  rw [ih] <;> [congr; convert Nat.lt_succ_of_lt h using 1] <;>
    simp only [_root_.bit1, _root_.bit0, cast_bit1, cast_succ, Nat.succ_eq_add_one, add_assoc,
      add_left_comm, ← one_add_one_eq_two]
#align pos_num.min_fac_aux_to_nat PosNum.minFacAux_to_nat

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac : PosNum → PosNum
  | 1 => 1
  | bit0 _ => 2
  | bit1 n => minFacAux (bit1 n) n 1
#align pos_num.min_fac PosNum.minFac

@[simp]
theorem minFac_to_nat (n : PosNum) : (minFac n : ℕ) = Nat.minFac n := by
  cases' n with n
  · rfl
  · rw [minFac, Nat.minFac_eq, if_neg]
    swap
    · simp
    rw [minFacAux_to_nat]
    · rfl
    simp only [cast_one, cast_bit1]
    unfold _root_.bit1 _root_.bit0
    rw [Nat.sqrt_lt]
    calc
      (n : ℕ) + (n : ℕ) + 1 ≤ (n : ℕ) + (n : ℕ) + (n : ℕ) := by simp
      _ = (n : ℕ) * (1 + 1 + 1) := by simp only [mul_add, mul_one]
      _ < _ := by
        set_option simprocs false in simp [mul_lt_mul]
  · rw [minFac, Nat.minFac_eq, if_pos]
    · rfl
    simp
#align pos_num.min_fac_to_nat PosNum.minFac_to_nat

/-- Primality predicate for a `PosNum`. -/
@[simp]
def Prime (n : PosNum) : Prop :=
  Nat.Prime n
#align pos_num.prime PosNum.Prime

instance decidablePrime : DecidablePred PosNum.Prime
  | 1 => Decidable.isFalse Nat.not_prime_one
  | bit0 n =>
    decidable_of_iff' (n = 1)
      (by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans <| eq_comm.trans ?_)
        · exact add_le_add (Nat.succ_le_of_lt (to_nat_pos _)) (Nat.succ_le_of_lt (to_nat_pos _))
        rw [← minFac_to_nat, to_nat_inj]
        exact ⟨bit0.inj, congr_arg _⟩)
  | bit1 n =>
    decidable_of_iff' (minFacAux (bit1 n) n 1 = bit1 n)
      (by
        refine Nat.prime_def_minFac.trans ((and_iff_right ?_).trans ?_)
        · exact Nat.bit0_le_bit1_iff.2 (to_nat_pos _)
        rw [← minFac_to_nat, to_nat_inj]; rfl)
#align pos_num.decidable_prime PosNum.decidablePrime

end PosNum

namespace Num

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def minFac : Num → PosNum
  | 0 => 2
  | pos n => n.minFac
#align num.min_fac Num.minFac

@[simp]
theorem minFac_to_nat : ∀ n : Num, (minFac n : ℕ) = Nat.minFac n
  | 0 => rfl
  | pos _ => PosNum.minFac_to_nat _
#align num.min_fac_to_nat Num.minFac_to_nat

/-- Primality predicate for a `Num`. -/
@[simp]
def Prime (n : Num) : Prop :=
  Nat.Prime n
#align num.prime Num.Prime

instance decidablePrime : DecidablePred Num.Prime
  | 0 => Decidable.isFalse Nat.not_prime_zero
  | pos n => PosNum.decidablePrime n
#align num.decidable_prime Num.decidablePrime

end Num
