/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.bitvec.basic
! leanprover-community/mathlib commit 008af8bb14b3ebef7e04ec3b0d63b947dee4d26a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Bitvec.Core
import Mathbin.Data.Fin.Basic
import Mathbin.Tactic.Monotonicity.Default
import Mathbin.Tactic.NormNum

namespace Bitvec

instance (n : ℕ) : Preorder (Bitvec n) :=
  Preorder.lift Bitvec.toNat

/-- convert `fin` to `bitvec` -/
def ofFin {n : ℕ} (i : Fin <| 2 ^ n) : Bitvec n :=
  Bitvec.ofNat _ i.val
#align bitvec.of_fin Bitvec.ofFin

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [of_fin, to_nat_of_nat, Nat.mod_eq_of_lt] <;> apply i.is_lt
#align bitvec.of_fin_val Bitvec.ofFin_val

/-- convert `bitvec` to `fin` -/
def toFin {n : ℕ} (i : Bitvec n) : Fin <| 2 ^ n :=
  i.toNat
#align bitvec.to_fin Bitvec.toFin

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [add_lsb, two_mul]
#align bitvec.add_lsb_eq_twice_add_one Bitvec.addLsb_eq_twice_add_one

theorem toNat_eq_foldr_reverse {n : ℕ} (v : Bitvec n) :
    v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by rw [List.foldr_reverse, flip] <;> rfl
#align bitvec.to_nat_eq_foldr_reverse Bitvec.toNat_eq_foldr_reverse

theorem toNat_lt {n : ℕ} (v : Bitvec n) : v.toNat < 2 ^ n :=
  by
  suffices v.to_nat + 1 ≤ 2 ^ n by simpa
  rw [to_nat_eq_foldr_reverse]
  cases' v with xs h
  dsimp [Bitvec.toNat, bits_to_nat]
  rw [← List.length_reverse] at h
  generalize xs.reverse = ys at h⊢
  clear xs
  induction ys generalizing n
  · simp [← h]
  · simp only [← h, pow_add, flip, List.length, List.foldr, pow_one]
    rw [add_lsb_eq_twice_add_one]
    trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => add_lsb y x) 0 ys_tl + 2 * 1
    · ac_mono
      rw [two_mul]
      mono
      cases ys_hd <;> simp
    · rw [← left_distrib]
      ac_mono
      exact ys_ih rfl
      norm_num
#align bitvec.to_nat_lt Bitvec.toNat_lt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
      simp only [Nat.add_mul_div_left, add_lsb, ← two_mul, add_comm, Nat.succ_pos',
        Nat.mul_div_right, gt_iff_lt, zero_add, cond] <;>
    norm_num
#align bitvec.add_lsb_div_two Bitvec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  cases b <;>
      simp only [Bool.decide_iff, Nat.add_mul_mod_self_left, add_lsb, ← two_mul, add_comm,
        Bool.decide_False, Nat.mul_mod_right, zero_add, cond, zero_ne_one] <;>
    norm_num
#align bitvec.to_bool_add_lsb_mod_two Bitvec.decide_addLsb_mod_two

theorem ofNat_toNat {n : ℕ} (v : Bitvec n) : Bitvec.ofNat _ v.toNat = v :=
  by
  cases' v with xs h
  ext1
  change Vector.toList _ = xs
  dsimp [Bitvec.toNat, bits_to_nat]
  rw [← List.length_reverse] at h
  rw [← List.reverse_reverse xs, List.foldl_reverse]
  generalize xs.reverse = ys at h⊢; clear xs
  induction ys generalizing n
  · cases h
    simp [Bitvec.ofNat]
  · simp only [← Nat.succ_eq_add_one, List.length] at h
    subst n
    simp only [Bitvec.ofNat, Vector.toList_cons, Vector.toList_nil, List.reverse_cons,
      Vector.toList_append, List.foldr]
    erw [add_lsb_div_two, to_bool_add_lsb_mod_two]
    congr
    apply ys_ih
    rfl
#align bitvec.of_nat_to_nat Bitvec.ofNat_toNat

theorem toFin_val {n : ℕ} (v : Bitvec n) : (toFin v : ℕ) = v.toNat := by
  rw [to_fin, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt] <;> apply to_nat_lt
#align bitvec.to_fin_val Bitvec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : Bitvec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by rw [to_fin_val, to_fin_val] <;> exact h
#align bitvec.to_fin_le_to_fin_of_le Bitvec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (Bitvec.ofNat n i).toNat ≤ (Bitvec.ofNat n j).toNat
    by
    simp only [to_nat_of_nat, Nat.mod_eq_of_lt, Fin.is_lt]
    exact h
#align bitvec.of_fin_le_of_fin_of_le Bitvec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [to_fin_val, of_fin, to_nat_of_nat, Nat.mod_eq_of_lt, i.is_lt])
#align bitvec.to_fin_of_fin Bitvec.toFin_ofFin

theorem ofFin_toFin {n} (v : Bitvec n) : ofFin (toFin v) = v := by
  dsimp [of_fin] <;> rw [to_fin_val, of_nat_to_nat]
#align bitvec.of_fin_to_fin Bitvec.ofFin_toFin

end Bitvec

