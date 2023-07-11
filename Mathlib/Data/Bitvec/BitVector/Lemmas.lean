/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.bitvec.basic
! leanprover-community/mathlib commit 008af8bb14b3ebef7e04ec3b0d63b947dee4d26a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Bitvec.BitVector.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.FinVector.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Init.Data.Nat.Lemmas

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors and their coercions to
`Nat` and `Fin`.
-/
namespace Bitvec.BitVector

open Bitvec (BitVector)

open Nat FinVector


attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

theorem toNat_append {m : ℕ} (xs : BitVector m) (b : Bool) :
    BitVector.toNat (xs++b ::ᵥ nil) =
      BitVector.toNat xs * 2 + BitVector.toNat (b ::ᵥ nil) := by
  simp[BitVector.toNat]
  -- generalize the accumulator of foldl
  suffices ∀ y,
      foldl addLsb y (xs ++ b ::ᵥ nil) 
      = foldl addLsb 0 (b ::ᵥ nil) + foldl addLsb 0 xs * 2
    from this _
  simp only [List.foldl_append, List.foldl]
  induction' xs using FinVector.rec with x xs xs_ih
  · simp
    unfold addLsb
    simp [Nat.mul_succ]
  · simp
    apply xs_ih
#align bitvec.to_nat_append Bitvec.BitVector.toNat_append

-- Porting Note: the mathlib3port version of the proof was :
--  simp [bits_to_nat_to_list]
--  unfold bits_to_nat add_lsb List.foldl cond
--  simp [cond_to_bool_mod_two]
theorem bits_toNat_decide (n : ℕ) :
    BitVector.toNat (decide (n % 2 = 1) ::ᵥ Vector.nil) = n % 2 := by
  simp [bitsToNat_toList]
  unfold bitsToNat addLsb List.foldl
  simp [Nat.cond_decide_mod_two, -Bool.cond_decide]
#align bitvec.bits_to_nat_to_bool Bitvec.BitVector.bits_toNat_decide

theorem ofNat_succ {k n : ℕ} :
    BitVector.ofNat k.succ n = BitVector.ofNat k (n / 2)++decide (n % 2 = 1) ::ᵥ Vector.nil :=
  rfl
#align bitvec.of_nat_succ Bitvec.BitVector.ofNat_succ

theorem toNat_ofNat {k n : ℕ} : BitVector.toNat (BitVector.ofNat k n) = n % 2 ^ k := by
  induction' k with k ih generalizing n
  · simp [Nat.mod_one]
    rfl
  · rw [ofNat_succ, toNat_append, ih, bits_toNat_decide, mod_pow_succ, Nat.mul_comm]
#align bitvec.to_nat_of_nat Bitvec.BitVector.toNat_ofNat

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [ofFin, toNat_ofNat, Nat.mod_eq_of_lt]
  apply i.is_lt
#align bitvec.of_fin_val Bitvec.BitVector.ofFin_val

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]
#align bitvec.add_lsb_eq_twice_add_one Bitvec.BitVector.addLsb_eq_twice_add_one

theorem toNat_eq_foldr_reverse {n : ℕ} (v : BitVector n) :
    v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by rw [List.foldr_reverse]; rfl
#align bitvec.to_nat_eq_foldr_reverse Bitvec.BitVector.toNat_eq_foldr_reverse

theorem toNat_lt {n : ℕ} (v : BitVector n) : v.toNat < 2 ^ n := by
  show v.toNat + 1 ≤ 2 ^ n
  rw [toNat_eq_foldr_reverse]
  cases' v with xs h
  dsimp [BitVector.toNat, bitsToNat]
  rw [← List.length_reverse] at h
  generalize xs.reverse = ys at h
  induction' ys with head tail ih generalizing n
  · simp [← h]
  · simp only [← h, pow_add, flip, List.length, List.foldr, pow_one]
    rw [addLsb_eq_twice_add_one]
    trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => addLsb y x) 0 tail + 2 * 1
    -- Porting note: removed `ac_mono`, `mono` calls
    · rw [add_assoc]
      apply Nat.add_le_add_left
      cases head <;> simp only
    · rw [← left_distrib]
      rw [mul_comm _ 2]
      apply Nat.mul_le_mul_left
      exact ih rfl
#align bitvec.to_nat_lt Bitvec.BitVector.toNat_lt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
      simp only [Nat.add_mul_div_left, addLsb, ← two_mul, add_comm, Nat.succ_pos',
        Nat.mul_div_right, gt_iff_lt, zero_add, cond]
  norm_num
#align bitvec.add_lsb_div_two Bitvec.BitVector.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  cases b <;>
      simp only [Bool.decide_iff, Nat.add_mul_mod_self_left, addLsb, ← two_mul, add_comm,
        Bool.decide_False, Nat.mul_mod_right, zero_add, cond, zero_ne_one]
#align bitvec.to_bool_add_lsb_mod_two Bitvec.BitVector.decide_addLsb_mod_two

theorem ofNat_toNat {n : ℕ} (v : BitVector n) : BitVector.ofNat n v.toNat = v := by
  cases' v with xs h
  -- Porting note: was `ext1`, but that now applies `Vector.ext` rather than `Subtype.ext`.
  apply Subtype.ext
  change Vector.toList _ = xs
  dsimp [BitVector.toNat, bitsToNat]
  rw [← List.length_reverse] at h
  rw [← List.reverse_reverse xs, List.foldl_reverse]
  generalize xs.reverse = ys at h ⊢; clear xs
  induction' ys with ys_head ys_tail ys_ih generalizing n
  · cases h
    simp [BitVector.ofNat]
  · simp only [← Nat.succ_eq_add_one, List.length] at h
    subst n
    simp only [BitVector.ofNat, Vector.toList_cons, Vector.toList_nil, List.reverse_cons,
      Vector.toList_append, List.foldr]
    erw [addLsb_div_two, decide_addLsb_mod_two]
    congr
    apply ys_ih
    rfl
#align bitvec.of_nat_to_nat Bitvec.BitVector.ofNat_toNat

theorem toFin_val {n : ℕ} (v : BitVector n) : (toFin v : ℕ) = v.toNat := by
  rw [toFin, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt]
  apply toNat_lt
#align bitvec.to_fin_val Bitvec.BitVector.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVector n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
#align bitvec.to_fin_le_to_fin_of_le Bitvec.BitVector.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (BitVector.ofNat n i).toNat ≤ (BitVector.ofNat n j).toNat by
    simp only [toNat_ofNat, Nat.mod_eq_of_lt, Fin.is_lt]
    exact h
#align bitvec.of_fin_le_of_fin_of_le Bitvec.BitVector.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
#align bitvec.to_fin_of_fin Bitvec.BitVector.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVector n) : ofFin (toFin v) = v := by
  dsimp [ofFin]
  rw [toFin_val, ofNat_toNat]
#align bitvec.of_fin_to_fin Bitvec.BitVector.ofFin_toFin

end Bitvec.BitVector
