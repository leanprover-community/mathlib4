/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum

#align_import data.bitvec.basic from "leanprover-community/mathlib"@"008af8bb14b3ebef7e04ec3b0d63b947dee4d26a"

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors and their coercions to
`Nat` and `Fin`.
-/
namespace Bitvec

open Nat

theorem bitsToNat_toList {n : ℕ} (x : Bitvec n) : Bitvec.toNat x = bitsToNat (Vector.toList x) :=
  rfl
#align bitvec.bits_to_nat_to_list Bitvec.bitsToNat_toList

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

local infixl:65 "++ₜ" => Vector.append

-- mul_left_comm
theorem toNat_append {m : ℕ} (xs : Bitvec m) (b : Bool) :
    Bitvec.toNat (xs++ₜb ::ᵥ Vector.nil) =
      Bitvec.toNat xs * 2 + Bitvec.toNat (b ::ᵥ Vector.nil) := by
  cases' xs with xs P
  -- ⊢ Bitvec.toNat ({ val := xs, property := P }++ₜb ::ᵥ Vector.nil) = Bitvec.toNa …
  simp [bitsToNat_toList]; clear P
  -- ⊢ bitsToNat (xs ++ [b]) = bitsToNat [b] + bitsToNat xs * 2
                           -- ⊢ bitsToNat (xs ++ [b]) = bitsToNat [b] + bitsToNat xs * 2
  unfold bitsToNat
  -- ⊢ List.foldl addLsb 0 (xs ++ [b]) = List.foldl addLsb 0 [b] + List.foldl addLs …
  -- porting note: was `unfold List.foldl`, which now unfolds to an ugly match
  rw [List.foldl, List.foldl]
  -- ⊢ List.foldl addLsb 0 (xs ++ [b]) = addLsb 0 b + List.foldl addLsb 0 xs * 2
  -- generalize the accumulator of foldl
  generalize h : 0 = x
  -- ⊢ List.foldl addLsb x (xs ++ [b]) = addLsb x b + List.foldl addLsb x xs * 2
  conv in addLsb x b =>
    rw [← h]
  clear h
  -- ⊢ List.foldl addLsb x (xs ++ [b]) = addLsb 0 b + List.foldl addLsb x xs * 2
  simp
  -- ⊢ addLsb (List.foldl addLsb x xs) b = addLsb 0 b + List.foldl addLsb x xs * 2
  induction' xs with x xs xs_ih generalizing x
  -- ⊢ addLsb (List.foldl addLsb x []) b = addLsb 0 b + List.foldl addLsb x [] * 2
  · simp
    -- ⊢ addLsb x b = addLsb 0 b + x * 2
    unfold addLsb
    -- ⊢ (x + x + bif b then 1 else 0) = (0 + 0 + bif b then 1 else 0) + x * 2
    simp [Nat.mul_succ]
    -- 🎉 no goals
  · simp
    -- ⊢ addLsb (List.foldl addLsb (addLsb x x✝) xs) b = addLsb 0 b + List.foldl addL …
    apply xs_ih
    -- 🎉 no goals
#align bitvec.to_nat_append Bitvec.toNat_append

-- Porting Note: the mathlib3port version of the proof was :
--  simp [bits_to_nat_to_list]
--  unfold bits_to_nat add_lsb List.foldl cond
--  simp [cond_to_bool_mod_two]
theorem bits_toNat_decide (n : ℕ) : Bitvec.toNat (decide (n % 2 = 1) ::ᵥ Vector.nil) = n % 2 := by
  simp [bitsToNat_toList]
  -- ⊢ bitsToNat [decide (n % 2 = 1)] = n % 2
  unfold bitsToNat addLsb List.foldl
  -- ⊢ List.foldl (fun r b => r + r + bif b then 1 else 0) (0 + 0 + bif decide (n % …
  simp [Nat.cond_decide_mod_two, -Bool.cond_decide]
  -- 🎉 no goals
#align bitvec.bits_to_nat_to_bool Bitvec.bits_toNat_decide

theorem ofNat_succ {k n : ℕ} :
    Bitvec.ofNat k.succ n = Bitvec.ofNat k (n / 2)++ₜdecide (n % 2 = 1) ::ᵥ Vector.nil :=
  rfl
#align bitvec.of_nat_succ Bitvec.ofNat_succ

theorem toNat_ofNat {k n : ℕ} : Bitvec.toNat (Bitvec.ofNat k n) = n % 2 ^ k := by
  induction' k with k ih generalizing n
  -- ⊢ Bitvec.toNat (Bitvec.ofNat zero n) = n % 2 ^ zero
  · simp [Nat.mod_one]
    -- ⊢ Bitvec.toNat (Bitvec.ofNat 0 n) = 0
    rfl
    -- 🎉 no goals
  · rw [ofNat_succ, toNat_append, ih, bits_toNat_decide, mod_pow_succ, Nat.mul_comm]
    -- 🎉 no goals
#align bitvec.to_nat_of_nat Bitvec.toNat_ofNat

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [ofFin, toNat_ofNat, Nat.mod_eq_of_lt]
  -- ⊢ ↑i < 2 ^ n
  apply i.is_lt
  -- 🎉 no goals
#align bitvec.of_fin_val Bitvec.ofFin_val

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]
  -- 🎉 no goals
#align bitvec.add_lsb_eq_twice_add_one Bitvec.addLsb_eq_twice_add_one

theorem toNat_eq_foldr_reverse {n : ℕ} (v : Bitvec n) :
    v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by rw [List.foldr_reverse]; rfl
                                                           -- ⊢ Bitvec.toNat v = List.foldl (fun x y => flip addLsb y x) 0 (Vector.toList v)
                                                                                    -- 🎉 no goals
#align bitvec.to_nat_eq_foldr_reverse Bitvec.toNat_eq_foldr_reverse

theorem toNat_lt {n : ℕ} (v : Bitvec n) : v.toNat < 2 ^ n := by
  suffices : v.toNat + 1 ≤ 2 ^ n; simpa
  -- ⊢ Bitvec.toNat v < 2 ^ n
                                  -- ⊢ Bitvec.toNat v + 1 ≤ 2 ^ n
  rw [toNat_eq_foldr_reverse]
  -- ⊢ List.foldr (flip addLsb) 0 (List.reverse (Vector.toList v)) + 1 ≤ 2 ^ n
  cases' v with xs h
  -- ⊢ List.foldr (flip addLsb) 0 (List.reverse (Vector.toList { val := xs, propert …
  dsimp [Bitvec.toNat, bitsToNat]
  -- ⊢ List.foldr (flip addLsb) 0 (List.reverse xs) + 1 ≤ 2 ^ n
  rw [← List.length_reverse] at h
  -- ⊢ List.foldr (flip addLsb) 0 (List.reverse xs) + 1 ≤ 2 ^ n
  generalize xs.reverse = ys at h
  -- ⊢ List.foldr (flip addLsb) 0 ys + 1 ≤ 2 ^ n
  induction' ys with head tail ih generalizing n
  -- ⊢ List.foldr (flip addLsb) 0 [] + 1 ≤ 2 ^ n
  · simp [← h]
    -- 🎉 no goals
  · simp only [← h, pow_add, flip, List.length, List.foldr, pow_one]
    -- ⊢ addLsb (List.foldr (fun b a => addLsb a b) 0 tail) head + 1 ≤ 2 ^ List.lengt …
    rw [addLsb_eq_twice_add_one]
    -- ⊢ (2 * List.foldr (fun b a => addLsb a b) 0 tail + bif head then 1 else 0) + 1 …
    trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => addLsb y x) 0 tail + 2 * 1
    -- ⊢ (2 * List.foldr (fun b a => addLsb a b) 0 tail + bif head then 1 else 0) + 1 …
    -- Porting note: removed `ac_mono`, `mono` calls
    · rw [add_assoc]
      -- ⊢ 2 * List.foldr (fun b a => addLsb a b) 0 tail + ((bif head then 1 else 0) +  …
      apply Nat.add_le_add_left
      -- ⊢ (bif head then 1 else 0) + 1 ≤ 2 * 1
      cases head <;> simp only
      -- ⊢ (bif false then 1 else 0) + 1 ≤ 2 * 1
                     -- 🎉 no goals
                     -- 🎉 no goals
    · rw [← left_distrib]
      -- ⊢ 2 * (List.foldr (fun x y => addLsb y x) 0 tail + 1) ≤ 2 ^ List.length tail * 2
      rw [mul_comm _ 2]
      -- ⊢ 2 * (List.foldr (fun x y => addLsb y x) 0 tail + 1) ≤ 2 * 2 ^ List.length tail
      apply Nat.mul_le_mul_left
      -- ⊢ List.foldr (fun x y => addLsb y x) 0 tail + 1 ≤ 2 ^ List.length tail
      exact ih rfl
      -- 🎉 no goals
#align bitvec.to_nat_lt Bitvec.toNat_lt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
  -- ⊢ addLsb x false / 2 = x
      simp only [Nat.add_mul_div_left, addLsb, ← two_mul, add_comm, Nat.succ_pos',
        Nat.mul_div_right, gt_iff_lt, zero_add, cond]
  norm_num
  -- 🎉 no goals
#align bitvec.add_lsb_div_two Bitvec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  cases b <;>
  -- ⊢ decide (addLsb x false % 2 = 1) = false
      simp only [Bool.decide_iff, Nat.add_mul_mod_self_left, addLsb, ← two_mul, add_comm,
        Bool.decide_False, Nat.mul_mod_right, zero_add, cond, zero_ne_one]
#align bitvec.to_bool_add_lsb_mod_two Bitvec.decide_addLsb_mod_two

theorem ofNat_toNat {n : ℕ} (v : Bitvec n) : Bitvec.ofNat n v.toNat = v := by
  cases' v with xs h
  -- ⊢ Bitvec.ofNat n (Bitvec.toNat { val := xs, property := h }) = { val := xs, pr …
  -- Porting note: was `ext1`, but that now applies `Vector.ext` rather than `Subtype.ext`.
  apply Subtype.ext
  -- ⊢ ↑(Bitvec.ofNat n (Bitvec.toNat { val := xs, property := h })) = ↑{ val := xs …
  change Vector.toList _ = xs
  -- ⊢ Vector.toList (Bitvec.ofNat n (Bitvec.toNat { val := xs, property := h })) = …
  dsimp [Bitvec.toNat, bitsToNat]
  -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldl addLsb 0 xs)) = xs
  rw [← List.length_reverse] at h
  -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldl addLsb 0 xs)) = xs
  rw [← List.reverse_reverse xs, List.foldl_reverse]
  -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldr (fun x y => addLsb y x) 0 (List.re …
  generalize xs.reverse = ys at h ⊢; clear xs
  -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldr (fun x y => addLsb y x) 0 ys)) = L …
                                     -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldr (fun x y => addLsb y x) 0 ys)) = L …
  induction' ys with ys_head ys_tail ys_ih generalizing n
  -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldr (fun x y => addLsb y x) 0 [])) = L …
  · cases h
    -- ⊢ Vector.toList (Bitvec.ofNat (List.length []) (List.foldr (fun x y => addLsb  …
    simp [Bitvec.ofNat]
    -- 🎉 no goals
  · simp only [← Nat.succ_eq_add_one, List.length] at h
    -- ⊢ Vector.toList (Bitvec.ofNat n (List.foldr (fun x y => addLsb y x) 0 (ys_head …
    subst n
    -- ⊢ Vector.toList (Bitvec.ofNat (succ (List.length ys_tail)) (List.foldr (fun x  …
    simp only [Bitvec.ofNat, Vector.toList_cons, Vector.toList_nil, List.reverse_cons,
      Vector.toList_append, List.foldr]
    erw [addLsb_div_two, decide_addLsb_mod_two]
    -- ⊢ Vector.toList (Bitvec.ofNat (List.length ys_tail) (List.foldr (fun x y => ad …
    congr
    -- ⊢ Vector.toList (Bitvec.ofNat (List.length ys_tail) (List.foldr (fun x y => ad …
    apply ys_ih
    -- ⊢ List.length ys_tail = List.length ys_tail
    rfl
    -- 🎉 no goals
#align bitvec.of_nat_to_nat Bitvec.ofNat_toNat

theorem toFin_val {n : ℕ} (v : Bitvec n) : (toFin v : ℕ) = v.toNat := by
  rw [toFin, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt]
  -- ⊢ Bitvec.toNat v < 2 ^ n
  apply toNat_lt
  -- 🎉 no goals
#align bitvec.to_fin_val Bitvec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : Bitvec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    -- ⊢ Bitvec.toNat v₀ ≤ Bitvec.toNat v₁
    exact h
    -- 🎉 no goals
#align bitvec.to_fin_le_to_fin_of_le Bitvec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (Bitvec.ofNat n i).toNat ≤ (Bitvec.ofNat n j).toNat by
    simp only [toNat_ofNat, Nat.mod_eq_of_lt, Fin.is_lt]
    -- ⊢ ↑i ≤ ↑j
    exact h
    -- 🎉 no goals
#align bitvec.of_fin_le_of_fin_of_le Bitvec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
                    -- 🎉 no goals
#align bitvec.to_fin_of_fin Bitvec.toFin_ofFin

theorem ofFin_toFin {n} (v : Bitvec n) : ofFin (toFin v) = v := by
  dsimp [ofFin]
  -- ⊢ Bitvec.ofNat n ↑(toFin v) = v
  rw [toFin_val, ofNat_toNat]
  -- 🎉 no goals
#align bitvec.of_fin_to_fin Bitvec.ofFin_toFin

end Bitvec
