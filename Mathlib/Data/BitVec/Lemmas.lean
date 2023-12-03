/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan
-/

import Mathlib.Data.BitVec.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors.
-/

namespace Std.BitVec

open Nat

#noalign bitvec.bits_to_nat_to_list
#noalign bitvec.to_nat_append

variable {w v : Nat}

theorem toNat_injective {n : Nat} : Function.Injective (@Std.BitVec.toNat n)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  toNat_injective.eq_iff

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  Iff.rfl

attribute [simp] toNat_ofNat toNat_ofFin

lemma toNat_ofNat_of_lt {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := by
  simp only [toNat_ofNat, mod_eq_of_lt h]

#noalign bitvec.bits_to_nat_to_bool

-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`
#noalign bitvec.of_nat_succ

#align bitvec.to_nat_of_nat Std.BitVec.toNat_ofNat

@[simp]
lemma extractLsb_eq {w : ℕ} (hi lo : ℕ) (a : BitVec w) :
    extractLsb hi lo a = extractLsb' lo (hi - lo + 1) a :=
  rfl

theorem toNat_extractLsb' {i j} {x : BitVec w} :
    (extractLsb' i j x).toNat = x.toNat / 2 ^ i % (2 ^ j) := by
  simp only [extractLsb', toNat_ofNat, shiftRight_eq_div_pow]

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val :=
  rfl
#align bitvec.of_fin_val Std.BitVec.ofFin_val

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]; cases b <;> rfl
#align bitvec.add_lsb_eq_twice_add_one Std.BitVec.addLsb_eq_twice_add_one

-- The previous statement was `(v : BitVec n) : v.toNat = v.toList.reverse.foldr (flip addLsb) 0`.
-- Since the statement is awkward and `Std.BitVec` has no comparable API, we just drop it.
#noalign bitvec.to_nat_eq_foldr_reverse

theorem toNat_lt {n : ℕ} (v : BitVec n) : v.toNat < 2 ^ n := by
  exact v.toFin.2
#align bitvec.to_nat_lt Std.BitVec.toNat_lt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  rw [addLsb, ← Nat.div2_val, Nat.div2_bit]
#align bitvec.add_lsb_div_two Std.BitVec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  simp [addLsb]
#align bitvec.to_bool_add_lsb_mod_two Std.BitVec.decide_addLsb_mod_two

lemma ofNat_toNat' (x : BitVec w) : (x.toNat)#w = x := by
  rw [ofNat_toNat, truncate_eq]

lemma ofNat_toNat_of_eq (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h := by
  cases h; rw [ofNat_toNat', cast_eq]

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := by
  rfl
#align bitvec.to_fin_val Std.BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
#align bitvec.to_fin_le_to_fin_of_le Std.BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j := by
  exact h
#align bitvec.of_fin_le_of_fin_of_le Std.BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i := rfl
#align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := rfl
#align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
### `Std.BitVec.ofLEFn` and `Std.BitVec.ofBEFn`
-/

@[simp] lemma ofLEFn_zero (f : Fin 0 → Bool) : ofLEFn f = nil := rfl

@[simp] lemma ofLEFn_cons {w} (b : Bool) (f : Fin w → Bool) :
    ofLEFn (Fin.cons b f) = concat (ofLEFn f) b :=
  rfl

@[simp] lemma ofBEFn_zero (f : Fin 0 → Bool) : ofBEFn f = nil := rfl

@[simp] lemma ofBEFn_cons {w} (b : Bool) (f : Fin w → Bool) :
    ofBEFn (Fin.cons b f) = cons b (ofBEFn f) :=
  rfl

@[simp] lemma Fin.rev_last (n : ℕ) : Fin.rev (Fin.last n) = ⟨0, succ_pos n⟩ := by
  sorry

theorem Fin.cons_comp_rev {α n} (a : α) (f : Fin n → α) :
    Fin.cons a f ∘ Fin.rev = Fin.snoc (f ∘ Fin.rev) a := by
  funext i
  simp only [Function.comp_apply, Function.comp_def]
  induction' f using Fin.consInduction with n b f ih generalizing a
  · funext; simp [Fin.rev, Fin.snoc]
  · simp [Fin.snoc, ih]
    split_ifs with lt_succ_n lt_n
    · have isLt := Nat.sub_lt_self (succ_pos ↑i) (lt_n)
      suffices ∀ h,
          (⟨n + 1 - i.val, h⟩ : Fin (n + 2))
          = Fin.succ (Fin.succ ⟨(n - (i.val + 1)), isLt⟩)
      by simp only [Fin.rev, succ_sub_succ_eq_sub, this, Fin.cons_succ, Fin.coe_castLT];
      intro _
      have one_le_sub : 1 ≤ n - ↑i := Nat.le_sub_of_add_le' lt_n
      simp only [ge_iff_le, sub_succ', tsub_le_iff_right, nonpos_iff_eq_zero, tsub_eq_zero_iff_le,
        tsub_zero, Fin.succ_mk, Fin.mk.injEq,
        Nat.sub_add_cancel (n := n - i.val - 0) one_le_sub,
        Nat.sub_add_comm (lt_succ.mp lt_succ_n)
      ]
    · obtain rfl : i = ⟨n, .step <| .base n⟩ :=
        eq_of_le_of_not_lt (Fin.succ_le_succ_iff.mp lt_succ_n) lt_n
      simp only [Fin.rev, ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
        add_tsub_cancel_left, Fin.mk_one, Fin.cons_one, Fin.cons_zero]
    · obtain rfl : i = Fin.last (n + 1) := sorry
      simp only [rev_last, Fin.zero_eta, Fin.cons_zero]

lemma ofBEFn_eq_ofLEFn_rev (f : Fin w → Bool) :
    ofBEFn f = ofLEFn (f ∘ Fin.rev) := by
  induction' f using Fin.consInduction with w b f ih
  · rw [ofLEFn_zero, ofBEFn_zero]
  · simp [Fin.cons_comp_rev]
    sorry

end Std.BitVec
