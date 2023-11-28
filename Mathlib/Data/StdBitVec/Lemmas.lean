/-
Copyright (c) 2023 Harun Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Alex Keizer
-/

import Std.Data.BitVec
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors, as defined in `Std`.

Note that `Std.BitVec` is distinct from mathlibs `Bitvec` type, this file is about the former.
For the latter, go to `Data.Bitvec` (notice the difference in capitalization).
Eventually, `Std.BitVec` will replace `Bitvec`, so we include the relevant `#align`s, but
comment them out for now
-/

namespace Std.BitVec

open Nat

variable {w v : Nat}

/-!
## Conversions
Theorems about `ofNat`, `toNat`, `ofFin`, `toFin`, `ofBool`, etc.
-/

/-! ### toNat -/

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  ⟨id, id⟩

theorem toNat_lt {n : ℕ} (v : BitVec n) : v.toNat < 2 ^ n :=
  v.toFin.isLt
-- #align bitvec.to_nat_lt Std.BitVec.toNat_lt

theorem toNat_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := Fin.val_cast_of_lt h
-- #align bitvec.to_nat_of_nat Std.BitVec.toNat_ofNat

@[simp] lemma toNat_ofFin (x : Fin (2^w)) : (ofFin x).toNat = x.val := rfl

@[simp] lemma toNat_cast {w w'} {h : w = w'} {v : BitVec w} :
    (cast h v).toNat = v.toNat := rfl

-- #noalign bitvec.bits_to_nat_to_bool

@[simp] lemma toNat_cons (b : Bool) (v : BitVec w) :
    (cons b v).toNat = b.toNat <<< w ||| v.toNat :=
  by  dsimp only [cons, (. ++ .), append, toNat_cast]
      rw [toNat_ofNat]
      . cases b <;> rfl
      . apply bitwise_lt
        . rw [Nat.shiftLeft_eq, Nat.pow_add, pow_one]
          refine (mul_lt_mul_right (Nat.two_pow_pos w)).mpr ?_
          . cases b
            . exact zero_lt_two
            . exact one_lt_two
        . rw [Nat.add_comm]
          exact lt_trans (toNat_lt v) (Nat.pow_lt_pow_succ one_lt_two w)

@[simp]
lemma toNat_neg (xs : BitVec w) :
    (-xs).toNat = (xs.toNat != 0).toNat * 2^w - xs.toNat := by
  rw [show (-xs).toNat = (2^w - xs.toNat) % 2^w
      from congrArg (. % 2^w) (Nat.zero_add _)]
  by_cases h : xs.toNat = 0
  . simp [h]
  . rw [(bne_iff_ne _ _).mpr h, Bool.toNat_true, Nat.one_mul]
    refine Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) (Nat.pos_of_ne_zero h))

@[simp]
lemma toNat_allOnes (w : ℕ) : (BitVec.allOnes w).toNat = 2^w - 1 := by
  refine Eq.trans (toNat_neg _) ?_
  by_cases h : w = 0
  . subst w; rfl
  . rw [show BitVec.toNat 1 = 1
        from toNat_ofNat $ Nat.one_lt_two_pow w $ Nat.pos_of_ne_zero h]
    refine congrArg₂ _ (Nat.one_mul _) rfl

/-! ### ofNat -/

@[simp]
lemma ofNat_eq_mod_two_pow (n : Nat) : (BitVec.ofNat w n).toNat = n % 2^w := rfl

@[simp]
lemma ofNat_toNat (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rcases x with ⟨x⟩
  simp [BitVec.ofNat]
  apply Fin.cast_val_eq_self x
#align bitvec.of_nat_to_nat Std.BitVec.ofNat_toNat

lemma ofNat_toNat' (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h := by
  cases h; rw [ofNat_toNat, cast_eq]

/-! ### OfFin / ToFin -/

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rfl
-- #align bitvec.of_fin_val Std.BitVec.ofFin_val

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := by
  rfl
-- #align bitvec.to_fin_val Std.BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
-- #align bitvec.to_fin_le_to_fin_of_le Std.BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j := by
  exact h
-- #align bitvec.of_fin_le_of_fin_of_le Std.BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
-- #align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := by
  rfl
-- #align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
  ### Distributivity of ofFin
  We add simp-lemmas that show how `ofFin` distributes over various bitvector operations, showing
  that bitvector operations are equivalent to `Fin` operations
-/
@[simp] lemma neg_ofFin (x : Fin (2^w)) : -(ofFin x) = ofFin (-x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma ofFin_and_ofFin (x y : Fin (2^w)) : ofFin x &&& ofFin y = ofFin (x &&& y) := rfl
@[simp] lemma ofFin_or_ofFin  (x y : Fin (2^w)) : ofFin x ||| ofFin y = ofFin (x ||| y) := rfl
@[simp] lemma ofFin_xor_ofFin (x y : Fin (2^w)) : ofFin x ^^^ ofFin y = ofFin (x ^^^ y) := rfl
@[simp] lemma ofFin_add_ofFin (x y : Fin (2^w)) : ofFin x + ofFin y   = ofFin (x + y)   := rfl
@[simp] lemma ofFin_sub_ofFin (x y : Fin (2^w)) : ofFin x - ofFin y   = ofFin (x - y)   := rfl
@[simp] lemma ofFin_mul_ofFin (x y : Fin (2^w)) : ofFin x * ofFin y   = ofFin (x * y)   := rfl

@[simp] lemma toFin_sub (x y : BitVec w) : (x - y).toFin = x.toFin - y.toFin := rfl

/-!
## Extract / Get bits
-/

@[simp]
lemma extractLsb_eq {w : ℕ} (hi lo : ℕ) (a : BitVec w) :
    extractLsb hi lo a = extractLsb' lo (hi - lo + 1) a :=
  rfl

theorem toNat_extractLsb' {i j} {x : BitVec w} :
    (extractLsb' i j x).toNat = x.toNat / 2 ^ i % (2 ^ j) := by
  simp only [extractLsb', ofNat_eq_mod_two_pow, shiftRight_eq_div_pow]

theorem getLsb_eq_testBit {i} {x : BitVec w} : getLsb x i = x.toNat.testBit i := by
  simp only [getLsb, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow]
  cases' testBit (BitVec.toNat x) i
  <;> simp [pos_iff_ne_zero.mp (Nat.two_pow_pos i)]

theorem getMsb_eq_testBit {i} {x : BitVec w} :
    getMsb x i = (i < w && x.toNat.testBit (w - i.succ)) :=
  congrArg _
  $ Eq.trans getLsb_eq_testBit
  $ congrArg (testBit (BitVec.toNat x))
  $ Eq.trans (Nat.sub_sub w 1 i)
  $ congrArg (w - .) $ Nat.one_add i

theorem msb_eq_testBit {x : BitVec w} : x.msb = x.toNat.testBit (w - 1) :=
  Eq.trans (@getMsb_eq_testBit w 0 x)
  $ if h : 0 < w
    then decide_eq_true h ▸ Bool.true_and _
    else by simp only [not_lt, nonpos_iff_eq_zero] at h; subst w; rw [x.eq_nil]
            rfl

/-!
## Ext
-/

namespace Nat
open Nat

lemma two_pow_succ_eq_bit_false (x : Nat) :
    2^(x+1) = bit false (2^x) := by
  rw [Nat.pow_succ, Nat.mul_two]; rfl

@[simp] lemma bit_and_two_pow_succ (x₀ : Bool) (x n : Nat) :
    bit x₀ x &&& 2^(n + 1) = bit false (x &&& 2^n) := by
  show bitwise .. = bit _ (bitwise ..)
  rw [two_pow_succ_eq_bit_false, bitwise_bit, Bool.and_false]

@[simp] theorem bit_mod_two_pow_succ (b x w) :
    bit b x % 2 ^ (w + 1) = bit b (x % 2 ^ w) := by
  simp [bit_val, Nat.pow_succ, mul_comm 2]
  cases b <;> simp [mul_mod_mul_right]
  · have h1 : 1 = 1 % (2 ^ w * 2) :=
      (mod_eq_of_lt <| one_lt_mul (one_le_two_pow w) (by decide)).symm
    conv_rhs => {
      rw [←mul_mod_mul_right, h1, ←add_mod_of_add_mod_lt <| by
        rw [mul_mod_mul_right, mul_two, mul_two, add_assoc, add_comm]
        have : x % 2 ^ w < 2 ^ w :=
          mod_lt x (Nat.pow_two_pos w)
        apply add_lt_add_of_le_of_lt _ this
        · rw [←mul_two, ←h1]; exact this
      ]
    }

theorem two_pow_succ_sub_one_eq_bit (w : Nat) : 2 ^ succ w - 1 = bit true (2^w - 1) := by
  induction' w with w ih
  · rfl
  · simp only [Nat.pow_succ, Nat.mul_two, Nat.add_sub_assoc (one_le_two_pow _), ih, bit_val,
      Nat.two_mul, Bool.cond_true]
    conv_rhs => {
      rw [←add_assoc]
      change 2 ^ w + (2 ^ w - 1) + 2 ^ w + ((2 ^ w - 1) + 1)
      rw [
        Nat.sub_add_cancel (one_le_two_pow _),
        add_assoc, ←two_mul (2 ^ w),
        Nat.self_add_sub_one, Nat.sub_one_add_self
      ]
    }
    ring_nf

lemma size_land_le_left {n m} : size (n &&& m) ≤ size n := by
  have {a b} (h' : a &&& b = 0) : size (a &&& b) ≤ size a := h' ▸ Nat.zero_le _
  revert n; induction' m using binaryRec with b₂ k₂ ih <;> intro n
  . exact this (Nat.land_zero _)
  . cases' n using bitCasesOn with b₁ k₁ ih
    refine Or.rec this ?_ (eq_or_ne _ _)
    intro h
    rw [size_bit]
    . rw [land_bit] at h ⊢
      rw [size_bit, Nat.succ_le_succ_iff]
      . exact ih
      . exact h
    . exact mt (. ▸ Nat.zero_land _) h

lemma size_land_le_right {n m} : size (n &&& m) ≤ size m :=
  land_comm n m ▸ size_land_le_left

@[simp]
lemma testBit_two_pow_sub_one {i} : testBit (2^w - 1) i = (i < w : Bool) := by
  revert i; induction' w with w ih <;> intro i
  . simp only [Nat.not_lt_zero, decide_False]
    exact zero_testBit i
  . rw [two_pow_succ_sub_one_eq_bit]
    cases i
    . simp only [Nat.zero_lt_succ, decide_True]
      exact Nat.testBit_zero true _
    . simp only [ih, Nat.testBit_succ]
      exact Eq.symm (Bool.decide_congr Nat.succ_lt_succ_iff)

lemma shiftLeft_add_eq_shiftLeft_lor :
    ∀ (n m : ℕ), m < 2^w → n <<< w + m = n <<< w ||| m := by
  induction' w with w ih
  . simp
  . intros n m h
    cases' m using Nat.bitCasesOn with b m
    rw [Nat.shiftLeft_succ, ← Nat.bit0_val, ← Nat.bit_false, ← Nat.bit_add,
        ih, Nat.lor_bit, Bool.false_or]
    exact bit_lt_two_pow_succ_iff.mp h

lemma shiftRight_sub (m : ℕ) {n k : ℕ} (h : k ≤ n) :
    m >>> (n - k) = (m <<< k) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  refine Eq.symm ?_
  refine Eq.trans (congrArg _ $ Eq.trans ?_ $ Nat.pow_add 2 (n - k) k) ?_
  . exact congrArg _ (Nat.sub_add_cancel h).symm
  . exact Nat.mul_div_mul_right _ _ (two_pow_pos k)

@[simp]
lemma testBit_shiftLeft (k w i : ℕ) :
    testBit (k <<< w) i = (i ≥ w && testBit k (i - w)) := by
  revert k i; induction' w with w ih <;> intros k i
  . simp
  . rw [shiftLeft_succ, ← bit0_val, ← bit_false]
    cases i
    . simp only [testBit_zero, zero_sub, zero_eq, ge_iff_le, le_zero,
                 decide_False, Bool.false_and]
    . simp only [testBit_succ, ih, succ_le_succ_iff, Nat.succ_sub_succ]

end Nat

-- Orphan :(

/-!
## Cons
-/

theorem Nat.mod_two_pow (x n : Nat) :
    x % (2^n) = x &&& 2^n - 1 := by
  induction' n with n ih generalizing x
  · simp only [Nat.zero_eq, _root_.pow_zero, mod_one, le_refl, tsub_eq_zero_of_le, land_zero]
  · cases' x using Nat.binaryRec with x₀ x _xih
    · rfl
    · simp [Nat.two_pow_succ_sub_one_eq_bit, -bit_true, ih]

@[simp] lemma Nat.bit_div_two (b : Bool) (x : Nat) : bit b x / 2 = x := by
  rw [←div2_val, div2_bit]

@[simp (high)]
lemma Nat.bit_shiftRight_succ (b : Bool) (x n : ℕ) :
    bit b x >>> (n + 1) = x >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm, ←Nat.div_div_eq_div_mul,
    bit_div_two]

@[simp]
lemma Nat.testBit_shiftRight (k w i : ℕ) :
    testBit (k >>> w) i = testBit k (i + w) := by
  revert k i; induction' w with w ih <;> intros k i
  . simp
  . cases' k using bitCasesOn with b k
    rw [add_succ, testBit_succ]
    exact Eq.trans (congrArg₂ _ (bit_shiftRight_succ _ _ _) rfl) (ih k i)

@[simp] lemma toNat_zeroExtend (xs : BitVec w) :
    (zeroExtend v xs).toNat = xs.toNat &&& (BitVec.allOnes v).toNat := by
  dsimp only [zeroExtend]
  rw [ofNat_eq_mod_two_pow, toNat_allOnes]
  apply Nat.mod_two_pow

@[simp] lemma toNat_truncate (xs : BitVec w) :
    (truncate v xs).toNat = xs.toNat &&& (BitVec.allOnes v).toNat :=
  toNat_zeroExtend xs

lemma ofBool_eq_cond (b : Bool) : ofBool b = bif b then 1 else 0 := by
  cases b <;> rfl

@[simp] lemma toNat_ofBool (b : Bool) : BitVec.toNat (ofBool b) = b.toNat := by
  cases b <;> rfl

theorem bitwise_self (f : Bool → Bool → Bool) (x : ℕ) (hf : f false false = false) :
    bitwise f x x = if f true true = true then x else 0 := by
  split_ifs with hf' <;> (
    induction' x using Nat.binaryRec with x₀ x ih
    · simp only [ne_eq, not_true_eq_false, bitwise_zero_right, ite_self]
    · rw [bitwise_bit (h:=hf), ih]
      cases x₀ <;> simp [hf, hf']
  )

theorem bitwise_self_eq_self (f : Bool → Bool → Bool)
    (hf : f false false = false) (hf' : f true true = true) (x : ℕ) :
    bitwise f x x = x := by
  simp [bitwise_self _ _ hf, hf']

theorem bitwise_self_eq_zero (f : Bool → Bool → Bool)
    (hf : f false false = false) (hf' : f true true = false) (x : ℕ) :
    bitwise f x x = 0 := by
  simp [bitwise_self _ _ hf, hf']

@[simp] lemma land_self (x : Nat) : x &&& x = x :=
  bitwise_self_eq_self _ rfl rfl _

@[simp] lemma lor_self (x : Nat) : x ||| x = x :=
  bitwise_self_eq_self _ rfl rfl _

@[simp] lemma xor_self (x : Nat) : x ^^^ x = 0 :=
  bitwise_self_eq_zero _ rfl rfl _

@[simp] lemma land_land_self (x y : Nat) :
    x &&& y &&& y = x &&& y := by
  rw [land_assoc, land_self]

theorem and_two_pow_or_and_two_pow_sub_one (x n : ℕ) :
    x &&& 2^n ||| x &&& 2^n - 1 = x &&& 2^(n+1) - 1 := by
  induction' x using Nat.binaryRec with x₀ x ih generalizing n
  · rfl
  · cases' n with n
    · simp
    · simp [-bit_false, -bit_true, Nat.two_pow_succ_sub_one_eq_bit, ih]

@[simp]
theorem cons_msb_truncate : ∀ (xs : BitVec (w+1)), cons xs.msb (xs.truncate w) = xs
  | ⟨⟨xs, h⟩⟩ => by
      simp [
        cons, BitVec.msb, getMsb, truncate, zeroExtend, (· ++ ·), BitVec.append, cast,
        Fin.cast, BitVec.ofNat, Fin.ofNat', Nat.zero_lt_succ, Nat.succ_sub_one, Nat.mod_two_pow
      ]
      rw [
        getLsb_eq_testBit, toNat_ofFin, ←and_two_pow, and_two_pow_or_and_two_pow_sub_one xs w,
        Nat.add_comm 1 w, land_land_self, ←Nat.mod_two_pow, Nat.mod_eq_of_lt h
      ]

@[elab_as_elim]
def consRecOn {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs)) :
    ∀ {w} (x : BitVec w), motive x
  | 0,    x => _root_.cast (by rw[eq_nil x]) nil
  | w+1,  x => _root_.cast (by rw[cons_msb_truncate]) <|
      cons x.msb (x.truncate w) (consRecOn nil cons <| x.truncate w)

@[simp]
theorem msb_cons (b : Bool) (xs : BitVec w) : (cons b xs).msb = b := by
  rw [msb_eq_testBit, toNat_cons, testBit_lor, Nat.shiftLeft_eq, mul_comm]
  refine Eq.trans (congrArg₂ _ ?_ ?_) (Bool.or_false _)
  . cases b
    . exact zero_testBit w
    . refine Eq.trans (congrArg₂ _ (Nat.zero_add _) rfl) ?_
      exact Nat.testBit_two_pow_self w
  . exact Nat.testBit_eq_false_of_lt (toNat_lt xs)

@[simp]
theorem getLsb_lt_cons (b : Bool) (xs : BitVec w) (i : ℕ) (h : i < w) :
    getLsb (cons b xs) i = getLsb xs i := by
  rw [getLsb_eq_testBit, toNat_cons, testBit_lor, Nat.shiftLeft_eq, mul_comm]
  refine Eq.trans (congrArg₂ _ ?_ getLsb_eq_testBit.symm) (Bool.false_or _)
  cases b
  . exact zero_testBit i
  . refine Eq.trans (congrArg₂ _ (Nat.zero_add _) rfl) ?_
    exact Nat.testBit_two_pow_of_ne (Nat.ne_of_gt h)

@[simp]
theorem getMsb_cons (b : Bool) (xs : BitVec w) (i : ℕ) :
    getMsb (cons b xs) i = if i = 0 then b else getMsb xs i.pred := by
  split_ifs with h
  . subst i; exact msb_cons b xs
  . by_cases h' : w = 0
    . subst w
      simp [getMsb_eq_testBit, h]
    . rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at h
      refine congrArg₂ _ (Bool.decide_congr $ Iff.symm $ tsub_lt_iff_right h) ?_
      have : getLsb (cons b xs) (w - i) = getLsb xs (w - i)
      . apply getLsb_lt_cons
        exact Nat.sub_lt (Nat.pos_of_ne_zero h') h
      refine Eq.trans this $ congrArg _ $ (tsub_tsub_tsub_cancel_right h).symm

lemma getMsb_truncate_of_lt_of_le (xs : BitVec w) {i : ℕ} (h₁ : i < v)
    (h₂ : v ≤ w) : getMsb (truncate v xs) i = getMsb xs (i + (w - v)) := by
  have h₃ := lt_of_lt_of_eq (add_lt_add_right h₁ _) (add_sub_of_le h₂)
  simp only [getMsb_eq_testBit, toNat_truncate, toNat_allOnes, testBit_land,
             Nat.testBit_two_pow_sub_one, Bool.true_and, Bool.and_true,
             decide_eq_true (Nat.sub_lt_self (Nat.zero_lt_succ i) h₁),
             decide_eq_true h₁, decide_eq_true h₃]
  rw [← Nat.succ_add, Nat.add_comm, ← Nat.sub_sub, Nat.sub_sub_self h₂]

lemma getMsb_truncate_succ_lt (xs : BitVec (w+1)) {i : ℕ} (h : i < w)
    : getMsb (truncate w xs) i = getMsb xs (i + 1) :=
  congrArg (i + .) (Eq.trans (Nat.succ_sub (le_refl w))
                             (congrArg succ (Nat.sub_self w)))
  ▸ getMsb_truncate_of_lt_of_le xs h (Nat.le_succ w)

@[ext]
lemma extMsb {w} {xs ys : BitVec w} (h : ∀ i < w, xs.getMsb i = ys.getMsb i) :
    xs = ys := by
  induction' ys using consRecOn with w' b ys ih
  . apply Std.BitVec.eq_nil
  . refine Eq.trans (Eq.symm $ cons_msb_truncate xs) (congrArg₂ cons ?_ ?_)
    . exact Eq.trans (h 0 (Nat.zero_lt_succ w')) (msb_cons b ys)
    . apply ih
      intro i hi
      specialize h (i+1) (Nat.succ_lt_succ hi)
      rw [getMsb_truncate_succ_lt xs hi]
      refine Eq.trans h ?_
      simp only [getMsb_cons, Nat.pred_succ, ite_false, Nat.succ_ne_zero]

@[simp]
lemma truncate_cons (b : Bool) (v : BitVec w) : truncate w (cons b v) = v := by
  ext
  rw [getMsb_truncate_succ_lt, getMsb_cons]
  . simp only [add_eq_zero, one_ne_zero, and_false, Nat.pred_succ, ite_false]
  . assumption

@[simp] lemma consRecOn_nil {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs)) :
    consRecOn nil cons BitVec.nil = nil := rfl

@[simp] lemma consRecOn_cons {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs))
    (b : Bool) (v : BitVec w) :
    consRecOn nil cons (v.cons b) = cons b v (consRecOn nil cons v) :=
  cast_eq_iff_heq.mpr $ by
    congr
    . apply msb_cons
    all_goals apply truncate_cons

end Std.BitVec
