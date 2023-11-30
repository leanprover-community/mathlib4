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
import Mathlib.Data.List.DropRight

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors, as defined in `Std`.

Note that `Std.BitVec` is distinct from mathlibs `Bitvec` type, this file is about the former.
For the latter, go to `Data.Bitvec` (notice the difference in capitalization).
Eventually, `Std.BitVec` will replace `Bitvec`, so we include the relevant `#align`s, but
comment them out for now
-/

section ShouldBeMoved

namespace Nat

def exists_decidable_of_min_bounded {p : ℕ → Prop} [DecidablePred p] (M : ℕ)
    (h : (∃ i, p i) → (∃ i < M, p i)) : Decidable (∃ i, p i) :=
  have h' : (∃ i : Fin M, p i) ↔ (∃ i, p i) :=
    Iff.trans Fin.exists_iff
    $ Iff.trans bex_def
    $ ⟨Exists.imp (fun _ => And.right), h⟩
  decidable_of_iff _ h'

def exists_decidable_of_sat_bounded {p : ℕ → Prop} [DecidablePred p] (M : ℕ)
    (h : ∀ i, p i → i < M) : Decidable (∃ i, p i) :=
  exists_decidable_of_min_bounded M
  $ Exists.imp (Iff.mpr $ and_iff_right_of_imp $ h .)

@[simp]
lemma testBit_pred_size_eq_true {n : ℕ} :
    n ≠ 0 → testBit n (size n).pred := Decidable.or_iff_not_imp_left.mp $ by
  induction' n using Nat.binaryRecFromOne with b n h ih
  . left; rfl
  . right; rfl
  . refine Or.inr (Eq.trans ?_ (ih.resolve_left h))
    refine Eq.trans (congrArg _ ?_) (testBit_succ _ b n)
    simp only [ne_eq, Nat.pred_succ, h, false_and, not_false_eq_true, size_bit,
               bit_eq_zero, Nat.succ_pred_eq_of_ne_zero $ mt size_eq_zero.mp h]

lemma testBit_pred_size (n : ℕ) : testBit n (size n).pred = (n != 0) :=
  if h : n = 0
  then by subst h; rfl
  else Eq.trans (testBit_pred_size_eq_true h) ((bne_iff_ne n 0).mpr h).symm

lemma lt_add_iff {w v i : ℕ} : i < w + v ↔ i < w ∨ i - w < v := by
  cases' Nat.lt_or_ge i w with h h
  <;> simp only [h, Nat.not_lt_of_le, Nat.lt_add_right, false_or, true_or]
  exact (tsub_lt_iff_left h).symm

lemma add_sub_lt_self_iff {a b c : ℕ} : (a + b) - c < a ↔ 0 < a ∧ b < c :=
  Iff.trans (iff_of_eq $ congrArg₂ _ (Nat.sub_eq_sub_min _ _)
                                     (Eq.symm $ add_sub_self_right a b))
  $ Iff.trans (tsub_lt_tsub_iff_left_of_le (Nat.min_le_left (a + b) c))
  $ Iff.trans lt_min_iff $ and_congr_left' (lt_add_iff_pos_left _)

@[simp] lemma bit_div_two (b : Bool) (x : Nat) : bit b x / 2 = x := by
  rw [←div2_val, div2_bit]

@[simp (high)]
lemma bit_shiftRight_succ (b : Bool) (x n : ℕ) :
    bit b x >>> (n + 1) = x >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm, ←Nat.div_div_eq_div_mul,
    bit_div_two]

lemma shiftRight_sub (m : ℕ) {n k : ℕ} (h : k ≤ n) :
    m >>> (n - k) = (m <<< k) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  refine Eq.symm ?_
  refine Eq.trans (congrArg _ $ Eq.trans ?_ $ Nat.pow_add 2 (n - k) k) ?_
  . exact congrArg _ (Nat.sub_add_cancel h).symm
  . exact Nat.mul_div_mul_right _ _ (two_pow_pos k)

lemma bitwise_shiftLeft f (h : f false false = false := by rfl) n m w :
    bitwise f (n <<< w) (m <<< w) = bitwise f n m <<< w := by
  induction' w with w ih
  . rfl
  . simp only [shiftLeft_succ, ← bit0_eq_two_mul, ← Nat.bit_false]
    rw [bitwise_bit h, h, ih]

lemma bitwise_shiftRight f (h : f false false = false := by rfl) n m w :
    bitwise f (n >>> w) (m >>> w) = bitwise f n m >>> w := by
  revert n m; induction' w with w ih <;> intros n m
  . rfl
  . cases' n using bitCasesOn with b n; cases' m using bitCasesOn with b' m
    simp only [Nat.succ_eq_one_add, shiftRight_add]
    rw [ih, bitwise_bit h]
    simp only [shiftRight_succ, shiftRight_zero, bit_div_two]

lemma land_shiftLeft :
    ∀ (n m w : ℕ), (n <<< w) &&& (m <<< w) = (n &&& m) <<< w :=
  bitwise_shiftLeft and

lemma lor_shiftLeft :
    ∀ (n m w : ℕ), (n <<< w) ||| (m <<< w) = (n ||| m) <<< w :=
  bitwise_shiftLeft or

lemma xor_shiftLeft :
    ∀ (n m w : ℕ), (n <<< w) ^^^ (m <<< w) = (n ^^^ m) <<< w :=
  bitwise_shiftLeft bne

lemma add_shiftLeft :
    ∀ (n m w : ℕ), (n <<< w) + (m <<< w) = (n + m) <<< w :=
  by simp only [shiftLeft_eq, Nat.add_mul, implies_true]

lemma sub_shiftLeft :
    ∀ (n m w : ℕ), (n <<< w) - (m <<< w) = (n - m) <<< w :=
  by simp only [shiftLeft_eq, tsub_mul, implies_true]

lemma land_shiftRight :
    ∀ (n m w : ℕ), (n >>> w) &&& (m >>> w) = (n &&& m) >>> w :=
  bitwise_shiftRight and

lemma lor_shiftRight :
    ∀ (n m w : ℕ), (n >>> w) ||| (m >>> w) = (n ||| m) >>> w :=
  bitwise_shiftRight or

lemma xor_shiftRight :
    ∀ (n m w : ℕ), (n >>> w) ^^^ (m >>> w) = (n ^^^ m) >>> w :=
  bitwise_shiftRight bne

lemma bit_false_eq_shiftLeft_one n : bit false n = n <<< 1 :=
  by rw [bit_false, bit0_val, shiftLeft_eq, Nat.pow_one, Nat.mul_comm]

lemma bit_of_zero_eq_toNat b : bit b 0 = Bool.toNat b :=
  by rw [bit_val, Nat.mul_zero, Nat.zero_add, Bool.toNat]

lemma bit_eq_shiftLeft_add_toNat b n : bit b n = n <<< 1 + b.toNat :=
  Eq.trans (Eq.trans (congrArg _ (Eq.symm $ Nat.add_zero n)) (bit_add b n 0))
  $ congrArg₂ (. + .) (bit_false_eq_shiftLeft_one n) (bit_of_zero_eq_toNat b)

lemma bit_eq_shiftLeft_lor_toNat b n : bit b n = n <<< 1 ||| b.toNat :=
  Eq.trans (Eq.symm $ Eq.trans (lor_bit false n b 0)
                    $ congrArg₂ bit (Bool.false_or b).symm (Nat.lor_zero n))
  $ congrArg₂ (. ||| .) (bit_false_eq_shiftLeft_one n) (bit_of_zero_eq_toNat b)

lemma shiftLeft_add_eq_shiftLeft_lor :
    ∀ {w} n m, m < 2^w → n <<< w + m = n <<< w ||| m := by
  have (n : ℕ) b : n <<< 1 + Bool.toNat b = n <<< 1 ||| Bool.toNat b :=
    Eq.trans (Eq.symm $ bit_eq_shiftLeft_add_toNat b n)
             (bit_eq_shiftLeft_lor_toNat b n)
  intro w; induction' w with w ih
  . simp only [pow_zero, lt_one_iff, forall_eq, shiftLeft_zero,
                add_zero, lor_zero, implies_true]
  . intros n m h
    cases' m using Nat.bitCasesOn with b m
    conv_lhs => rw [bit_eq_shiftLeft_add_toNat, ← Nat.add_assoc]
    conv_rhs => rw [bit_eq_shiftLeft_lor_toNat, ← Nat.lor_assoc]
    rw [Nat.succ_eq_add_one, Nat.shiftLeft_add, lor_shiftLeft,
        add_shiftLeft, ih _ _ (bit_lt_two_pow_succ_iff.mp h), this]

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

theorem mod_two_pow (x n : Nat) :
    x % (2^n) = x &&& 2^n - 1 := by
  induction' n with n ih generalizing x
  · simp only [Nat.zero_eq, _root_.pow_zero, mod_one, le_refl, tsub_eq_zero_of_le, land_zero]
  · cases' x using Nat.binaryRec with x₀ x _xih
    · rfl
    · simp [Nat.two_pow_succ_sub_one_eq_bit, -bit_true, ih]

theorem mod_two_eq_land (x : Nat) : x % 2 = x &&& 1 := mod_two_pow x 1

lemma bit_land_one_eq_toNat b n : bit b n &&& 1 = b.toNat :=
  Eq.trans (land_bit b n true 0)
  $ Eq.trans (congrArg₂ _ (Bool.and_true b) (Nat.land_zero n))
  $ bit_of_zero_eq_toNat b

-- reverse the bits of n, then pad with 0 lsbs up to length w
-- def reversePadded : ℕ → ℕ → ℕ := fun n w => go n w 0
--   where go (n w acc : ℕ) : ℕ :=
--     if n = 0
--     then acc <<< w
--     else if n &&& 1 = 1
--          then go (n / 2) (w - 1) ((acc <<< 1) ||| 1)
--          else go (n / 2) (w - 1) (acc <<< 1)
-- decreasing_by apply bitwise_rec_lemma; assumption

-- def reverse := fun n => go n 0
--   where go n acc :=
--     if n = 0
--     then acc
--     else go (n / 2) (bif n &&& 1 == 1 then (acc <<< 1) ||| 1 else acc <<< 1)
-- decreasing_by apply bitwise_rec_lemma; assumption

-- def reversePadded' (n w : ℕ) := if h : n = 0 then 0 else go n h w 0 where
--   H m (h1 : m % 2 = 0) (h2 : m / 2 = 0) : m = 0 :=
--     Eq.trans (Eq.symm $ Nat.div_add_mod m 2)
--     $ congrArg₂ _ (Eq.trans (congrArg _ h2) (Nat.mul_zero 2)) h1
--   go m (h : m ≠ 0) (curr acc : ℕ) : ℕ :=
--     if h' : m &&& 1 = 1
--     then reverse.go m acc <<< curr
--     else go (m / 2) (mt (H m $ Or.resolve_right (Nat.mod_two_eq_zero_or_one _)
--                              $ ne_of_eq_of_ne (mod_two_eq_land m) h') h)
--             (curr - 1) (acc <<< 1)
-- decreasing_by apply bitwise_rec_lemma; assumption

-- def prefixZeroesLen (n : ℕ) : ℕ := go n 0
--   where go (m acc : ℕ) :=
--     if m = 0 then 0 else
--     bif (m &&& 1 == 1) then acc else go (m / 2) (acc + 1)
-- decreasing_by apply bitwise_rec_lemma; assumption

-- lemma prefixZeroesLen_spec n :
--     prefixZeroesLen n = ((Nat.bits n).takeWhile (. == false)).length := by
--   dsimp only [prefixZeroesLen]; refine Eq.trans ?_ (Nat.add_zero _)
--   generalize 0 = acc; revert acc
--   induction' n using Nat.binaryRec' with b n h ih <;> intro acc
--   . rfl
--   . rw [prefixZeroesLen.go, bit_div_two, ih]
--     rw [← Decidable.not_and_not_right, Bool.not_eq_true, ← bit_eq_zero] at h
--     simp only [h, ite_false, bit_land_one_eq_toNat, Bool.toNat_beq_one]
--     cases b <;> dsimp only [cond]
--     .
--       admit
--     . admit
--     -- rw [Nat.bits_append_bit _ _ h, List.takeWhile_cons]; cases b
--     -- . refine Eq.trans ?_ (Eq.symm $ List.length_cons _ _)
--     --   rw [prefixZeroesLen]
--     --   admit
--     -- . admit

--     -- cases b <;> dsimp only [(. == .), instDecidableEqBool, Bool.decEq, decide]
--     -- .
--     --   admit
--     -- .
--     --   admit


--     -- cases b <;> simp [List.takeWhile_cons]
--     -- admit

-- lemma reversePadded_eq_reverse_then_pad :
--     ∀ n w, reversePadded n w = reverse n <<< (w - zeroPrefix n) :=
--   sorry

-- lemma reversePadded_eq_reverse_then_pad :
--     ∀ n w, reversePadded n w = reverse n <<< (w - size n) := by
--   have H1 n w acc :
--     reversePadded.go n w acc
--     = if n = 0 then acc <<< w
--       else reversePadded.go (n / 2) (w - 1) (bit (n &&& 1 == 1) acc)
--   . rw [bit_eq_shiftLeft_lor_toNat]
--     conv_lhs => rw [reversePadded.go, ← Nat.lor_zero (_ <<< 1), lor_assoc, Nat.zero_lor]
--     repeat (rw [← apply_ite]; congr)
--     simp_rw [← beq_iff_eq (n &&& 1) 1, ← Bool.cond_eq_ite]
--     rfl
--   have H2 n acc :
--     reverse.go n acc
--     = if n = 0 then acc else reverse.go (n / 2) (bit (n &&& 1 == 1) acc)
--   . cases' n using bitCasesOn with b n
--     split_ifs with h <;> rw [reverse.go]
--     . rw [h, binaryRec_zero, id_eq]
--     . rw [bit_eq_zero, ← Bool.not_eq_true, Decidable.not_and_not_right] at h
--       rw [binaryRec_eq' _ _ (Or.inr h), bit_div_two, bit_land_one_eq_toNat, Bool.toNat_beq_one]
--   dsimp only [reversePadded, reverse]; generalize 0 = acc
--   revert acc; rw [forall_comm]; apply binaryRec'
--   . intros; simp (config:={singlePass:=true}) only [H1, H2]; rfl
--   . intros _ _ h ih _ _; simp (config:={singlePass:=true}) only [H1, H2]
--     rw [← Decidable.not_and_not_right, Bool.not_eq_true, ← bit_eq_zero] at h
--     simp only [h, ite_false]
--     rw [size_bit h, bit_div_two, Nat.succ_eq_one_add, ← Nat.sub_sub]
--     apply ih

-- lemma reversePadded_size n w (h1 : n ≠ 0) (h : size n ≤ w) :
--     size (reversePadded n w) = w := by

--   rw [reversePadded_eq_reverse_then_pad, size_shiftLeft]

--   admit

-- lemma reversePadded_spec (n w i : ℕ) (h : i < w) :
--     testBit (reversePadded n w) i = testBit ()


end Nat

namespace Std.BitVec

/-- Return least-significant bit in bitvector. -/
@[inline] protected def lsb {w : ℕ} (xs : BitVec w) : Bool := getLsb xs 0

end Std.BitVec

end ShouldBeMoved

/-!
## Nat lemmas
-/
namespace Nat

open Nat

@[simp]
lemma testBit_two_pow_sub_one {w i} : testBit (2^w - 1) i = (i < w : Bool) := by
  revert i; induction' w with w ih <;> intro i
  . simp only [Nat.not_lt_zero, decide_False]
    exact zero_testBit i
  . rw [two_pow_succ_sub_one_eq_bit]
    cases i
    . simp only [Nat.zero_lt_succ, decide_True]
      exact Nat.testBit_zero true _
    . simp only [ih, Nat.testBit_succ]
      exact Eq.symm (Bool.decide_congr Nat.succ_lt_succ_iff)

@[simp]
lemma testBit_shiftLeft (k w i : ℕ) :
    testBit (k <<< w) i = (i ≥ w && testBit k (i - w)) := by
  revert k i; induction' w with w ih <;> intros k i
  <;> simp only [zero_eq, shiftLeft_zero, shiftLeft_succ, Bool.true_and,
                 decide_True, zero_le i, Nat.sub_zero, ← bit0_val, ← bit_false]
  cases i
  . simp only [testBit_zero, zero_sub, zero_eq, ge_iff_le, le_zero,
                decide_False, Bool.false_and]
  . simp only [testBit_succ, ih, succ_le_succ_iff, Nat.succ_sub_succ]

@[simp]
lemma testBit_shiftRight (k w i : ℕ) :
    testBit (k >>> w) i = testBit k (i + w) := by
  revert k i; induction' w with w ih <;> intros k i
  . simp
  . cases' k using bitCasesOn with b k
    rw [add_succ, testBit_succ]
    exact Eq.trans (congrArg₂ _ (bit_shiftRight_succ _ _ _) rfl) (ih k i)

end Nat

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

lemma ofBool_eq_cond (b : Bool) : ofBool b = bif b then 1 else 0 := by
  cases b <;> rfl

@[simp] lemma toNat_ofBool (b : Bool) : BitVec.toNat (ofBool b) = b.toNat := by
  cases b <;> rfl

@[simp] lemma toNat_append (msbs : BitVec w) (lsbs : BitVec v) :
    (msbs ++ lsbs).toNat = msbs.toNat <<< v ||| lsbs.toNat := by
  refine toNat_ofNat  $ bitwise_lt ?_ $ lt_of_lt_of_le (toNat_lt lsbs)
                      $ pow_le_pow one_le_two $ le_add_left v w
  rw [Nat.pow_add, Nat.shiftLeft_eq]
  exact (mul_lt_mul_right (Nat.two_pow_pos v)).mpr (toNat_lt msbs)

@[simp] lemma toNat_cons (b : Bool) (v : BitVec w) :
    (cons b v).toNat = b.toNat <<< w ||| v.toNat :=
  Eq.trans  (toNat_append (ofBool b) v)
            $ congrArg (. <<< w ||| BitVec.toNat v) $ by cases b <;> rfl

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

@[simp] lemma toNat_zeroExtend (xs : BitVec w) :
    (zeroExtend v xs).toNat = xs.toNat &&& (BitVec.allOnes v).toNat :=
  Eq.trans (Nat.mod_two_pow _ _) (congrArg _ (Eq.symm $ toNat_allOnes _))

@[simp] lemma toNat_truncate (xs : BitVec w) :
    (truncate v xs).toNat = xs.toNat &&& (BitVec.allOnes v).toNat :=
  toNat_zeroExtend xs

@[simp] lemma toNat_nil : BitVec.toNat nil = 0 := rfl

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
## Nil
-/
@[simp]
lemma append_nil (xs : BitVec w) : xs ++ nil = xs :=
  Eq.trans (congrArg (BitVec.ofNat w) (Nat.lor_zero _)) (ofNat_toNat xs)

@[simp]
lemma nil_append (xs : BitVec w) : nil ++ xs = cast (Nat.zero_add w).symm xs :=
  Eq.trans (congrArg (.#_) $ Eq.trans (congrArg (.|||_) $ zero_shiftLeft _) $ zero_lor _)
           $ ofNat_toNat' xs $ Eq.symm $ Nat.zero_add w

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

theorem lsb_eq_testBit {x : BitVec w} : x.lsb = x.toNat.testBit 0 :=
  getLsb_eq_testBit

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

@[simp]
lemma getLsb_cast (h : v = w) xs i : getLsb (cast h xs) i = getLsb xs i := rfl

@[simp]
lemma lsb_cast (h : v = w) xs : (cast h xs).lsb = xs.lsb := getLsb_cast h xs 0

@[simp]
lemma getMsb_cast (h : v = w) xs i : getMsb (cast h xs) i = getMsb xs i := by
  refine Eq.trans (Eq.symm ?_) (congrArg₂ (.&&.) rfl (getLsb_cast h xs _))
  exact congrArg₂ (.&&.)  (Bool.decide_congr $ iff_of_eq (congrArg _ h))
                          (congrArg (getLsb _ $ . - _ - _) h)

@[simp]
lemma msb_cast (h : v = w) xs : (cast h xs).msb = xs.msb := getMsb_cast h xs 0

lemma getLsb_only_if_bounded {i} {xs : BitVec w} : getLsb xs i → i < w :=
  suffices h : w ≤ i → getLsb xs i = false
  from Nat.not_le.mp ∘ mt h ∘ (Bool.not_eq_false _).mpr
  Eq.trans getLsb_eq_testBit
  ∘ Nat.testBit_eq_false_of_lt
  ∘ lt_of_lt_of_le xs.toNat_lt
  ∘ pow_le_pow one_le_two

lemma getMsb_only_if_bounded {i} {xs : BitVec w} : getMsb xs i → i < w :=
  of_decide_eq_true ∘ And.left ∘ (Bool.and_eq_true_iff _ _).mp

lemma getLsb_intro_bound i (xs : BitVec w) :
    getLsb xs i = (decide (i < w) && getLsb xs i) :=
  Eq.symm $ Bool.eq_iff_iff.mpr
  $ Iff.trans (Bool.and_eq_true_iff _ _)
  $ and_iff_right_of_imp $ decide_eq_true ∘ getLsb_only_if_bounded

lemma getMsb_intro_bound i (xs : BitVec w) :
    getMsb xs i = (decide (i < w) && getMsb xs i) :=
  Eq.symm $ Eq.trans (Eq.symm $ Bool.and_assoc _ _ _)
                     (congrArg₂ _ (Bool.and_self _) rfl)

@[simp] lemma getLsb_nil {i} : getLsb nil i = false := rfl
@[simp] lemma getMsb_nil {i} : getMsb nil i = false := rfl

@[simp]
lemma getLsb_append {xs : BitVec w} {ys : BitVec v} {i} :
    getLsb (xs ++ ys) i = (getLsb ys i || ((v ≤ i) && getLsb xs (i - v))) := by
  simp only [getLsb_eq_testBit, toNat_append, testBit_lor]
  rw [testBit_shiftLeft]
  simp_rw [← getLsb_eq_testBit]
  exact Bool.or_comm _ _

@[simp]
lemma getMsb_append {xs : BitVec w} {ys : BitVec v} {i} :
    getMsb (xs ++ ys) i = (getMsb xs i || (i ≥ w && getMsb ys (i - w))) := by
  rw [getMsb, getLsb_append, Bool.and_or_distrib_left, Bool.or_comm,
      ← Bool.and_assoc, ← Bool.decide_and, Nat.sub_right_comm _ i v,
      Nat.sub_right_comm _ 1 v, Nat.add_sub_cancel, getMsb, getMsb, Bool.eq_iff_iff]
  simp only [Bool.decide_and, Bool.or_eq_true, Bool.and_eq_true,
             decide_eq_true_eq, lt_add_iff]
  rw [Nat.add_comm w v, Nat.sub_sub, Nat.add_comm 1 i]
  conv => left; right; rw [getLsb_intro_bound]
  rw [Bool.and_eq_true, decide_eq_true_eq, ← not_lt, add_sub_lt_self_iff]
  refine or_congr ?_ ?_
  . rw [or_and_right, not_and, not_lt, add_one_le_iff,
        and_iff_left_of_imp (fun h _ => h),
        and_congr_right (forall_prop_of_true ∘ zero_lt_of_lt),
        or_iff_left_of_imp And.right]
  . rw [← and_assoc, ← and_assoc, ← and_assoc]
    refine Iff.trans (and_congr_left' ?_) (and_congr_right ?_)
    . rw [and_right_comm, or_and_right, lt_add_one_iff, or_iff_right]
      . rw [and_comm, and_left_comm, ← and_comm, and_congr_left_iff,
            and_iff_right_iff_imp, imp.swap]
        intro; exact zero_lt_of_lt
      . rw [← not_lt]
        exact and_not_self
    . rintro ⟨h1, h2⟩
      rw [← Bool.eq_iff_iff, ← Nat.sub_sub, Nat.sub_right_comm v]
      refine congrArg (getLsb _ $ . - 1) ?_
      refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
      refine Eq.trans (Eq.symm ?_) (Nat.add_sub_assoc h1 _)
      refine Eq.trans ?_ (Nat.add_sub_cancel v w)
      refine congrArg₂ _ (Nat.sub_add_cancel ?_) rfl
      exact Nat.le_add_of_sub_le (le_of_lt h2)

/-!
## Cons
-/

theorem getLsb_cons_lt_length (b : Bool) (xs : BitVec w) {i : ℕ} (h : i < w) :
    getLsb (cons b xs) i = getLsb xs i := by
  refine Eq.trans getLsb_append (Eq.trans (congrArg₂ _ rfl ?_) (Bool.or_false _))
  refine (Bool.and_eq_false_eq_eq_false_or_eq_false _ _).mpr ?_
  exact Or.inl (decide_eq_false (Nat.not_le.mpr h))

theorem getMsb_cons_succ (b : Bool) (xs : BitVec w) {i : ℕ} :
    getMsb (cons b xs) (i + 1) = getMsb xs i := by
  refine Eq.trans (getMsb_cast _ _ _) (Eq.trans getMsb_append ?_)
  rw [decide_eq_true (Nat.le_add_left 1 i), Bool.true_and]
  refine Eq.trans (congrArg₂ _ ?_ rfl) (Bool.false_or _)
  rw [Bool.eq_false_iff]
  exact mt (Nat.lt_of_succ_lt_succ ∘ getMsb_only_if_bounded) (not_lt_zero i)

@[simp] theorem msb_cons (b : Bool) (xs : BitVec w) : (cons b xs).msb = b := by
  rw [msb_eq_testBit, toNat_cons, testBit_lor, Nat.shiftLeft_eq, mul_comm]
  refine Eq.trans (congrArg₂ _ ?_ ?_) (Bool.or_false _)
  . cases b
    . exact zero_testBit w
    . refine Eq.trans (congrArg₂ _ (Nat.zero_add _) rfl) ?_
      exact Nat.testBit_two_pow_self w
  . exact Nat.testBit_eq_false_of_lt (toNat_lt xs)

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
      simp only [getMsb_cons_succ, Nat.pred_succ, ite_false, Nat.succ_ne_zero]

@[simp]
lemma truncate_cons (b : Bool) (v : BitVec w) : truncate w (cons b v) = v := by
  ext
  rw [getMsb_truncate_succ_lt, getMsb_cons_succ]
  assumption

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

-- should define it on nats really...
def reverse : ∀ {w}, BitVec w → BitVec w :=
  consRecOn (motive := fun {w} _ => BitVec w) nil $ fun b _ rev => concat rev b

@[simp] lemma reverse_nil : reverse nil = nil :=
  consRecOn_nil _ _

@[simp] lemma reverse_cons b (xs : BitVec w)
    : reverse (cons b xs) = reverse xs ++ ofBool b := consRecOn_cons _ _ _ _

lemma append_assoc {w v u} (xs : BitVec w) (ys : BitVec v) (zs : BitVec u) :
    xs ++ (ys ++ zs) = cast (Nat.add_assoc _ _ _) (xs ++ ys ++ zs) :=
  by  simp only [← toNat_inj, toNat_append, toNat_cast,
                 ← lor_assoc, shiftLeft_add, lor_shiftLeft]

@[simp] lemma cons_append {b} (xs : BitVec w) (ys : BitVec v)
    : cons b xs ++ ys = cast (Nat.add_right_comm _ _ _) (cons b (xs ++ ys)) :=
  by  simp only [← toNat_inj, toNat_append, toNat_cons, toNat_cast,
                 ← lor_assoc, shiftLeft_add, lor_shiftLeft]

end Std.BitVec
