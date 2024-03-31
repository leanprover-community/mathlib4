/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Init.Data.Int.Bitwise

#align_import data.int.bitwise from "leanprover-community/mathlib"@"0743cc5d9d86bcd1bba10f480e948a257d65056f"

/-!
# Bitwise operations on integers


## Recursors
* `Int.bitCasesOn`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.
-/

namespace Int

/-! ### bitwise ops -/

@[simp]
theorem bodd_zero : bodd 0 = false :=
  rfl
#align int.bodd_zero Int.bodd_zero

@[simp]
theorem bodd_one : bodd 1 = true :=
  rfl
#align int.bodd_one Int.bodd_one

theorem bodd_two : bodd 2 = false :=
  rfl
#align int.bodd_two Int.bodd_two

@[simp, norm_cast]
theorem bodd_coe (n : ℕ) : Int.bodd n = Nat.bodd n :=
  rfl
#align int.bodd_coe Int.bodd_coe

@[simp]
theorem bodd_subNatNat (m n : ℕ) : bodd (subNatNat m n) = xor m.bodd n.bodd := by
  apply subNatNat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;>
  intros i j <;>
  simp only [Int.bodd, Int.bodd_coe, Nat.bodd_add] <;>
  cases Nat.bodd i <;> simp
#align int.bodd_sub_nat_nat Int.bodd_subNatNat

@[simp]
theorem bodd_negOfNat (n : ℕ) : bodd (negOfNat n) = n.bodd := by
  cases n <;> simp (config := {decide := true})
  rfl
#align int.bodd_neg_of_nat Int.bodd_negOfNat

@[simp]
theorem bodd_neg (n : ℤ) : bodd (-n) = bodd n := by
  cases n with
  | ofNat =>
    rw [← negOfNat_eq, bodd_negOfNat]
    simp
  | negSucc n =>
    rw [neg_negSucc, bodd_coe, Nat.bodd_succ]
    change (!Nat.bodd n) = !(bodd n)
    rw [bodd_coe]
-- Porting note: Heavily refactored proof, used to work all with `simp`:
-- `cases n <;> simp [Neg.neg, Int.coe_nat_eq, Int.neg, bodd, -of_nat_eq_coe]`
#align int.bodd_neg Int.bodd_neg

@[simp]
theorem bodd_add (m n : ℤ) : bodd (m + n) = xor (bodd m) (bodd n) := by
  cases' m with m m <;>
  cases' n with n n <;>
  simp only [ofNat_eq_coe, ofNat_add_negSucc, negSucc_add_ofNat,
             negSucc_add_negSucc, bodd_subNatNat] <;>
  simp only [negSucc_coe, bodd_neg, bodd_coe, ← Nat.bodd_add, Bool.xor_comm, ← Nat.cast_add]
  rw [← Nat.succ_add, add_assoc]
-- Porting note: Heavily refactored proof, used to work all with `simp`:
-- `by cases m with m m; cases n with n n; unfold has_add.add;`
-- `simp [int.add, -of_nat_eq_coe, bool.xor_comm]`
#align int.bodd_add Int.bodd_add

@[simp]
theorem bodd_mul (m n : ℤ) : bodd (m * n) = (bodd m && bodd n) := by
  cases' m with m m <;> cases' n with n n <;>
  simp only [ofNat_eq_coe, ofNat_mul_negSucc, negSucc_mul_ofNat, ofNat_mul_ofNat,
             negSucc_mul_negSucc] <;>
  simp only [negSucc_coe, bodd_neg, bodd_coe, ← Nat.bodd_mul]
-- Porting note: Heavily refactored proof, used to be:
-- `by cases m with m m; cases n with n n;`
-- `simp [← int.mul_def, int.mul, -of_nat_eq_coe, bool.xor_comm]`
#align int.bodd_mul Int.bodd_mul

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : ℕ) => by
    rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ) by cases bodd n <;> rfl]
    exact congr_arg ofNat n.bodd_add_div2
  | -[n+1] => by
    refine' Eq.trans _ (congr_arg negSucc n.bodd_add_div2)
    dsimp [bodd]; cases Nat.bodd n <;> dsimp [cond, not, div2, Int.mul]
    · change -[2 * Nat.div2 n+1] = _
      rw [zero_add]
    · rw [zero_add, add_comm]
      rfl
#align int.bodd_add_div2 Int.bodd_add_div2

theorem div2_val : ∀ n, div2 n = n / 2
  | (n : ℕ) => congr_arg ofNat n.div2_val
  | -[n+1] => congr_arg negSucc n.div2_val
#align int.div2_val Int.div2_val

section deprecated

set_option linter.deprecated false

@[deprecated]
theorem bit0_val (n : ℤ) : bit0 n = 2 * n :=
  (two_mul _).symm
#align int.bit0_val Int.bit0_val

@[deprecated]
theorem bit1_val (n : ℤ) : bit1 n = 2 * n + 1 :=
  congr_arg (· + (1 : ℤ)) (bit0_val _)
#align int.bit1_val Int.bit1_val

theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  apply (bit0_val n).trans (add_zero _).symm
  apply bit1_val
#align int.bit_val Int.bit_val

theorem bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (add_comm _ _).trans <| bodd_add_div2 _
#align int.bit_decomp Int.bit_decomp

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def bitCasesOn.{u} {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n]
  apply h
#align int.bit_cases_on Int.bitCasesOn

@[simp]
theorem bit_zero : bit false 0 = 0 :=
  rfl
#align int.bit_zero Int.bit_zero

@[simp]
theorem bit_coe_nat (b) (n : ℕ) : bit b n = Nat.bit b n := by
  rw [bit_val, Nat.bit_val]
  cases b <;> rfl
#align int.bit_coe_nat Int.bit_coe_nat

@[simp]
theorem bit_negSucc (b) (n : ℕ) : bit b -[n+1] = -[Nat.bit (not b) n+1] := by
  rw [bit_val, Nat.bit_val]
  cases b <;> rfl
#align int.bit_neg_succ Int.bit_negSucc

@[simp]
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  cases b <;> cases bodd n <;> simp [(show bodd 2 = false by rfl)]
#align int.bodd_bit Int.bodd_bit

@[simp, deprecated]
theorem bodd_bit0 (n : ℤ) : bodd (bit0 n) = false :=
  bodd_bit false n
#align int.bodd_bit0 Int.bodd_bit0

@[simp, deprecated]
theorem bodd_bit1 (n : ℤ) : bodd (bit1 n) = true :=
  bodd_bit true n
#align int.bodd_bit1 Int.bodd_bit1

@[deprecated]
theorem bit0_ne_bit1 (m n : ℤ) : bit0 m ≠ bit1 n :=
  mt (congr_arg bodd) <| by simp
#align int.bit0_ne_bit1 Int.bit0_ne_bit1

@[deprecated]
theorem bit1_ne_bit0 (m n : ℤ) : bit1 m ≠ bit0 n :=
  (bit0_ne_bit1 _ _).symm
#align int.bit1_ne_bit0 Int.bit1_ne_bit0

@[deprecated]
theorem bit1_ne_zero (m : ℤ) : bit1 m ≠ 0 := by simpa only [bit0_zero] using bit1_ne_bit0 m 0
#align int.bit1_ne_zero Int.bit1_ne_zero

end deprecated

@[simp]
theorem testBit_bit_zero (b) : ∀ n, testBit (bit b n) 0 = b
  | (n : ℕ) => by rw [bit_coe_nat]; apply Nat.testBit_bit_zero
  | -[n+1] => by
    rw [bit_negSucc]; dsimp [testBit]; rw [Nat.testBit_bit_zero]; clear testBit_bit_zero;
        cases b <;>
      rfl
#align int.test_bit_zero Int.testBit_bit_zero

@[simp]
theorem testBit_bit_succ (m b) : ∀ n, testBit (bit b n) (Nat.succ m) = testBit n m
  | (n : ℕ) => by rw [bit_coe_nat]; apply Nat.testBit_bit_succ
  | -[n+1] => by
    dsimp only [testBit]
    simp only [bit_negSucc]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Nat.testBit_bit_succ]
#align int.test_bit_succ Int.testBit_bit_succ

-- Porting note (#11215): TODO
-- /- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
-- private unsafe def bitwise_tac : tactic Unit :=
--   sorry
-- #align int.bitwise_tac int.bitwise_tac

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_or : bitwise or = lor := by
  funext m n
  cases' m with m m <;> cases' n with n n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true, cond_true, lor, Nat.ldiff,
      negSucc.injEq, Bool.true_or, Nat.land]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    funext x y
    cases x <;> cases y <;> rfl
#align int.bitwise_or Int.bitwise_or

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_and : bitwise and = land := by
  funext m n
  cases' m with m m <;> cases' n with n n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true,
      cond_false, cond_true, lor, Nat.ldiff, Bool.and_true, negSucc.injEq,
      Bool.and_false, Nat.land]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    funext x y
    cases x <;> cases y <;> rfl
#align int.bitwise_and Int.bitwise_and

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_diff : (bitwise fun a b => a && not b) = ldiff := by
  funext m n
  cases' m with m m <;> cases' n with n n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true,
      cond_false, cond_true, lor, Nat.ldiff, Bool.and_true, negSucc.injEq,
      Bool.and_false, Nat.land, Bool.not_true, ldiff, Nat.lor]
  · congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    funext x y
    cases x <;> cases y <;> rfl
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
#align int.bitwise_diff Int.bitwise_diff

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_xor : bitwise xor = Int.xor := by
  funext m n
  cases' m with m m <;> cases' n with n n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true, Bool.bne_eq_xor,
      cond_false, cond_true, lor, Nat.ldiff, Bool.and_true, negSucc.injEq, Bool.false_xor,
      Bool.true_xor, Bool.and_false, Nat.land, Bool.not_true, ldiff,
      HOr.hOr, OrOp.or, Nat.lor, Int.xor, HXor.hXor, Xor.xor, Nat.xor]
  · congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    funext x y
    cases x <;> cases y <;> rfl
#align int.bitwise_xor Int.bitwise_xor

@[simp]
theorem bitwise_bit (f : Bool → Bool → Bool) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  cases' m with m m <;> cases' n with n n <;>
  simp [bitwise, ofNat_eq_coe, bit_coe_nat, natBitwise, Bool.not_false, Bool.not_eq_false',
    bit_negSucc]
  · by_cases h : f false false <;> simp (config := {decide := true}) [h]
  · by_cases h : f false true <;> simp (config := {decide := true}) [h]
  · by_cases h : f true false <;> simp (config := {decide := true}) [h]
  · by_cases h : f true true <;> simp (config := {decide := true}) [h]
#align int.bitwise_bit Int.bitwise_bit

@[simp]
theorem lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := by
  rw [← bitwise_or, bitwise_bit]
#align int.lor_bit Int.lor_bit

@[simp]
theorem land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) := by
  rw [← bitwise_and, bitwise_bit]
#align int.land_bit Int.land_bit

@[simp]
theorem ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) := by
  rw [← bitwise_diff, bitwise_bit]
#align int.ldiff_bit Int.ldiff_bit

@[simp]
theorem lxor_bit (a m b n) : Int.xor (bit a m) (bit b n) = bit (xor a b) (Int.xor m n) := by
  rw [← bitwise_xor, bitwise_bit]
#align int.lxor_bit Int.lxor_bit

@[simp]
theorem lnot_bit (b) : ∀ n, lnot (bit b n) = bit (not b) (lnot n)
  | (n : ℕ) => by simp [lnot]
  | -[n+1] => by simp [lnot]
#align int.lnot_bit Int.lnot_bit

@[simp]
theorem testBit_bitwise (f : Bool → Bool → Bool) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  cases m <;> cases n <;> simp only [testBit, bitwise, natBitwise]
  · by_cases h : f false false <;> simp [h]
  · by_cases h : f false true <;> simp [h]
  · by_cases h : f true false <;> simp [h]
  · by_cases h : f true true <;> simp [h]
#align int.test_bit_bitwise Int.testBit_bitwise

@[simp]
theorem testBit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k) := by
  rw [← bitwise_or, testBit_bitwise]
#align int.test_bit_lor Int.testBit_lor

@[simp]
theorem testBit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k) := by
  rw [← bitwise_and, testBit_bitwise]
#align int.test_bit_land Int.testBit_land

@[simp]
theorem testBit_ldiff (m n k) : testBit (ldiff m n) k = (testBit m k && not (testBit n k)) := by
  rw [← bitwise_diff, testBit_bitwise]
#align int.test_bit_ldiff Int.testBit_ldiff

@[simp]
theorem testBit_lxor (m n k) : testBit (Int.xor m n) k = xor (testBit m k) (testBit n k) := by
  rw [← bitwise_xor, testBit_bitwise]
#align int.test_bit_lxor Int.testBit_lxor

@[simp]
theorem testBit_lnot : ∀ n k, testBit (lnot n) k = not (testBit n k)
  | (n : ℕ), k => by simp [lnot, testBit]
  | -[n+1], k => by simp [lnot, testBit]
#align int.test_bit_lnot Int.testBit_lnot

@[simp]
theorem shiftLeft_neg (m n : ℤ) : m <<< (-n) = m >>> n :=
  rfl
#align int.shiftl_neg Int.shiftLeft_neg

@[simp]
theorem shiftRight_neg (m n : ℤ) : m >>> (-n) = m <<< n := by rw [← shiftLeft_neg, neg_neg]
#align int.shiftr_neg Int.shiftRight_neg

-- Porting note: what's the correct new name?
@[simp]
theorem shiftLeft_coe_nat (m n : ℕ) : (m : ℤ) <<< (n : ℤ) = ↑(m <<< n) :=
  by simp [instShiftLeftInt, HShiftLeft.hShiftLeft]
#align int.shiftl_coe_nat Int.shiftLeft_coe_nat

-- Porting note: what's the correct new name?
@[simp]
theorem shiftRight_coe_nat (m n : ℕ) : (m : ℤ) >>> (n : ℤ) = m >>> n := by cases n <;> rfl
#align int.shiftr_coe_nat Int.shiftRight_coe_nat

@[simp]
theorem shiftLeft_negSucc (m n : ℕ) : -[m+1] <<< (n : ℤ) = -[Nat.shiftLeft' true m n+1] :=
  rfl
#align int.shiftl_neg_succ Int.shiftLeft_negSucc

@[simp]
theorem shiftRight_negSucc (m n : ℕ) : -[m+1] >>> (n : ℤ) = -[m >>> n+1] := by cases n <;> rfl
#align int.shiftr_neg_succ Int.shiftRight_negSucc

theorem shiftRight_add : ∀ (m : ℤ) (n k : ℕ), m >>> (n + k : ℤ) = (m >>> (n : ℤ)) >>> (k : ℤ)
  | (m : ℕ), n, k => by
    rw [shiftRight_coe_nat, shiftRight_coe_nat, ← Int.ofNat_add, shiftRight_coe_nat,
      Nat.shiftRight_add]
  | -[m+1], n, k => by
    rw [shiftRight_negSucc, shiftRight_negSucc, ← Int.ofNat_add, shiftRight_negSucc,
      Nat.shiftRight_add]
#align int.shiftr_add Int.shiftRight_add

/-! ### bitwise ops -/

attribute [local simp] Int.zero_div

theorem shiftLeft_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), m <<< (n + k) = (m <<< (n : ℤ)) <<< k
  | (m : ℕ), n, (k : ℕ) =>
    congr_arg ofNat (by simp [Nat.shiftLeft_eq, Nat.pow_add, mul_assoc])
  | -[m+1], n, (k : ℕ) => congr_arg negSucc (Nat.shiftLeft'_add _ _ _ _)
  | (m : ℕ), n, -[k+1] =>
    subNatNat_elim n k.succ (fun n k i => (↑m) <<< i = (Nat.shiftLeft' false m n) >>> k)
      (fun (i n : ℕ) =>
        by dsimp; simp [← Nat.shiftLeft_sub _ , Nat.add_sub_cancel_left])
      fun i n => by
        dsimp
        simp only [Nat.shiftLeft'_false, Nat.shiftRight_add, le_refl, ← Nat.shiftLeft_sub,
          Nat.sub_eq_zero_of_le, Nat.shiftLeft_zero]
        rfl
  | -[m+1], n, -[k+1] =>
    subNatNat_elim n k.succ
      (fun n k i => -[m+1] <<< i = -[(Nat.shiftLeft' true m n) >>> k+1])
      (fun i n =>
        congr_arg negSucc <| by
          rw [← Nat.shiftLeft'_sub, Nat.add_sub_cancel_left]; apply Nat.le_add_right)
      fun i n =>
      congr_arg negSucc <| by rw [add_assoc, Nat.shiftRight_add, ← Nat.shiftLeft'_sub, Nat.sub_self]
      <;> rfl
#align int.shiftl_add Int.shiftLeft_add

theorem shiftLeft_sub (m : ℤ) (n : ℕ) (k : ℤ) : m <<< (n - k) = (m <<< (n : ℤ)) >>> k :=
  shiftLeft_add _ _ _
#align int.shiftl_sub Int.shiftLeft_sub

theorem shiftLeft_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), m <<< (n : ℤ) = m * (2 ^ n : ℕ)
  | (m : ℕ), _ => congr_arg ((↑) : ℕ → ℤ) (by simp [Nat.shiftLeft_eq])
  | -[_+1], _ => @congr_arg ℕ ℤ _ _ (fun i => -i) (Nat.shiftLeft'_tt_eq_mul_pow _ _)
#align int.shiftl_eq_mul_pow Int.shiftLeft_eq_mul_pow

theorem shiftRight_eq_div_pow : ∀ (m : ℤ) (n : ℕ), m >>> (n : ℤ) = m / (2 ^ n : ℕ)
  | (m : ℕ), n => by rw [shiftRight_coe_nat, Nat.shiftRight_eq_div_pow _ _]; simp
  | -[m+1], n => by
    rw [shiftRight_negSucc, negSucc_ediv, Nat.shiftRight_eq_div_pow]; rfl
    exact ofNat_lt_ofNat_of_lt (Nat.pow_pos (by decide))
#align int.shiftr_eq_div_pow Int.shiftRight_eq_div_pow

theorem one_shiftLeft (n : ℕ) : 1 <<< (n : ℤ) = (2 ^ n : ℕ) :=
  congr_arg ((↑) : ℕ → ℤ) (by simp [Nat.shiftLeft_eq])
#align int.one_shiftl Int.one_shiftLeft

@[simp]
theorem zero_shiftLeft : ∀ n : ℤ, 0 <<< n = 0
  | (n : ℕ) => congr_arg ((↑) : ℕ → ℤ) (by simp)
  | -[_+1] => congr_arg ((↑) : ℕ → ℤ) (by simp)
#align int.zero_shiftl Int.zero_shiftLeft

@[simp]
theorem zero_shiftRight (n : ℤ) : 0 >>> n = 0 :=
  zero_shiftLeft _
#align int.zero_shiftr Int.zero_shiftRight

end Int
