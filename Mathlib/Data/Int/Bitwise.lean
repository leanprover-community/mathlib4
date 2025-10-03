/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Batteries.Data.Int

/-!
# Bitwise operations on integers

Possibly only of archaeological significance.

## Recursors
* `Int.bitCasesOn`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.
-/

namespace Int

/-- `div2 n = n/2` -/
def div2 : ℤ → ℤ
  | (n : ℕ) => n.div2
  | -[n +1] => negSucc n.div2

/-- `bodd n` returns `true` if `n` is odd -/
def bodd : ℤ → Bool
  | (n : ℕ) => n.bodd
  | -[n +1] => not (n.bodd)

/-- `bit b` appends the digit `b` to the binary representation of
  its integer input. -/
def bit (b : Bool) : ℤ → ℤ :=
  cond b (2 * · + 1) (2 * ·)

/-- `Int.natBitwise` is an auxiliary definition for `Int.bitwise`. -/
def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[ Nat.bitwise (fun x y => not (f x y)) m n +1] (Nat.bitwise f m n)

/-- `Int.bitwise` applies the function `f` to pairs of bits in the same position in
  the binary representations of its inputs. -/
def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n +1] => natBitwise (fun x y => f x (not y)) m n
  | -[m +1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m +1], -[n +1] => natBitwise (fun x y => f (not x) (not y)) m n

/-- `lnot` flips all the bits in the binary representation of its input -/
def lnot : ℤ → ℤ
  | (m : ℕ) => -[m +1]
  | -[m +1] => m

/-- `lor` takes two integers and returns their bitwise `or` -/
def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m ||| n
  | (m : ℕ), -[n +1] => -[Nat.ldiff n m +1]
  | -[m +1], (n : ℕ) => -[Nat.ldiff m n +1]
  | -[m +1], -[n +1] => -[m &&& n +1]

/-- `land` takes two integers and returns their bitwise `and` -/
def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m &&& n
  | (m : ℕ), -[n +1] => Nat.ldiff m n
  | -[m +1], (n : ℕ) => Nat.ldiff n m
  | -[m +1], -[n +1] => -[m ||| n +1]

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as Booleans, say `aᵢ` and `bᵢ`, it applies the
  Boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[n +1] => m &&& n
  | -[m +1], (n : ℕ) => -[m ||| n +1]
  | -[m +1], -[n +1] => Nat.ldiff n m

/-- `xor` computes the bitwise `xor` of two natural numbers -/
protected def xor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => (m ^^^ n)
  | (m : ℕ), -[n +1] => -[(m ^^^ n) +1]
  | -[m +1], (n : ℕ) => -[(m ^^^ n) +1]
  | -[m +1], -[n +1] => (m ^^^ n)

/-- `m <<< n` produces an integer whose binary representation
  is obtained by left-shifting the binary representation of `m` by `n` places -/
instance : ShiftLeft ℤ where
  shiftLeft
  | (m : ℕ), (n : ℕ) => Nat.shiftLeft' false m n
  | (m : ℕ), -[n +1] => m >>> (Nat.succ n)
  | -[m +1], (n : ℕ) => -[Nat.shiftLeft' true m n +1]
  | -[m +1], -[n +1] => -[m >>> (Nat.succ n) +1]

/-- `m >>> n` produces an integer whose binary representation
  is obtained by right-shifting the binary representation of `m` by `n` places -/
instance : ShiftRight ℤ where
  shiftRight m n := m <<< (-n)

/-! ### bitwise ops -/

@[simp]
theorem bodd_zero : bodd 0 = false :=
  rfl

@[simp]
theorem bodd_one : bodd 1 = true :=
  rfl

theorem bodd_two : bodd 2 = false :=
  rfl

@[simp, norm_cast]
theorem bodd_coe (n : ℕ) : Int.bodd n = Nat.bodd n :=
  rfl

@[simp]
theorem bodd_subNatNat (m n : ℕ) : bodd (subNatNat m n) = xor m.bodd n.bodd := by
  apply subNatNat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;>
  intro i j <;>
  simp only [Int.bodd, Nat.bodd_add] <;>
  cases Nat.bodd i <;> simp

@[simp]
theorem bodd_negOfNat (n : ℕ) : bodd (negOfNat n) = n.bodd := by
  cases n <;> simp +decide
  rfl

@[simp]
theorem bodd_neg (n : ℤ) : bodd (-n) = bodd n := by
  cases n <;> simp only [← negOfNat_eq, bodd_negOfNat, neg_negSucc] <;> simp [bodd]

@[simp]
theorem bodd_add (m n : ℤ) : bodd (m + n) = xor (bodd m) (bodd n) := by
  rcases m with m | m <;>
  rcases n with n | n <;>
  simp only [ofNat_eq_coe, ofNat_add_negSucc, negSucc_add_ofNat,
             negSucc_add_negSucc, bodd_subNatNat, ← Nat.cast_add] <;>
  simp [bodd, Bool.xor_comm]

@[simp]
theorem bodd_mul (m n : ℤ) : bodd (m * n) = (bodd m && bodd n) := by
  rcases m with m | m <;> rcases n with n | n <;>
  simp only [ofNat_eq_coe, ofNat_mul_negSucc, negSucc_mul_ofNat, ofNat_mul_ofNat,
             negSucc_mul_negSucc] <;>
  simp only [negSucc_eq, ← Int.natCast_succ, bodd_neg, bodd_coe, Nat.bodd_mul]

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : ℕ) => by
    rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ) by cases bodd n <;> rfl]
    exact congr_arg ofNat n.bodd_add_div2
  | -[n+1] => by
    refine Eq.trans ?_ (congr_arg negSucc n.bodd_add_div2)
    dsimp [bodd]; cases Nat.bodd n <;> dsimp [cond, not, div2, Int.mul]
    · change -[2 * Nat.div2 n+1] = _
      rw [zero_add]
    · rw [zero_add, add_comm]
      rfl

theorem div2_val : ∀ n, div2 n = n / 2
  | (n : ℕ) => congr_arg ofNat n.div2_val
  | -[n+1] => congr_arg negSucc n.div2_val

theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  · apply (add_zero _).symm
  · rfl

theorem bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (add_comm _ _).trans <| bodd_add_div2 _

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def bitCasesOn.{u} {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n]
  apply h

@[simp]
theorem bit_zero : bit false 0 = 0 :=
  rfl

@[simp]
theorem bit_coe_nat (b) (n : ℕ) : bit b n = Nat.bit b n := by
  rw [bit_val, Nat.bit_val]
  cases b <;> rfl

@[simp]
theorem bit_negSucc (b) (n : ℕ) : bit b -[n+1] = -[Nat.bit (not b) n+1] := by
  rw [bit_val, Nat.bit_val]
  cases b <;> rfl

@[simp]
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  cases b <;> cases bodd n <;> simp [(show bodd 2 = false by rfl)]

@[simp]
theorem testBit_bit_zero (b) : ∀ n, testBit (bit b n) 0 = b
  | (n : ℕ) => by rw [bit_coe_nat]; apply Nat.testBit_bit_zero
  | -[n+1] => by
    rw [bit_negSucc]; dsimp [testBit]; rw [Nat.testBit_bit_zero]; clear testBit_bit_zero
    cases b <;>
      rfl

@[simp]
theorem testBit_bit_succ (m b) : ∀ n, testBit (bit b n) (Nat.succ m) = testBit n m
  | (n : ℕ) => by rw [bit_coe_nat]; apply Nat.testBit_bit_succ
  | -[n+1] => by
    dsimp only [testBit]
    simp only [bit_negSucc]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Nat.testBit_bit_succ]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO
-- private unsafe def bitwise_tac : tactic Unit :=
--   sorry

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_or : bitwise or = lor := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.or_true, cond_true, lor, Nat.ldiff,
      negSucc.injEq, Bool.true_or]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · simp
  · congr
    simp

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_and : bitwise and = land := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Bool.and_true,
      Bool.and_false]
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl
  · congr
    simp

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_diff : (bitwise fun a b => a && not b) = ldiff := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false,
      cond_false, cond_true, Nat.ldiff, Bool.and_true, negSucc.injEq,
      Bool.and_false, Bool.not_true, ldiff]
  · congr
    simp
  · congr
    simp
  · rw [Nat.bitwise_swap, Function.swap]
    congr
    funext x y
    cases x <;> cases y <;> rfl

-- Porting note: Was `bitwise_tac` in mathlib
theorem bitwise_xor : bitwise xor = Int.xor := by
  funext m n
  rcases m with m | m <;> rcases n with n | n <;> try {rfl}
    <;> simp only [bitwise, natBitwise, Bool.not_false, Bool.bne_eq_xor,
      cond_false, cond_true, negSucc.injEq, Bool.false_xor,
      Bool.true_xor, Bool.not_true,
      Int.xor, HXor.hXor, XorOp.xor, Nat.xor] <;> simp

@[simp]
theorem bitwise_bit (f : Bool → Bool → Bool) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  rcases m with m | m <;> rcases n with n | n <;>
  simp [bitwise, ofNat_eq_coe, bit_coe_nat, natBitwise, Bool.not_false,
    bit_negSucc]
  · by_cases h : f false false <;> simp +decide [h]
  · by_cases h : f false true <;> simp +decide [h]
  · by_cases h : f true false <;> simp +decide [h]
  · by_cases h : f true true <;> simp +decide [h]

@[simp]
theorem lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := by
  rw [← bitwise_or, bitwise_bit]

@[simp]
theorem land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) := by
  rw [← bitwise_and, bitwise_bit]

@[simp]
theorem ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) := by
  rw [← bitwise_diff, bitwise_bit]

@[simp]
theorem lxor_bit (a m b n) : Int.xor (bit a m) (bit b n) = bit (xor a b) (Int.xor m n) := by
  rw [← bitwise_xor, bitwise_bit]

@[simp]
theorem lnot_bit (b) : ∀ n, lnot (bit b n) = bit (not b) (lnot n)
  | (n : ℕ) => by simp [lnot]
  | -[n+1] => by simp [lnot]

@[simp]
theorem testBit_bitwise (f : Bool → Bool → Bool) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  cases m <;> cases n <;> simp only [testBit, bitwise, natBitwise]
  · by_cases h : f false false <;> simp [h]
  · by_cases h : f false true <;> simp [h]
  · by_cases h : f true false <;> simp [h]
  · by_cases h : f true true <;> simp [h]

@[simp]
theorem testBit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k) := by
  rw [← bitwise_or, testBit_bitwise]

@[simp]
theorem testBit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k) := by
  rw [← bitwise_and, testBit_bitwise]

@[simp]
theorem testBit_ldiff (m n k) : testBit (ldiff m n) k = (testBit m k && not (testBit n k)) := by
  rw [← bitwise_diff, testBit_bitwise]

@[simp]
theorem testBit_lxor (m n k) : testBit (Int.xor m n) k = xor (testBit m k) (testBit n k) := by
  rw [← bitwise_xor, testBit_bitwise]

@[simp]
theorem testBit_lnot : ∀ n k, testBit (lnot n) k = not (testBit n k)
  | (n : ℕ), k => by simp [lnot, testBit]
  | -[n+1], k => by simp [lnot, testBit]

@[simp]
theorem shiftLeft_neg (m n : ℤ) : m <<< (-n) = m >>> n :=
  rfl

@[simp]
theorem shiftRight_neg (m n : ℤ) : m >>> (-n) = m <<< n := by rw [← shiftLeft_neg, neg_neg]

@[simp]
theorem shiftLeft_natCast (m n : ℕ) : (m : ℤ) <<< (n : ℤ) = ↑(m <<< n) := by
  unfold_projs; simp

@[simp]
theorem shiftRight_natCast (m n : ℕ) : (m : ℤ) >>> (n : ℤ) = m >>> n := by cases n <;> rfl

@[simp]
theorem shiftLeft_negSucc (m n : ℕ) : -[m+1] <<< (n : ℤ) = -[Nat.shiftLeft' true m n+1] :=
  rfl

@[simp]
theorem shiftRight_negSucc (m n : ℕ) : -[m+1] >>> (n : ℤ) = -[m >>> n+1] := by cases n <;> rfl

/-- Compare with `Int.shiftRight_add`, which doesn't have the coercions `ℕ → ℤ`. -/
theorem shiftRight_add' : ∀ (m : ℤ) (n k : ℕ), m >>> (n + k : ℤ) = (m >>> (n : ℤ)) >>> (k : ℤ)
  | (m : ℕ), n, k => by
    rw [shiftRight_natCast, shiftRight_natCast, ← Int.natCast_add, shiftRight_natCast,
      Nat.shiftRight_add]
  | -[m+1], n, k => by
    rw [shiftRight_negSucc, shiftRight_negSucc, ← Int.natCast_add, shiftRight_negSucc,
      Nat.shiftRight_add]

/-! ### bitwise ops -/

theorem shiftLeft_add' : ∀ (m : ℤ) (n : ℕ) (k : ℤ), m <<< (n + k) = (m <<< (n : ℤ)) <<< k
  | (m : ℕ), n, (k : ℕ) =>
    congr_arg ofNat (by simp [Nat.shiftLeft_eq, Nat.pow_add, mul_assoc])
  | -[_+1], _, (k : ℕ) => congr_arg negSucc (Nat.shiftLeft'_add _ _ _ _)
  | (m : ℕ), n, -[k+1] =>
    subNatNat_elim n k.succ (fun n k i => (↑m) <<< i = (Nat.shiftLeft' false m n) >>> k)
      (fun (i n : ℕ) =>
        by simp [← Nat.shiftLeft_sub _, Nat.add_sub_cancel_left])
      fun i n => by
        dsimp only [← Int.natCast_shiftRight]
        simp_rw [negSucc_eq, shiftLeft_neg, Nat.shiftLeft'_false, Nat.shiftRight_add,
          ← Nat.shiftLeft_sub _ le_rfl, Nat.sub_self, Nat.shiftLeft_zero, ← shiftRight_natCast,
          ← shiftRight_add', Nat.cast_one]
  | -[m+1], n, -[k+1] =>
    subNatNat_elim n k.succ
      (fun n k i => -[m+1] <<< i = -[(Nat.shiftLeft' true m n) >>> k+1])
      (fun i n =>
        congr_arg negSucc <| by
          rw [← Nat.shiftLeft'_sub, Nat.add_sub_cancel_left]; apply Nat.le_add_right)
      fun i n =>
      congr_arg negSucc <| by rw [add_assoc, Nat.shiftRight_add, ← Nat.shiftLeft'_sub _ _ le_rfl,
          Nat.sub_self, Nat.shiftLeft']

theorem shiftLeft_sub (m : ℤ) (n : ℕ) (k : ℤ) : m <<< (n - k) = (m <<< (n : ℤ)) >>> k :=
  shiftLeft_add' _ _ _

theorem shiftLeft_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), m <<< (n : ℤ) = m * (2 ^ n : ℕ)
  | (m : ℕ), _ => congr_arg ((↑) : ℕ → ℤ) (by simp [Nat.shiftLeft_eq])
  | -[_+1], _ => @congr_arg ℕ ℤ _ _ (fun i => -i) (Nat.shiftLeft'_tt_eq_mul_pow _ _)

theorem one_shiftLeft (n : ℕ) : 1 <<< (n : ℤ) = (2 ^ n : ℕ) :=
  congr_arg ((↑) : ℕ → ℤ) (by simp [Nat.shiftLeft_eq])

/-- Compare with `Int.zero_shiftLeft`, which has `n : ℕ`. -/
@[simp]
theorem zero_shiftLeft' : ∀ n : ℤ, 0 <<< n = 0
  | (n : ℕ) => congr_arg ((↑) : ℕ → ℤ) (by simp)
  | -[_+1] => congr_arg ((↑) : ℕ → ℤ) (by simp)

/-- Compare with `Int.zero_shiftRight`, which has `n : ℕ`. -/
@[simp]
theorem zero_shiftRight' (n : ℤ) : 0 >>> n = 0 :=
  zero_shiftLeft' _

end Int
