/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Brendan Murphy
-/

import Mathlib.Data.BitVec.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors.
-/

-- this should be moved
section ShouldBeMoved

lemma eq_ite_iff' {α} {P} [Decidable P] {a b c : α} :
    a = (if P then b else c) ↔ (P → a = b) ∧ (¬P → a = c) := by
  refine Iff.trans eq_comm (Iff.trans ite_eq_iff' (Iff.and ?_ ?_))
  <;> exact Iff.imp Iff.rfl eq_comm

namespace Bool

lemma xor_eq_or_and_not_and : ∀ (b b' : Bool),
    xor b b' = and (or b b') !(and b b') :=
  by rw [forall_bool]; constructor <;> rw [forall_bool] <;> constructor <;> rfl

lemma or_eq_xor_of_and_eq_false {b b'} (h : (b && b') = false) :
    or b b' = xor b b' :=
  Eq.symm $ Eq.trans (xor_eq_or_and_not_and b b')
  $ Eq.trans (congrArg _ $ (Bool.not_eq_true' _).mpr h) (Bool.and_true _)

end Bool

namespace Nat

section NatLemmas

lemma alt_sum_eq_max_sub_of_left_le {x y} (z : ℕ) (h : x ≤ y) :
    (z - y) + (y - x) = max y z - x := by
  rw [max_def]
  split_ifs with h'
  . exact tsub_add_tsub_cancel h' h
  . refine Eq.trans ?_ (Nat.zero_add _)
    exact congrArg (. + _) $ Nat.sub_eq_zero_of_le $ Nat.le_of_not_le h'

theorem add_lt_iff_lt_sub {a b c : ℕ} : a + b < c ↔ a < c - b :=
  Iff.intro Nat.lt_sub_of_add_lt Nat.add_lt_of_lt_sub

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

lemma shiftRight_sub (m : ℕ) {n k : ℕ} (h : k ≤ n) :
    m >>> (n - k) = (m <<< k) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  refine Eq.symm ?_
  refine Eq.trans (congrArg _ $ Eq.trans ?_ $ Nat.pow_add 2 (n - k) k) ?_
  . exact congrArg _ (Nat.sub_add_cancel h).symm
  . refine Nat.mul_div_mul_right _ _ (two_pow_pos k)

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

lemma shiftRight_shiftLeft_eq (n w : ℕ) :
    (n >>> w) <<< w = Nat.ldiff n (2^w - 1) := by
  refine eq_of_testBit_eq ?_; intro
  rw [testBit_shiftLeft, testBit_shiftRight, Bool.and_comm, testBit_ldiff,
      testBit_two_pow_sub_one, Bool.eq_iff_iff, Bool.and_eq_true,
      Bool.and_eq_true, decide_eq_true_iff, not_decide_eq_true, not_lt,
      and_congr_left (iff_of_eq ∘ congrArg (testBit n . = _) ∘ add_sub_of_le)]

lemma shiftLeft_one (n : ℕ) : n <<< 1 = 2 * n := shiftLeft_succ n 0

@[simp] lemma testBit_mod_two (n i : ℕ) :
    testBit (n % 2) i = ((i == 0) && testBit n i) :=
  Eq.trans (testBit_mod_two_pow n 1 i) $ congrArg (. && _)
  $ Eq.trans (Bool.decide_congr lt_one_iff)
  $ Eq.symm (Bool.beq_eq_decide_eq _ _)

@[simp] lemma testBit_div_two (n i : ℕ) :
    testBit (n / 2) i = testBit n (i + 1) :=
  Eq.trans (congrArg (testBit . i) $ Eq.symm $ shiftRight_eq_div_pow n 1)
  $ Eq.trans (testBit_shiftRight n) (congrArg _ (Nat.add_comm _ _))

lemma testBit_eq_true_of_max_two_pow_le {n w : ℕ}
    (h1 : 2^w ≤ n) (h2 : n < 2^(w+1)) : testBit n w = true := by
  rw [← Nat.add_zero w, ← testBit_shiftRight, shiftRight_eq_div_pow n w]
  refine Eq.trans (congrArg₂ _ (?_ : _ = 1) rfl) (Nat.testBit_two_pow_self 0)
  refine eq_of_le_of_lt_succ ?_ ?_
  . rwa [Nat.one_le_div_iff (two_pow_pos w)]
  . rwa [Nat.div_lt_iff_lt_mul (two_pow_pos w), ← pow_succ']

lemma and_distrib_of_false_false_ax {f : Bool → Bool → Bool}
    (false_false_axiom : f false false = false) :
    ∀ (b₀ b₁ b₂ : Bool), (b₀ && f b₁ b₂) = f (b₀ && b₁) (b₀ && b₂)
  | false, b₁, b₂ => by simp only [Bool.false_and, false_false_axiom]
  | true,  b₁, b₂ => by simp only [Bool.true_and]

lemma bitwise_step {f : Bool → Bool → Bool}
    (false_false_axiom : f false false = false) (n m : ℕ) :
    bitwise f n m = (bitwise f (n/2) (m/2)) <<< 1 ||| bitwise f (n%2) (m%2) := by
  apply eq_of_testBit_eq; intro
  rw [Bool.eq_iff_iff]
  simp only [testBit_bitwise false_false_axiom, testBit_lor, testBit_mod_two,
             testBit_div_two, testBit_shiftLeft, decide_eq_true_iff,
             ← and_distrib_of_false_false_ax false_false_axiom,
             Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rw [ge_iff_le, succ_le, Nat.pos_iff_ne_zero, or_comm, ← ite_eq_iff,
      ← Bool.eq_iff_iff, eq_comm, ite_eq_left_iff]
  exact congrArg (fun _ => f _ _) ∘ succ_pred

end NatLemmas

section induction

variable {motive : ℕ → Sort*} (h0 : motive 0)
    (hs : ∀ n, n ≠ 0 → motive (n / 2) → motive n)

@[elab_as_elim]
def div2Rec' (n : ℕ) := if h : n = 0 then h ▸ h0 else hs n h (div2Rec' (n / 2))
decreasing_by apply bitwise_rec_lemma; assumption

@[simp] lemma div2Rec'_zero : div2Rec' h0 hs 0 = h0 := rfl

@[simp] lemma div2Rec'_ne_zero {n} (h : n ≠ 0) :
    div2Rec' h0 hs n = hs n h (div2Rec' h0 hs (n / 2)) :=
  by rw [div2Rec']; simp only [h, dite_false]

lemma div_ne_zero_of_ne_zero_and_mod_eq_zero {n m}
    (h1 : n ≠ 0) (h2 : n % m = 0) : n / m ≠ 0 :=
  left_ne_zero_of_mul $
    ne_of_eq_of_ne (Nat.div_mul_cancel $ modEq_zero_iff_dvd.mp h2) h1

lemma eq_one_of_ne_zero_and_div_two_eq_zero {n} (h1 : n ≠ 0) (h2 : n / 2 = 0) : n = 1 :=
  (le_one_iff_eq_zero_or_eq_one.mp
  $ le_of_lt_succ $ (Nat.div_eq_zero_iff Nat.two_pos).mp h2).resolve_left h1

end induction

lemma add_eq_xor_add_shiftLeft_and (n m : ℕ) :
    n + m = (n ^^^ m) + (n &&& m) <<< 1 := by
  induction' n using Nat.div2Rec' with n _ ih generalizing m
  . simp only [Nat.zero_add, zero_xor, zero_and, zero_shiftLeft, Nat.add_zero]
  . have : ∀ {a b}, a < 2 → b < 2 → a + b = (a ^^^ b) + (a &&& b) <<< 1
    . simp only [lt_succ, Nat.le_one_iff_eq_zero_or_eq_one, or_imp,
                forall_and, forall_eq_apply_imp_iff, forall_eq]
      exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    have h1 := mod_lt n two_pos; have h2 := mod_lt m two_pos
    rw [← congrArg₂ (. + .) (Nat.div_add_mod n 2) (Nat.div_add_mod m 2),
        add_add_add_comm, ← Nat.mul_add, ← shiftLeft_one,
        congrArg₂ (. <<< 1 + .) (ih (m/2)) (this h1 h2),
        ← add_shiftLeft, add_add_add_comm, add_shiftLeft]
    refine congrArg₂ (. + . <<< 1) ?_ ?_
    <;> rw [shiftLeft_eq, Nat.mul_comm, mul_add_lt_is_or, ← Nat.mul_comm, ← shiftLeft_eq]
    any_goals exact bitwise_lt_two_pow h1 h2
    all_goals exact (bitwise_step rfl _ _).symm

lemma or_eq_xor_of_and_eq_zero {n m : ℕ} (h : n &&& m = 0) :
    n ||| m = n ^^^ m := eq_of_testBit_eq $ fun i =>
  Eq.trans (testBit_lor n m i)
  $ Eq.trans (Bool.or_eq_xor_of_and_eq_false
             $ Eq.trans (testBit_and n m i).symm
             $ Eq.trans (congrArg (testBit . i) h) (zero_testBit i))
  $ Eq.symm $ testBit_xor n m i

lemma or_eq_add_of_and_eq_zero {n m : ℕ} (h : n &&& m = 0) : n ||| m = n + m := by
  rw [add_eq_xor_add_shiftLeft_and, h, zero_shiftLeft, Nat.add_zero]
  exact or_eq_xor_of_and_eq_zero h

section size

def size' n := bif n == 0 then 0 else Nat.log2 n + 1

@[simp] theorem size'_zero : size' 0 = 0 := rfl

@[simp]
theorem size'_eq_succ_size' {n} (h : n ≠ 0) : size' n = size' (n / 2) + 1 := by
  simp only [size', Bool.cond_eq_ite, beq_iff_eq, h, ite_false, ite_not,
             Nat.div_eq_zero_iff Nat.two_pos, succ.injEq, ← not_le]
  rw [log2]

@[simp] theorem size'_one : size' 1 = 1 := rfl

@[simp]
theorem size'_pow {w : ℕ} : size' (2^w) = w + 1 := by
  induction w
  . rfl
  . rw [size'_eq_succ_size', succ_inj', Nat.pow_succ, mul_div_left _ Nat.two_pos]
    . assumption
    . exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)

@[simp]
theorem size'_two_pow_sub_one {w : ℕ} : size' (2^w - 1) = w := by
  induction w
  . rfl
  . rw [size'_eq_succ_size', succ_inj', Nat.pow_succ',
        Nat.mul_sub_div 0 2 _ (mul_pos two_pos (two_pow_pos _))]
    . assumption
    . rw [ne_eq, tsub_eq_zero_iff_le, not_le, one_lt_pow_iff]
      . exact one_lt_two
      . exact succ_ne_zero _

theorem size'_le_size {m n : ℕ} (h : m ≤ n) : size' m ≤ size' n := by
  induction' n using div2Rec' with n h' ih generalizing m
  . rw [nonpos_iff_eq_zero] at h; rw [h]
  . by_cases h'' : m = 0
    . rw [h'']; exact zero_le _
    . rw [size'_eq_succ_size' h', size'_eq_succ_size' h'', succ_le_succ_iff]
      exact ih (Nat.div_le_div_right h)

theorem size'_le {m n : ℕ} : size' m ≤ n ↔ m < 2 ^ n := by
  rw [iff_iff_implies_and_implies, ← Decidable.not_imp_not, not_lt, not_le]
  exact ⟨succ_le.mp ∘ le_of_eq_of_le size'_pow.symm ∘ size'_le_size,
         (congrArg _ size'_two_pow_sub_one).mp ∘ size'_le_size ∘ le_sub_one_of_lt⟩

theorem lt_size' {m n : ℕ} : m < size' n ↔ 2 ^ m ≤ n :=
  by rw [← not_lt, Decidable.iff_not_comm, not_lt, size'_le]

theorem lt_size'_self (n : ℕ) : n < 2 ^ size' n := by rw [← size'_le]

theorem size'_pos {n : ℕ} : 0 < size' n ↔ 0 < n := by rw [lt_size']; rfl

theorem size'_eq_zero {n : ℕ} : size' n = 0 ↔ n = 0 := by
  refine Decidable.not_iff_not.mp ?_
  simp_rw [← ne_eq, ← pos_iff_ne_zero]
  exact size'_pos

lemma testBit_eq_false_of_size'_le {n i} : size' n ≤ i → testBit n i = false :=
  testBit_eq_false_of_lt ∘ size'_le.mp

lemma lt_size'_of_testBit_eq_true {n i} : testBit n i = true → i < size' n :=
  lt_size'.mpr ∘ not_lt.mp ∘ mt (testBit_eq_false_of_lt) ∘ (Bool.not_eq_false _).mpr

theorem lt_size'_iff_higher_testBit (n w : ℕ) :
    w < size' n ↔ ∃ i ≥ w, testBit n i where
  mp  := ge_two_pow_implies_high_bit_true ∘ lt_size'.mp
  mpr := fun ⟨_, h1, h2⟩ => lt_of_le_of_lt h1 $ lt_size'_of_testBit_eq_true h2

theorem size'_le_iff_testBit_imp_lt (n w : ℕ) :
    size' n ≤ w ↔ (∀ i, testBit n i → i < w) := by
  simp_rw [← not_lt, lt_size'_iff_higher_testBit, not_exists, not_and', not_le]

lemma testBit_size'_sub_one {n} (h : n ≠ 0) : testBit n (size' n - 1) := by
  refine (Bool.not_eq_false _).mp ?_
  intro h'
  obtain ⟨i, h1, h2⟩ :=
    (lt_size'_iff_higher_testBit _ _).mp
    $ sub_one_lt_of_le (size'_pos.mpr (Nat.pos_iff_ne_zero.mpr h)) (le_refl _)
  refine Bool.false_ne_true (Eq.trans h'.symm (Eq.trans (congrArg _ ?_) h2))
  refine le_antisymm h1 $ Nat.le_sub_of_add_le $ Nat.succ_le.mpr ?_
  exact lt_size'_of_testBit_eq_true h2

theorem size'_or (n m : ℕ) : size' (n ||| m) = max (size' n) (size' m) := by
  have {p q : ℕ} := (size'_le_iff_testBit_imp_lt _ _).mpr $ fun _ =>
    lt_size'_of_testBit_eq_true ∘ Eq.trans (testBit_lor p q _) ∘ Bool.or_inl
  refine eq_max this (le_of_le_of_eq this (congrArg _ (Nat.lor_comm m n))) ?_
  intro; simp only [size'_le]; exact Nat.bitwise_lt_two_pow

theorem size'_shiftRight (n w : ℕ) : size' (n >>> w) = size' n - w := by
  refine extensional_of_trichotomous_of_irrefl LT.lt ?_
  simp_rw [← add_lt_iff_lt_sub, lt_size', shiftRight_eq_div_pow,
           Nat.le_div_iff_mul_le (two_pow_pos w), Nat.pow_add, implies_true]

theorem size'_shiftLeft (n w : ℕ) :
    size' (n <<< w) = if n = 0 then 0 else size' n + w := by
  split_ifs with h
  . subst n; rw [zero_shiftLeft, size'_zero]
  . have : size' (n <<< w) - w = size' n :=
      Eq.trans (size'_shiftRight (n <<< w) w).symm
      $ by rw [← shiftRight_sub _ (le_refl w), Nat.sub_self, shiftRight_zero]
    refine Nat.eq_add_of_sub_eq (le_of_lt (Nat.lt_of_sub_pos ?_)) this
    exact lt_of_lt_of_eq (size'_pos.mpr (Nat.pos_iff_ne_zero.mpr h)) this.symm

theorem size'_shiftLeft' (n w : ℕ) :
    size' (n <<< w) = size' n + if n = 0 then 0 else w :=
  Eq.trans (size'_shiftLeft _ _) $ Eq.symm $ Eq.trans (apply_ite _ _ _ _)
    $ ite_congr rfl size'_eq_zero.mpr (fun _ => rfl)

lemma size'_shiftLeft_le (n w : ℕ) : size' (n <<< w) ≤ size' n + w :=
  have : (if n = 0 then 0 else w) + (if n = 0 then w else 0) = w :=
    Eq.trans (apply_ite₂ _ _ _ _ _ _)
    $ ite_eq_iff'.mpr ⟨fun _ => Nat.zero_add w, fun _ => Nat.add_zero w⟩
  le_of_eq_of_le (size'_shiftLeft' n w) $ Nat.add_le_add_left (le.intro this) _

lemma eq_of_testBit_eq' {n m}
    (H : ∀ i < max (size' n) (size' m), testBit n i = testBit m i) : n = m := by
  apply eq_of_testBit_eq; intro i
  by_cases h : i < max (size' n) (size' m)
  . exact H i h
  . rw [lt_max_iff, not_or, not_lt, not_lt] at h
    exact Eq.trans (testBit_eq_false_of_size'_le h.left)
                   $ Eq.symm $ testBit_eq_false_of_size'_le h.right

end size

section reverse

-- reverse the bits of n, then pad with 0 lsbs up to length w
def reverseBits (n : ℕ) := go n 0
  where go (m acc : ℕ) :=
    if m = 0 then acc
    else go (m / 2) $ bif m &&& 1 = 0 then acc <<< 1 else (acc <<< 1) ||| 1
decreasing_by apply bitwise_rec_lemma; assumption

@[simp] lemma reverseBits_zero : reverseBits 0 = 0 := rfl

def reverseBitsPadded (n w : ℕ) := go n w 0
  where go (m curr acc : ℕ) :=
    if m = 0
    then acc <<< curr
    else go (m / 2) (curr - 1)
            $ bif m &&& 1 = 0 then acc <<< 1 else (acc <<< 1) ||| 1
decreasing_by apply bitwise_rec_lemma; assumption

lemma reverseBitsPadded_eq_reverseBits_shiftLeft (n w : ℕ)
    : reverseBitsPadded n w = reverseBits n <<< (w - size' n) := by
  rw [reverseBitsPadded, reverseBits]
  generalize 0 = acc
  induction' n using div2Rec' with n h ih generalizing w acc
  . rfl
  . rw [reverseBitsPadded.go, reverseBits.go]
    simp only [h, ite_false, ih, Nat.sub_sub, ← Nat.succ_eq_one_add, size'_eq_succ_size' h]

def prefixZeroesLen (n : ℕ) := if h : n = 0 then 0 else go n 0 h
  where go (m acc : ℕ) (h : m ≠ 0) :=
    if h' : m &&& 1 = 0 then
      go (m / 2) (acc + 1) (div_ne_zero_of_ne_zero_and_mod_eq_zero h
                            $ Eq.trans (Eq.symm $ and_one_is_mod _) h')
    else acc
decreasing_by apply bitwise_rec_lemma; assumption

private lemma prefixZeroes.go_spec {n acc} (h : n ≠ 0)
    : prefixZeroesLen.go n acc h = prefixZeroesLen n + acc := by
  induction' n using div2Rec' with n _ ih generalizing acc
  . exact absurd rfl h
  . simp_rw [prefixZeroesLen, h, dite_false]
    rw [prefixZeroesLen.go, prefixZeroesLen.go]
    simp_rw [apply_dite (. + acc), Nat.zero_add, ih, add_assoc, Nat.add_comm]

lemma prefixZeroes_spec (n : ℕ) :
    testBit n (prefixZeroesLen n) = (n != 0)
    ∧ (∀ i < prefixZeroesLen n, testBit n i = false) := by
  suffices : (n ≠ 0 → testBit n (prefixZeroesLen n) = true)
            ∧ (∀ i < prefixZeroesLen n, testBit n i = false)
  . refine (Decidable.eq_or_ne n 0).elim ?_ (this.imp_left ∘ ?_)
    . intro h; subst h; exact ⟨rfl, fun _ _ => zero_testBit _⟩
    . intro h1 h2; exact Eq.trans (h2 h1) (Eq.symm $ (bne_iff_ne _ _).mpr h1)
  induction' n using div2Rec' with n h ih
  . exact ⟨absurd rfl, fun _ _ => zero_testBit _⟩
  . rw [and_congr_left' (forall_prop_of_true h), prefixZeroesLen]
    simp only [h, dite_false]
    rw [prefixZeroesLen.go, Nat.zero_add]
    simp_rw [prefixZeroes.go_spec]
    split_ifs with h' <;> rw [and_one_is_mod] at h'
    . refine ih.imp ?_ ?_ <;> clear ih <;> intro ih
      . specialize ih (div_ne_zero_of_ne_zero_and_mod_eq_zero h h')
        exact Eq.trans (testBit_succ_div2 n _) ih
      . rintro (_|⟨i⟩) H
        . exact Eq.trans (testBit_zero_is_mod2 n)
                $ decide_eq_false $ ne_of_eq_of_ne h' (Nat.zero_ne_one)
        . exact Eq.trans (testBit_succ_div2 n _) $ ih i (lt_of_succ_lt_succ H)
    . exact ⟨Eq.trans (testBit_zero_is_mod2 _) $ decide_eq_true
            $ (Nat.mod_two_eq_zero_or_one n).resolve_left h',
            Not.elim ∘' Nat.not_lt_zero⟩

lemma testBit_prefixZeroesLen {n} (h : n ≠ 0) : testBit n (prefixZeroesLen n) :=
  Eq.trans (prefixZeroes_spec n).left ((bne_iff_ne n 0).mpr h)

lemma testBit_eq_false_of_lt_prefixZeroesLen {n i} : i < prefixZeroesLen n →
    testBit n i = false := (prefixZeroes_spec n).right i

lemma prefixZeroesLen_le_size' (n : ℕ) : prefixZeroesLen n ≤ size' n :=
  if h : n = 0
  then h ▸ le_refl 0
  else le_of_lt $ lt_size'_of_testBit_eq_true $ testBit_prefixZeroesLen h

lemma shiftRight_shiftLeft_prefixZeroesLen (n : ℕ) :
    (n >>> prefixZeroesLen n) <<< prefixZeroesLen n = n := by
  refine Eq.trans (shiftRight_shiftLeft_eq _ _) $ eq_of_testBit_eq $ fun i =>
          Eq.trans (testBit_ldiff _ _ i) $ Bool.not_inj ?_
  rw [Bool.not_and, Bool.eq_iff_iff, Bool.or_eq_true, Bool.not_eq_true',
      Bool.not_not, testBit_two_pow_sub_one, decide_eq_true_eq]
  exact or_iff_left_of_imp testBit_eq_false_of_lt_prefixZeroesLen

lemma testBit_reverseBits : ∀ n i,
    testBit (reverseBits n) i
    = ((i < size' n) && testBit n (size' n - i - 1)) := by
  suffices : ∀ n acc i, testBit (reverseBits.go n acc) i
                      = (((i < size' n) && testBit n (size' n - i - 1))
                        || ((size' n ≤ i) && testBit acc (i - size' n)))
  . intro n i
    refine Eq.trans (this n 0 i) (Eq.trans (congrArg _ ?_) (Bool.or_false _))
    exact Eq.trans (congrArg _ (zero_testBit (i - size' n))) (Bool.and_false _)
  intro n acc i
  simp_rw (config:={singlePass:=true})
    [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
     ← not_lt, ← ite_prop_iff_or, ← apply_ite (. = true), ← Bool.eq_iff_iff]
  induction' n using div2Rec' with n h ih generalizing acc i <;> rw [reverseBits.go]
  . simp_rw [size'_zero, not_lt_zero', ite_false, Nat.sub_zero, ite_true]
  . simp_rw [h, ite_false, Nat.and_one_is_mod]
    rw [Bool.cond_eq_ite, if_congr (decide_eq_true_iff _) (zero_or _).symm rfl,
        ← apply_ite ((acc <<< 1) ||| .),
        ite_eq_iff'.mpr ⟨Eq.symm, Eq.symm ∘ (mod_two_eq_zero_or_one n).resolve_left⟩,
        size'_eq_succ_size' h, ih, Nat.succ_sub_sub_succ, Nat.sub_zero]
    simp only [lt_succ_iff_lt_or_eq, Decidable.or_iff_not_and_not, ite_not, ite_and]
    refine ite_congr rfl (Eq.trans (testBit_succ_div2 _ _).symm
                          ∘ congrArg _ ∘ succ_pred ∘ Nat.sub_ne_zero_iff_lt.mpr
                          ∘ Nat.sub_pos_of_lt) (?_ ∘ le_of_not_lt)
    intro h'
    simp_rw [testBit_lor, testBit_shiftLeft, ge_iff_le, succ_le_iff, Nat.sub_pos_iff_lt]
    split_ifs with h''
    . simp_rw [h'', Nat.sub_self, decide_eq_false (lt_irrefl _), Bool.false_and,
               Bool.false_or, testBit_zero_is_mod2, mod_mod]
    . rw [decide_eq_true (lt_of_le_of_ne h' (Ne.symm h'')), Bool.true_and]
      refine Eq.trans (congrArg _ ?_) (Bool.or_false _)
      rw [← and_one_is_mod, testBit_and, Bool.and_eq_false_iff]
      exact Or.inr  $ Eq.trans (testBit_two_pow_sub_one 1 _)
                    $ decide_eq_false
                    $ mt (le_antisymm h' ∘ Nat.le_of_sub_eq_zero ∘ lt_one_iff.mp)
                    $ Ne.symm h''

lemma size'_reverseBits_le (n : ℕ) : size' (reverseBits n) ≤ size' n := by
  simp only [testBit_reverseBits, Bool.and_eq_true, decide_eq_true_iff,
             size'_le_iff_testBit_imp_lt]
  intro; exact And.left

lemma reverseBits_shiftLeft (n w : ℕ) : reverseBits (n <<< w) = reverseBits n := by
  apply eq_of_testBit_eq
  intro i
  simp_rw [testBit_reverseBits]
  rw [testBit_shiftLeft, size'_shiftLeft]
  split_ifs with h
  . simp only [h, size'_zero, not_lt_zero', decide_False, Nat.zero_sub, Bool.false_and]
  . simp only [Nat.sub_sub _ i 1, Nat.sub_right_comm _ _ w, Nat.add_sub_cancel]
    rw [← Bool.and_assoc, ← Bool.decide_and]
    refine congrArg₂ _ (Bool.decide_congr ?_) rfl
    rw [ge_iff_le, and_congr_right (Nat.le_sub_iff_add_le ∘ add_one_le_iff.mpr),
        Nat.add_comm w, Nat.add_le_add_iff_right, Nat.add_one_le_iff]
    exact and_iff_right_of_imp (Nat.lt_of_lt_of_le . (Nat.le_add_right _ _))

private lemma size'_reverseBits_of_lsb_one {n : ℕ} (h : n % 2 = 1) :
    size' (reverseBits n) = size' n :=
  le_antisymm (size'_reverseBits_le _)
  $ le_of_pred_lt $ lt_size'_of_testBit_eq_true
  $ Eq.trans (testBit_reverseBits _ _)
  $ (Bool.and_eq_true _ _).mpr ⟨
  decide_eq_true
  $ Nat.pred_lt $ size'_eq_zero.not.mpr
  $ mt (congrArg (. % 2)) (ne_of_eq_of_ne h Nat.zero_ne_one.symm),
  Eq.trans (congrArg _ $ Eq.trans (Nat.sub_sub _ _ _) $ Nat.sub_eq_zero_of_le
                        $ Nat.le_succ_of_pred_le $ le_refl _)
  $ Eq.trans (Nat.testBit_zero_is_mod2 n) $ decide_eq_true h⟩

lemma reverseBits_reverseBits_of_lsb_one {n : ℕ} (h : n % 2 = 1) :
    reverseBits (reverseBits n) = n :=
  eq_of_testBit_eq $ fun i => Bool.eq_iff_iff.mpr $ by
    simp only [testBit_reverseBits, Bool.and_eq_true, decide_eq_true_iff,
               ← and_assoc, size'_reverseBits_of_lsb_one h, Nat.sub_sub]
    rw [and_iff_left_of_imp (Nat.sub_lt_self (succ_pos _) ∘ succ_le.mpr)]
    refine Iff.trans ?_ $ and_iff_right_of_imp lt_size'_of_testBit_eq_true
    refine and_congr_right (Bool.eq_iff_iff.mp ∘ congrArg _ ∘ ?_)
    rw [← Nat.sub_sub]
    exact Nat.sub_eq_of_eq_add ∘ Nat.sub_sub_self ∘ Nat.succ_le.mp

lemma reverseBits_reverseBits (n : ℕ) :
    reverseBits (reverseBits n) = n >>> prefixZeroesLen n := by
  refine (Decidable.eq_or_ne n 0).elim (. ▸ rfl) ?_
  refine Eq.trans (congrArg _ ?_) ∘ reverseBits_reverseBits_of_lsb_one ∘ ?_
  . exact Eq.trans (congrArg _ (shiftRight_shiftLeft_prefixZeroesLen n)).symm
          $ reverseBits_shiftLeft _ _
  . exact of_decide_eq_true ∘ Eq.trans (Nat.testBit_zero_is_mod2 _).symm
          ∘ Eq.trans (testBit_shiftRight _) ∘ testBit_prefixZeroesLen

lemma size'_reverseBits (n : ℕ) :
    size' (reverseBits n) = size' n - prefixZeroesLen n := by
  refine Eq.trans ?_ (size'_shiftRight _ _)
  refine (Decidable.eq_or_ne n 0).elim (. ▸ rfl) ?_; intro h
  refine Eq.trans (Eq.symm ?_) (congrArg _ (reverseBits_reverseBits _))
  refine size'_reverseBits_of_lsb_one ?_
  refine of_decide_eq_true $ Eq.trans (Nat.testBit_zero_is_mod2 _).symm ?_
  refine Eq.trans ?_ (testBit_size'_sub_one h)
  rw [← Nat.pos_iff_ne_zero, ← size'_pos] at h
  rw [testBit_reverseBits, decide_eq_true h, Bool.true_and, Nat.sub_zero]

lemma reverseBits_eq_zero {n} : reverseBits n = 0 ↔ n = 0 := by
  refine Iff.intro (Decidable.not_imp_not.mp ?_) (congrArg reverseBits)
  intro h1 h2
  have h3 : n >>> _ = 0 := Eq.trans (Eq.symm $ reverseBits_reverseBits _) (congrArg _ h2)
  exact h1 $ Eq.trans (shiftRight_shiftLeft_prefixZeroesLen n).symm
           $ Eq.trans (congrArg (. <<< _) h3) (zero_shiftLeft _)

lemma size'_reverseBitsPadded {n} (h : n ≠ 0) (w : ℕ) :
    size' (reverseBitsPadded n w) = max (size' n) w - prefixZeroesLen n := by
  refine Eq.trans (congrArg _ (reverseBitsPadded_eq_reverseBits_shiftLeft _ _)) ?_
  refine Eq.trans (size'_shiftLeft _ _) ?_
  simp only [h, reverseBits_eq_zero, ite_false, size'_reverseBits]
  rw [Nat.add_comm, alt_sum_eq_max_sub_of_left_le]
  exact prefixZeroesLen_le_size' n

lemma size'_reverseBitsPadded_of_size'_le_padding {n w} (h : size' n ≤ w) :
    size' (reverseBitsPadded n w) ≤ w :=
  if h' : n = 0
  then ge_trans (Nat.zero_le _) $ ge_of_eq $ Eq.symm $ size'_eq_zero.mpr
       $ Eq.trans (congrArg₂ _ h' rfl)
       $ Eq.trans (reverseBitsPadded_eq_reverseBits_shiftLeft _ _)
       $ Nat.zero_shiftLeft _
  else le_of_eq_of_le (size'_reverseBitsPadded h' w) $ sub_le_of_le_add
       $ le_of_eq_of_le (max_eq_right h) (Nat.le_add_right w _)

lemma reverseBitsPadded_reverseBitsPadded {n w} (h : size' n ≤ w) :
    reverseBitsPadded (reverseBitsPadded n w) w = n := by
  rw [reverseBitsPadded_eq_reverseBits_shiftLeft]
  by_cases h' : n = 0
  . simp only [h', reverseBits_zero, zero_shiftLeft,
               reverseBitsPadded_eq_reverseBits_shiftLeft]
  . rw [size'_reverseBitsPadded h', max_eq_right h, Nat.sub_sub_self,
        reverseBitsPadded_eq_reverseBits_shiftLeft, reverseBits_shiftLeft,
        reverseBits_reverseBits, shiftRight_shiftLeft_prefixZeroesLen]
    exact le_trans (prefixZeroesLen_le_size' _) h

private
lemma testBit_reverseBitsPadded_rev {n w} (i : ℕ) (h1 : size' n ≤ w) (h2 : i < w) :
    testBit (reverseBitsPadded n w) (w - 1 - i) = testBit n i := by
  rw [Bool.eq_iff_iff, Nat.sub_sub, Nat.add_comm]
  simp only [reverseBitsPadded_eq_reverseBits_shiftLeft, testBit_reverseBits,
             testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff, ge_iff_le,
             Nat.sub_le_sub_iff_left h2, tsub_tsub_tsub_cancel_left h1]
  rw [← and_assoc, and_iff_left_of_imp (Nat.sub_lt_self (succ_pos i)),
      Nat.sub_right_comm, Nat.add_comm, ← Nat.sub_sub, Nat.succ_le]
  refine Iff.trans ?_ (and_iff_right_of_imp lt_size'_of_testBit_eq_true)
  refine and_congr_right (Bool.eq_iff_iff.mp ∘ congrArg (testBit n) ∘ ?_)
  exact Nat.sub_sub_self ∘ Nat.le_pred_of_lt

lemma testBit_reverseBitsPadded {n w} (i : ℕ) (h1 : size' n ≤ w) (h2 : i < w) :
    testBit (reverseBitsPadded n w) i = testBit n (w - 1 - i) :=
  have h1' := size'_reverseBitsPadded_of_size'_le_padding h1
  Eq.trans (Eq.symm $ testBit_reverseBitsPadded_rev i h1' h2)
  $ congrArg (testBit . _) $ reverseBitsPadded_reverseBitsPadded h1

end reverse

end Nat

end ShouldBeMoved

namespace Std.BitVec

open Nat

#noalign bitvec.bits_to_nat_to_list
#noalign bitvec.to_nat_append

variable {w v : Nat}

@[inline] protected def lsb (xs : BitVec w) : Bool := getLsb xs 0

def reverse (xs : BitVec w) : BitVec w :=
  ⟨reverseBitsPadded xs.toNat w,
  size'_le.mp $ size'_reverseBitsPadded_of_size'_le_padding $ size'_le.mpr (isLt xs)⟩

theorem toFin_injective : Function.Injective (toFin : BitVec w → _) :=
  fun _ _ h => congrArg ofFin h

theorem toFin_inj {x y : BitVec w} : x.toFin = y.toFin ↔ x = y :=
  toFin_injective.eq_iff

theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _) :=
  Fin.val_injective.comp toFin_injective

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  Iff.symm (toNat_eq x y)

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  Iff.rfl

lemma toNat_one : BitVec.toNat (1 : BitVec w) = Bool.toNat (w != 0) :=
  have : 2 ^ w ≤ 1 ↔ w = 0 := show 2^w ≤ 2^0 ↔ w = 0 from
    Iff.trans not_lt.symm $ Iff.trans (pow_lt_pow_iff_right Nat.one_lt_two).not
    $ Iff.symm (Decidable.iff_not_comm.mp Nat.pos_iff_ne_zero)
  Eq.trans (toNat_ofNat 1 w) $ Eq.trans (Nat.mod_eq _ _) $ by
  simp only [Bool.toNat, Bool.cond_eq_ite, two_pow_pos, bne_iff_ne, zero_mod,
             true_and, this, ite_not, Nat.sub_eq_zero_of_le, Nat.one_le_two_pow]

attribute [simp] toNat_ofNat toNat_ofFin

lemma toNat_ofNat_of_lt {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m :=
  Eq.trans (toNat_ofNat m w) (Nat.mod_eq_of_lt h)

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

#align bitvec.of_fin_val Std.BitVec.toNat_ofFin

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]; cases b <;> rfl
#align bitvec.add_lsb_eq_twice_add_one Std.BitVec.addLsb_eq_twice_add_one

-- The previous statement was `(v : BitVec n) : v.toNat = v.toList.reverse.foldr (flip addLsb) 0`.
-- Since the statement is awkward and `Std.BitVec` has no comparable API, we just drop it.
#noalign bitvec.to_nat_eq_foldr_reverse

#align bitvec.to_nat_lt Std.BitVec.isLt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  rw [addLsb, ← Nat.div2_val, Nat.div2_bit]
#align bitvec.add_lsb_div_two Std.BitVec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  simp [addLsb]
#align bitvec.to_bool_add_lsb_mod_two Std.BitVec.decide_addLsb_mod_two

lemma ofNat_toNat' (x : BitVec w) : (x.toNat)#w = x := by
  rw [ofNat_toNat, truncate_eq]

lemma ofNat_toNat_of_eq (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h :=
  toNat_injective $ Eq.trans (toNat_ofNat_of_lt (h ▸ isLt x)) (Eq.symm (toNat_cast h x))

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := rfl
#align bitvec.to_fin_val Std.BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
#align bitvec.to_fin_le_to_fin_of_le Std.BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j := by
  exact h
#align bitvec.of_fin_le_of_fin_of_le Std.BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
#align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := by
  rfl
#align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
### Distributivity of `Std.BitVec.ofFin`
-/
section
variable (x y : Fin (2^w))

@[simp] lemma ofFin_neg : ofFin (-x) = -(ofFin x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma ofFin_and : ofFin (x &&& y) = ofFin x &&& ofFin y := by
  simp only [HAnd.hAnd, AndOp.and, Fin.land, BitVec.and, toNat_ofFin, ofFin.injEq, Fin.mk.injEq]
  exact mod_eq_of_lt (Nat.and_lt_two_pow _ y.prop)

@[simp] lemma ofFin_or  : ofFin (x ||| y) = ofFin x ||| ofFin y := by
  simp only [HOr.hOr, OrOp.or, Fin.lor, BitVec.or, toNat_ofFin, ofFin.injEq, Fin.mk.injEq]
  exact mod_eq_of_lt (Nat.or_lt_two_pow x.prop y.prop)

@[simp] lemma ofFin_xor : ofFin (x ^^^ y) = ofFin x ^^^ ofFin y := by
  simp only [HXor.hXor, Xor.xor, Fin.xor, BitVec.xor, toNat_ofFin, ofFin.injEq, Fin.mk.injEq]
  exact mod_eq_of_lt (Nat.xor_lt_two_pow x.prop y.prop)

@[simp] lemma ofFin_add : ofFin (x + y)   = ofFin x + ofFin y   := rfl
@[simp] lemma ofFin_sub : ofFin (x - y)   = ofFin x - ofFin y   := rfl
@[simp] lemma ofFin_mul : ofFin (x * y)   = ofFin x * ofFin y   := rfl

-- These should be simp, but Std's simp-lemmas do not allow this yet.
lemma ofFin_zero : ofFin (0 : Fin (2^w)) = 0 := rfl
lemma ofFin_one  : ofFin (1 : Fin (2^w)) = 1 := by
  simp only [OfNat.ofNat, BitVec.ofNat, and_pow_two_is_mod]

lemma ofFin_nsmul (n : ℕ) (x : Fin (2^w)) : ofFin (n • x) = n • ofFin x := rfl
lemma ofFin_zsmul (z : ℤ) (x : Fin (2^w)) : ofFin (z • x) = z • ofFin x := rfl
@[simp] lemma ofFin_pow (n : ℕ) : ofFin (x ^ n) = ofFin x ^ n := rfl

@[simp] lemma ofFin_natCast (n : ℕ) : ofFin (n : Fin (2^w)) = n := by
  simp only [Nat.cast, NatCast.natCast, OfNat.ofNat, BitVec.ofNat, and_pow_two_is_mod]
  rfl

-- See Note [no_index around OfNat.ofNat]
@[simp] lemma ofFin_ofNat (n : ℕ) :
    ofFin (no_index (OfNat.ofNat n : Fin (2^w))) = OfNat.ofNat n := by
  simp only [OfNat.ofNat, Fin.ofNat', BitVec.ofNat, and_pow_two_is_mod]

end

/-!
### Distributivity of `Std.BitVec.toFin`
-/
section
variable (x y : BitVec w)

@[simp] lemma toFin_neg : toFin (-x) = -(toFin x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma toFin_and : toFin (x &&& y) = toFin x &&& toFin y := by
  apply toFin_inj.mpr; simp only [ofFin_and]

@[simp] lemma toFin_or  : toFin (x ||| y) = toFin x ||| toFin y := by
  apply toFin_inj.mpr; simp only [ofFin_or]

@[simp] lemma toFin_xor : toFin (x ^^^ y) = toFin x ^^^ toFin y := by
  apply toFin_inj.mpr; simp only [ofFin_xor]

@[simp] lemma toFin_add : toFin (x + y)   = toFin x + toFin y   := rfl
@[simp] lemma toFin_sub : toFin (x - y)   = toFin x - toFin y   := rfl
@[simp] lemma toFin_mul : toFin (x * y)   = toFin x * toFin y   := rfl

-- These should be simp, but Std's simp-lemmas do not allow this yet.
lemma toFin_zero : toFin (0 : BitVec w) = 0 := rfl
lemma toFin_one  : toFin (1 : BitVec w) = 1 := by
  apply toFin_inj.mpr; simp only [ofNat_eq_ofNat, ofFin_ofNat]

lemma toFin_nsmul (n : ℕ) (x : BitVec w) : toFin (n • x) = n • x.toFin := rfl
lemma toFin_zsmul (z : ℤ) (x : BitVec w) : toFin (z • x) = z • x.toFin := rfl
@[simp] lemma toFin_pow (n : ℕ) : toFin (x ^ n) = x.toFin ^ n := rfl

@[simp] lemma toFin_natCast (n : ℕ) : toFin (n : BitVec w) = n := by
  apply toFin_inj.mpr; simp only [ofFin_natCast]

-- See Note [no_index around OfNat.ofNat]
lemma toFin_ofNat (n : ℕ) :
    toFin (no_index (OfNat.ofNat n : BitVec w)) = OfNat.ofNat n := by
  simp only [OfNat.ofNat, BitVec.ofNat, and_pow_two_is_mod, Fin.ofNat']

end

/-!
### `IntCast`
-/

-- Either of these follows trivially from the other. Which one to
-- prove is not yet clear.
lemma ofFin_intCast (z : ℤ) : ofFin (z : Fin (2^w)) = z := by
  cases' z with n n
  . simp only [Int.ofNat_eq_coe, Int.cast_ofNat, ofFin_natCast]; rfl
  . refine congrArg ofFin ?_
    change -(_ : Fin (2^w)) = { val := _ - 1 ^^^ (n#w).toNat, isLt := _ }
    simp_rw [← Fin.ofNat''_eq_cast, Fin.ofNat'']
    simp (config:={singlePass:=true}) only [Nat.add_mod, toNat_ofNat]
    change (- ((n : Fin (2^w)) + 1)) = _
    refine Eq.trans (neg_add _ _) $ neg_add_eq_of_eq_add ?_
    by_cases h : w = 0
    . subst h; exact Fin.subsingleton_one.allEq _ _
    . refine Fin.val_injective ?_
      have h' : ((1 : Fin (2 ^ w)) : ℕ) = 1 :=
        Eq.trans (Fin.val_one' _) $ Nat.mod_eq_of_lt
        $ pow_right_strictMono Nat.one_lt_two (Nat.pos_iff_ne_zero.mpr h)
      have h'' : n % 2 ^ w &&& (2 ^ w - 1 ^^^ n % 2 ^ w) = 0
      . refine zero_of_testBit_eq_false (fun _ => ?_)
        simp only [testBit_land, testBit_xor, testBit_two_pow_sub_one,
                   Nat.testBit_mod_two_pow]
        rw [and_distrib_of_false_false_ax (Bool.xor_self false),
            Bool.and_self, Bool.and_right_comm, Bool.and_self, Bool.xor_self]
      rw [neg_eq_zero_sub, Fin.coe_sub_iff_lt.mpr, h']
      . refine Eq.trans (congrArg (_ + . - _) (zero_mod _)) ?_
        simp only [Nat.add_zero, Fin.val_add, Fin.val_nat_cast,
                   Nat.shiftLeft_eq, one_mul]
        rw [← or_eq_add_of_and_eq_zero h'', or_eq_xor_of_and_eq_zero h'',
            ← Nat.xor_comm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        exact Eq.symm (mod_eq_of_lt (Nat.sub_lt_self zero_lt_one (two_pow_pos _)))
      . exact Nat.pos_iff_ne_zero.mpr (ne_of_eq_of_ne h' one_ne_zero)

lemma toFin_intCast (z : ℤ) : toFin (z : BitVec w) = z :=
  congrArg toFin $ Eq.symm $ ofFin_intCast z

/-!
## Ring
-/

instance : CommRing (BitVec w) :=
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg
    toFin_sub (Function.swap toFin_nsmul) (Function.swap toFin_zsmul)
    toFin_pow toFin_ofNat toFin_intCast

-- todo: clean up proof of ofFin_intCast with these lemmas

lemma toNat_one_eq_one (h : w ≠ 0) : (1 : BitVec w).toNat = 1 :=
  Eq.trans toNat_one (congrArg Bool.toNat (Iff.mpr (bne_iff_ne _ _) h))

theorem toNat_neg (xs : BitVec w) :
    (-xs).toNat = if xs = 0 then 0 else 2^w - xs.toNat :=
  eq_ite_iff'.mpr $ And.intro (. ▸ congrArg _ neg_zero)
    $ Eq.trans (congrArg Fin.val (toFin_neg _)) ∘ mod_eq_of_lt
    ∘ sub_lt (two_pow_pos w) ∘ Nat.pos_of_ne_zero ∘ mt (@eq_of_toNat_eq w _ 0)

lemma one_eq_zero_iff : (1 : BitVec w) = 0 ↔ w = 0 := by
  rw [toNat_eq, toNat_one, ofNat_eq_ofNat, toNat_zero, ← beq_iff_eq,
      Bool.toNat_beq_zero, bne, Bool.not_not, beq_iff_eq]

lemma not_one_eq_zero : w ≠ 0 → (1 : BitVec w) ≠ 0 := mt one_eq_zero_iff.mp

theorem allOnes_def : BitVec.allOnes w = - 1 := rfl

theorem toNat_allOnes : (BitVec.allOnes w).toNat = 2^w - 1 :=
  Eq.trans (toNat_neg _)
  $ Eq.trans (ite_congr (propext one_eq_zero_iff) (Eq.symm ∘ congrArg (2^.-1))
              $ congrArg (2^w - .) ∘ toNat_ofNat_of_lt ∘ Nat.one_lt_two_pow w)
  $ ite_self _

lemma toNat_xor (xs ys : BitVec w) : (xs ^^^ ys).toNat = xs.toNat ^^^ ys.toNat := rfl
lemma toNat_and (xs ys : BitVec w) : (xs &&& ys).toNat = xs.toNat &&& ys.toNat := rfl

lemma ne_allOnes_iff_lt (xs : BitVec w) : xs ≠ allOnes w ↔ xs.toNat < 2^w - 1 :=
  Iff.trans (toNat_eq _ _).not
  $ toNat_allOnes.symm ▸ (ne_iff_lt_iff_le.mpr (le_pred_of_lt (isLt xs)))

lemma add_one_eq_zero_iff_allOnes (xs : BitVec w) : xs + 1 = 0 ↔ xs = allOnes w :=
  by rw [add_eq_zero_iff_eq_neg, allOnes_def]

lemma toNat_add_one (xs : BitVec w) :
    (xs + 1).toNat = if xs = allOnes w then 0 else xs.toNat + 1 := by
  split_ifs with h
  . rw [h, allOnes_def, add_left_neg, ofNat_eq_ofNat, toNat_zero]
  . rw [toNat_add, toNat_one_eq_one (mt _ h), mod_eq_of_lt]
    . exact Nat.add_lt_of_lt_sub ((ne_allOnes_iff_lt _).mp h)
    . intro; subst w; exact Subsingleton.allEq _ _

@[simp]
theorem cons_msb_truncate (xs : BitVec (w+1)) : cons xs.msb (xs.truncate w) = xs := by
  refine eq_of_getLsb_eq ?_
  intro i
  refine Eq.trans (getLsb_cons _ _ _) $ ite_eq_iff'.mpr
    ⟨?_ ∘ congrArg (getLsb xs) ∘ Eq.symm, ?_ ∘ lt_of_le_of_ne (Fin.is_le i)⟩
  . refine Eq.trans ?_ ∘ Eq.trans (Bool.true_and _)
    exact congrArg (. && _) (decide_eq_true (zero_lt_succ w))
  . intro h
    refine Eq.trans (getLsb_truncate _ _ _) ?_
    exact Eq.trans (congrArg (. && _) (decide_eq_true h)) (Bool.true_and _)

@[elab_as_elim]
def consRecOn {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs)) :
    ∀ {w} (x : BitVec w), motive x
  | 0,    x => _root_.cast (congrArg motive (eq_nil x).symm) nil
  | w+1,  x => _root_.cast (congrArg motive $ cons_msb_truncate x)
      $ cons x.msb (x.truncate w) $ consRecOn nil cons $ x.truncate w

@[simp] lemma consRecOn_nil {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs)) :
    consRecOn nil cons BitVec.nil = nil := rfl

@[simp] lemma getLsb_cast (h : w = v) (xs : BitVec w) (i : ℕ) :
    getLsb (cast h xs) i = getLsb xs i :=
  congrArg (testBit . i) (toNat_cast h xs)

@[simp] lemma getMsb_cast (h : w = v) (xs : BitVec w) (i : ℕ) :
    getMsb (cast h xs) i = getMsb xs i :=
  congrArg₂ Bool.and (congrArg (decide $ i < .) h.symm)
  $ Eq.trans (getLsb_cast h xs _) $ congrArg (getLsb xs $ . - 1 - i) h.symm

@[simp] lemma getLsb'_cast (h : w = v) (xs : BitVec w) (i : Fin v) :
    getLsb' (cast h xs) i = getLsb' xs (i.cast h.symm) :=
  getLsb_cast h xs i

@[simp] lemma getMsb'_cast (h : w = v) (xs : BitVec w) (i : Fin v) :
    getMsb' (cast h xs) i = getMsb' xs (i.cast h.symm) :=
  getMsb_cast h xs i

lemma toNat_size'_le (xs : BitVec w) : size' xs.toNat ≤ w := size'_le.mpr xs.isLt

lemma lt_width_of_getLsb_eq_true {xs : BitVec w} {i} (h : getLsb xs i) : i < w :=
  lt_of_lt_of_le (lt_size'_of_testBit_eq_true h) (toNat_size'_le xs)

lemma lt_width_of_getMsb_eq_true {xs : BitVec w} {i} (h : getMsb xs i) : i < w :=
  of_decide_eq_true $ And.left $ (Bool.and_eq_true _ _).mp h

lemma getLsb_eq_false_of_width_le {xs : BitVec w} {i} :
    w ≤ i → getLsb xs i = false :=
  (Bool.not_eq_true _).mp ∘ (mt lt_width_of_getLsb_eq_true ∘ not_lt.mpr)

lemma getMsb_eq_false_of_width_le {xs : BitVec w} {i} :
    w ≤ i → getMsb xs i = false :=
  (Bool.not_eq_true _).mp ∘ (mt lt_width_of_getMsb_eq_true ∘ not_lt.mpr)

@[simp] lemma toNat_nil : BitVec.toNat nil = 0 := rfl

@[simp] lemma getLsb_nil {i} : getLsb nil i = false := zero_testBit i
@[simp] lemma getMsb_nil {i} : getMsb nil i = false := rfl

lemma cast_heq : ∀ (h : w = v) (xs : BitVec w), HEq (cast h xs) xs
  | rfl => HEq.refl

lemma toNat_append' {m n : ℕ} (x : BitVec m) (y : BitVec n) :
    BitVec.toNat (x ++ y) = x.toNat * 2^n + y.toNat := by
  refine Eq.trans (toNat_append x y) ?_
  refine Eq.trans ?_ (congrArg (. + _) (Nat.shiftLeft_eq _ _))
  refine Nat.or_eq_add_of_and_eq_zero ?_
  apply Nat.zero_of_testBit_eq_false; intro i
  rw [← Bool.not_eq_true, Nat.testBit_land, Bool.and_eq_true, not_and,
      testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true]
  exact getLsb_eq_false_of_width_le ∘ And.left

lemma append_assoc {w v u} (xs : BitVec w) (ys : BitVec v) (zs : BitVec u) :
    xs ++ (ys ++ zs) = cast (Nat.add_assoc w v u) (xs ++ ys ++ zs) :=
  by simp_rw [toNat_eq, toNat_cast, toNat_append, shiftLeft_add, ← lor_shiftLeft, lor_assoc]

lemma append_assoc_heq {w v u} (xs : BitVec w) (ys : BitVec v) (zs : BitVec u) :
    HEq (xs ++ (ys ++ zs)) (xs ++ ys ++ zs) :=
  heq_of_eq_of_heq (append_assoc xs ys zs) (cast_heq _ _)

lemma cons_append (b : Bool) (xs : BitVec w) (ys : BitVec v) :
    cons b xs ++ ys = cast (Nat.add_right_comm _ _ _) (cons b (xs ++ ys)) :=
  Eq.symm $ Eq.trans (cast_cast _ _ _) (congrArg _ $ append_assoc _ _ _)

lemma cons_append_heq (b : Bool) (xs : BitVec w) (ys : BitVec v) :
    HEq (cons b xs ++ ys) (cons b (xs ++ ys)) :=
  heq_of_eq_of_heq (cons_append b xs ys) (cast_heq _ _)

lemma cons_heq_append (b : Bool) (xs : BitVec w) :
    HEq (cons b xs) (ofBool b ++ xs) := cast_heq _ _

-- we can actually get rid of the cast here, but it's relying too much on a defeq
lemma append_concat (xs : BitVec w) (ys : BitVec v) (b : Bool) :
    xs ++ concat ys b = cast (Nat.add_assoc _ _ _) (concat (xs ++ ys) b) :=
  append_assoc _ _ _

lemma append_concat_heq (b : Bool) (xs : BitVec w) (ys : BitVec v) :
    HEq (xs ++ concat ys b) (concat (xs ++ ys) b) :=
  heq_of_eq_of_heq (append_concat xs ys b) (cast_heq _ _)

lemma concat_eq_append (xs : BitVec w) (b : Bool) :
    concat xs b = xs ++ ofBool b := rfl

@[simp] lemma append_nil (xs : BitVec w) : xs ++ nil = cast (Nat.add_zero _) xs :=
  by rw [toNat_eq, toNat_cast, toNat_append, toNat_nil, shiftLeft_zero, Nat.zero_or]

lemma append_nil_heq (xs : BitVec w) : HEq (xs ++ nil) xs :=
  heq_of_eq_of_heq (append_nil xs) (cast_heq _ _)

@[simp] lemma nil_append (xs : BitVec w) : nil ++ xs = cast (Nat.zero_add _).symm xs :=
  by rw [toNat_eq, toNat_cast, toNat_append, toNat_nil, zero_shiftLeft, Nat.or_zero]

lemma nil_append_heq (xs : BitVec w) : HEq (nil ++ xs) xs :=
  heq_of_eq_of_heq (nil_append xs) (cast_heq _ _)

@[simp] lemma reverse_nil : reverse nil = nil := rfl

@[simp] lemma reverse_bit : ∀ {xs : BitVec 1}, reverse xs = xs
  | ⟨b, h⟩ => eq_of_toNat_eq $ show reverseBitsPadded b 1 = b from
    Or.elim (Nat.le_one_iff_eq_zero_or_eq_one.mp $ Nat.lt_succ.mp h)
            (Eq.symm . ▸ rfl) (Eq.symm . ▸ rfl)

@[simp] lemma toNat_reverse (xs : BitVec w) :
    (reverse xs).toNat = reverseBitsPadded xs.toNat w := rfl

lemma reverse_reverse (xs : BitVec w) : reverse (reverse xs) = xs :=
  eq_of_toNat_eq (reverseBitsPadded_reverseBitsPadded (toNat_size'_le xs))

lemma getMsb'_eq_getLsb'_rev (xs : BitVec w) (i : Fin w) :
    getMsb' xs i = getLsb' xs i.rev :=
  Eq.trans (congrArg (. && _) (decide_eq_true i.prop))
  $ Eq.trans (Bool.true_and _) $ congrArg _ $ Nat.sub_right_comm w 1 i

lemma getLsb'_eq_getMsb'_rev (xs : BitVec w) (i : Fin w) :
    getLsb' xs i = getMsb' xs i.rev := Eq.symm $
  Eq.trans (getMsb'_eq_getLsb'_rev _ i.rev) $ congrArg (getLsb' xs) i.rev_rev

lemma getMsb'_reverse (xs : BitVec w) (i : Fin w) :
    getMsb' (reverse xs) i = getLsb' xs i :=
  Eq.trans (getMsb'_eq_getLsb'_rev _ i)
  $ Eq.trans (congrArg (testBit _)
              $ Eq.trans (Nat.sub_sub _ _ _).symm (Nat.sub_right_comm _ _ _))
  $ testBit_reverseBitsPadded_rev _ (toNat_size'_le xs) i.prop

lemma getLsb'_reverse (xs : BitVec w) (i : Fin w) :
    getLsb' (reverse xs) i = getMsb' xs i :=
  Eq.trans (getMsb'_reverse _ _).symm $ congrArg₂ _ (reverse_reverse _) rfl

lemma getMsb_reverse (xs : BitVec w) (i : ℕ) :
    getMsb (reverse xs) i = getLsb xs i :=
  if h : i < w
  then getMsb'_reverse xs ⟨i, h⟩
  else Eq.trans (getMsb_eq_false_of_width_le (not_lt.mp h))
                (Eq.symm $ getLsb_eq_false_of_width_le (not_lt.mp h))

lemma getLsb_reverse (xs : BitVec w) (i : ℕ) :
    getLsb (reverse xs) i = getMsb xs i :=
  if h : i < w
  then getLsb'_reverse xs ⟨i, h⟩
  else Eq.trans (getLsb_eq_false_of_width_le (not_lt.mp h))
                (Eq.symm $ getMsb_eq_false_of_width_le (not_lt.mp h))

lemma getMsb_cons (b : Bool) (xs : BitVec w) (i : ℕ) :
    getMsb (cons b xs) i = if i = 0 then b else getMsb xs (i - 1) := by
  by_cases h : i < w + 1
  . simp only [getMsb, h, getLsb_cons, decide_True, Nat.add_sub_cancel, Bool.true_and]
    refine ite_congr ?_ (fun _ => rfl) ?_
    . refine propext ⟨?_, (. ▸ rfl)⟩
      refine Decidable.not_imp_not.mp (Nat.ne_of_lt ∘ ?_)
      intro h'
      have h'' := not_eq_zero_of_lt
        $ Nat.sub_lt_right_of_lt_add (one_le_iff_ne_zero.mpr h') h
      refine Nat.sub_lt (pos_iff_ne_zero.mpr h'') (pos_iff_ne_zero.mpr h')
    . intro h'
      have h'' : 1 ≤ i := Nat.succ_le.mpr (pos_iff_ne_zero.mpr h')
      refine Eq.symm $ Eq.trans (congrArg₂ Bool.and ?_ ?_) (Bool.true_and _)
      . exact decide_eq_true (Nat.sub_lt_right_of_lt_add h'' h)
      . exact congrArg _ (tsub_tsub_tsub_cancel_right h'')
  . simp only [getMsb, h, decide_False, Bool.false_and, ite_false,
               not_eq_zero_of_lt (not_lt.mp h), mt lt_add_of_tsub_lt_right h]

@[simp] lemma msb_cons (b : Bool) (xs : BitVec w) : (cons b xs).msb = b :=
  getMsb_cons b xs 0

@[simp]
lemma truncate_cons (b : Bool) (v : BitVec w) : truncate w (cons b v) = v := by
  apply eq_of_getLsb_eq; intro i
  simp only [getLsb_truncate, getLsb_cons, Fin.is_lt, decide_True, Bool.true_and]
  exact ite_eq_right_iff.mpr (Not.elim (Nat.ne_of_lt i.prop))

@[simp] lemma consRecOn_cons {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs))
    (b : Bool) (v : BitVec w) :
    consRecOn nil cons (v.cons b) = cons b v (consRecOn nil cons v) :=
  cast_eq_iff_heq.mpr $ by
    congr
    . apply getMsb_cons
    all_goals apply truncate_cons

lemma getLsb_append {xs : BitVec w} {ys : BitVec v} {i} :
    getLsb (xs ++ ys) i = (getLsb ys i || (v ≤ i && getLsb xs (i - v))) := by
  simp only [getLsb, toNat_append, testBit_lor]
  rw [testBit_shiftLeft]
  exact Bool.or_comm _ _

lemma getLsb_append' {xs : BitVec w} {ys : BitVec v} {i} :
    getLsb (xs ++ ys) i = if i < v then getLsb ys i else getLsb xs (i - v) := by
  simp_rw [getLsb_append, ← not_le, ite_not, eq_ite_iff']
  constructor <;> intro h
  . simp only [h, getLsb_eq_false_of_width_le, Bool.false_or, decide_True, Bool.true_and]
  . rw [decide_eq_false h, Bool.false_and, Bool.or_false]

lemma getMsb_append {xs : BitVec w} {ys : BitVec v} {i} :
    getMsb (xs ++ ys) i = (getMsb xs i || (w ≤ i && getMsb ys (i - w))) := by
  induction' xs using consRecOn with w b xs ih generalizing i
  . simp only [nil_append, getMsb_cast, getMsb_nil, Bool.false_or,
               Bool.true_and, Nat.zero_le, decide_True, Nat.sub_zero]
  . simp only [cons_append, getMsb_cast, getMsb_cons]
    split_ifs with h
    . simp only [h, decide_eq_false (not_succ_le_zero w), Bool.false_and, Bool.or_false]
    . rw [ih, Nat.sub_sub, Nat.add_comm 1 w]
      simp_rw [Nat.le_sub_iff_add_le (Nat.succ_le.mpr (pos_iff_ne_zero.mpr h))]

lemma reverse_append (xs : BitVec w) (ys : BitVec v) :
    reverse (xs ++ ys) = cast (Nat.add_comm _ _) (reverse ys ++ reverse xs) := by
  apply eq_of_getLsb_eq; intro
  simp only [getLsb_reverse, getMsb_append, getLsb_cast, getLsb_append]

lemma reverse_append_heq (xs : BitVec w) (ys : BitVec v) :
    HEq (reverse (xs ++ ys)) (reverse ys ++ reverse xs) :=
  heq_of_eq_of_heq (reverse_append _ _) (cast_heq _ _)

lemma reverse_concat (b : Bool) (xs : BitVec w) :
    reverse (concat xs b) = cons b (reverse xs) :=
  Eq.trans (reverse_append _ _) (congrArg (cast _ $ . ++ _) reverse_bit)

lemma reverse_cons (b : Bool) (xs : BitVec w) :
    reverse (cons b xs) = concat (reverse xs) b :=
  Eq.trans (Eq.symm $ congrArg reverse $ Eq.trans (reverse_concat b _)
                    $ congrArg _ $ reverse_reverse _)
           $ reverse_reverse _

lemma getLsb_concat (xs : BitVec w) (b : Bool) (i : ℕ) :
    getLsb (concat xs b) i = if i = 0 then b else getLsb xs (i - 1) :=
  by rw [← reverse_reverse (concat xs b), getLsb_reverse, reverse_concat,
         getMsb_cons, getMsb_reverse]

@[simp] lemma lsb_concat (xs : BitVec w) (b : Bool) : (concat xs b).lsb = b :=
  getLsb_concat xs b 0

def dropLast (xs : BitVec (w + 1)) : BitVec w :=
  ofFin ⟨xs.toNat >>> 1,
    lt_of_eq_of_lt (shiftRight_eq_div_pow _ _)
    $ Nat.div_lt_of_lt_mul $ lt_of_lt_of_eq xs.isLt (Nat.pow_add' 2 w 1)⟩

lemma getLsb_dropLast (xs : BitVec (w + 1)) (i : ℕ) :
    getLsb (dropLast xs) i = getLsb xs (i + 1) :=
  Eq.trans (testBit_shiftRight _) (congrArg _ (Nat.add_comm 1 i))

@[simp]
theorem dropLast_concat_lsb (xs : BitVec (w + 1)) :
    concat xs.dropLast xs.lsb = xs := by
  refine eq_of_getLsb_eq ?_; intro
  refine Eq.trans (getLsb_concat _ _ _) (ite_eq_iff'.mpr ⟨?_, ?_⟩)
  . exact congrArg (getLsb xs) ∘ Eq.symm
  . exact Eq.trans (getLsb_dropLast _ _) ∘ congrArg _ ∘ succ_pred

@[elab_as_elim]
def concatRecOn {motive : ∀ {w}, BitVec w → Sort*}
    (nil : motive BitVec.nil)
    (concat : ∀ {w} (xs : BitVec w) (x : Bool), motive xs → motive (concat xs x)) :
    ∀ {w} (x : BitVec w), motive x
  | 0,    x => _root_.cast (congrArg motive (eq_nil x).symm) nil
  | w+1,  x => _root_.cast (congrArg motive $ dropLast_concat_lsb x)
      $ concat x.dropLast x.lsb $ concatRecOn nil concat x.dropLast

@[simp] lemma concatRecOn_nil {motive : ∀ {w}, BitVec w → Sort*}
    (nil : motive BitVec.nil)
    (concat : ∀ {w} (xs : BitVec w) (x : Bool), motive xs → motive (concat xs x)) :
    concatRecOn nil concat BitVec.nil = nil := rfl

lemma dropLast_concat (v : BitVec w) (b : Bool) :
    dropLast (concat v b) = v := by
  apply eq_of_getLsb_eq; intro i
  simp only [getLsb_dropLast, getLsb_concat, Nat.succ_ne_zero, decide_False,
             ite_false, Nat.add_sub_cancel]

@[simp] lemma concatRecOn_concat {motive : ∀ {w}, BitVec w → Sort*}
    (nil : motive BitVec.nil)
    (concat : ∀ {w} (xs : BitVec w) (x : Bool), motive xs → motive (concat xs x))
    (v : BitVec w) (b : Bool) :
    concatRecOn nil concat (v.concat b) = concat v b (concatRecOn nil concat v) :=
  cast_eq_iff_heq.mpr $ by
    congr
    any_goals apply dropLast_concat
    . apply lsb_concat

theorem head_eq_of_cons_eq {b₁ b₂} {v₁ v₂ : BitVec w}
    (H : cons b₁ v₁ = cons b₂ v₂) : b₁ = b₂ :=
  Eq.trans (msb_cons _ _).symm $ Eq.trans (congrArg _ H) $ msb_cons _ _

theorem tail_eq_of_cons_eq {b₁ b₂} {v₁ v₂ : BitVec w}
    (H : cons b₁ v₁ = cons b₂ v₂) : v₁ = v₂ :=
  Eq.trans (truncate_cons _ _).symm $ Eq.trans (congrArg _ H) $ truncate_cons _ _

theorem cons_inj (b : Bool) {v₁ v₂ : BitVec w} : cons b v₁ = cons b v₂ ↔ v₁ = v₂ :=
  ⟨tail_eq_of_cons_eq, congrArg _⟩

lemma testBit_two_pow_sub_one_xor (n : ℕ) {i w} (h : i < w) :
    testBit ((2^w - 1) ^^^ n) i = !testBit n i := by
  rw [testBit_xor, testBit_two_pow_sub_one, decide_eq_true h]
  exact Bool.true_xor _

lemma getLsb'_allOnes_xor (xs : BitVec w) (i : Fin w) :
    getLsb' (allOnes w ^^^ xs) i = !getLsb' xs i := by
  rw [getLsb', getLsb, toNat_xor, toNat_allOnes]
  exact testBit_two_pow_sub_one_xor xs.toNat i.prop

lemma getLsb_and (xs ys : BitVec w) (i : ℕ) :
    getLsb (xs &&& ys) i = (getLsb xs i && getLsb ys i) := testBit_land _ _ i

theorem toNat_not (xs : BitVec w) : (~~~xs).toNat = (2^w - 1) ^^^ xs.toNat := by
  refine Eq.trans (BitVec.toNat_xor _ _) (congrArg (. ^^^ _) ?_)
  exact congrArg (. - 1) (Eq.trans (Nat.shiftLeft_eq _ _) (Nat.one_mul _))

-- BitVec.not is changed to this (roughly) in an upcoming Std
theorem not_alt_desc (xs : BitVec w) : ~~~xs = BitVec.allOnes w ^^^ xs :=
  eq_of_toNat_eq $ Eq.symm $ Eq.trans (toNat_xor _ _)
  $ Eq.trans (congrArg (. ^^^ xs.toNat) toNat_allOnes) $ Eq.symm $ toNat_not xs

lemma getLsb'_not (xs : BitVec w) (i : Fin w) :
    getLsb' (~~~xs) i = !getLsb' xs i :=
  Eq.trans (congrArg (getLsb' . i) (not_alt_desc _)) (getLsb'_allOnes_xor _ _)

lemma not_append (xs : BitVec w) (ys : BitVec v) :
    ~~~(xs ++ ys) = ~~~xs ++ ~~~ys := by
  apply eq_of_getLsb_eq; intro i
  rw [← getLsb', getLsb'_not, getLsb', getLsb_append', getLsb_append']
  split_ifs with h <;> refine Eq.symm (getLsb'_not _ ⟨_, ?_⟩)
  . exact h
  . exact Or.resolve_left (lt_add_iff.mp (Nat.add_comm w v ▸ i.prop)) h

lemma not_ofBool (b : Bool) : ~~~ ofBool b = ofBool (!b) :=
  by cases' b <;> exact eq_of_toNat_eq rfl

lemma not_cons (b : Bool) (xs : BitVec w) :
    ~~~(cons b xs) = cons (!b) (~~~xs) := by
  refine eq_of_heq ?_
  refine HEq.trans ?_ (cons_heq_append _ _).symm
  refine heq_of_heq_of_eq ?_ (congrArg₂ _ (not_ofBool _) rfl)
  refine heq_of_heq_of_eq ?_ (not_append _ _)
  have := Nat.add_comm w 1; congr 2; exact cons_heq_append b xs

lemma not_concat (xs : BitVec w) (b : Bool) :
    ~~~(concat xs b) = concat (~~~xs) (!b) :=
  Eq.trans (congrArg _ (concat_eq_append _ _))
  $ Eq.trans (not_append _ _)
  $ Eq.trans (congrArg _ (not_ofBool _)) (concat_eq_append _ _).symm

lemma not_not (xs : BitVec w) : ~~~(~~~xs) = xs :=
  eq_of_getLsb_eq $ fun _ =>
    Eq.trans (getLsb'_not _ _)
    $ Eq.trans (congrArg _ (getLsb'_not _ _)) (Bool.not_not _)

end Std.BitVec
