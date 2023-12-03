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

-- this should be moved
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
      . exact Ne.symm (succ_ne_zero _)

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

namespace Std.BitVec

open Nat

#noalign bitvec.bits_to_nat_to_list
#noalign bitvec.to_nat_append

variable {w v : Nat}

def reverse (xs : BitVec w) : BitVec w :=
  ⟨reverseBitsPadded xs.toNat w,
  size'_le.mp $ size'_reverseBitsPadded_of_size'_le_padding $ size'_le.mpr (isLt xs)⟩

theorem toNat_injective {n : Nat} : Function.Injective (@Std.BitVec.toNat n) :=
  fun _ _ => eq_of_toNat_eq

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  Iff.symm (toNat_eq x y)

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  Iff.rfl

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

lemma append_assoc {w v u} (xs : BitVec w) (ys : BitVec v) (zs : BitVec u) :
    xs ++ (ys ++ zs) = cast (Nat.add_assoc w v u) (xs ++ ys ++ zs) :=
  by simp_rw [toNat_eq, toNat_cast, toNat_append, shiftLeft_add, ← lor_shiftLeft, lor_assoc]

lemma cons_append (b : Bool) (xs : BitVec w) (ys : BitVec v) :
    cons b xs ++ ys = cast (Nat.add_right_comm _ _ _) (cons b (xs ++ ys)) :=
  Eq.symm $ Eq.trans (cast_cast _ _ _) (congrArg _ $ append_assoc _ _ _)

lemma append_nil (xs : BitVec w) : xs ++ nil = cast (Nat.add_zero _) xs :=
  by rw [toNat_eq, toNat_cast, toNat_append, toNat_nil, shiftLeft_zero, Nat.zero_or]

lemma nil_append (xs : BitVec w) : nil ++ xs = cast (Nat.zero_add _).symm xs :=
  by rw [toNat_eq, toNat_cast, toNat_append, toNat_nil, zero_shiftLeft, Nat.or_zero]

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

lemma getMsb_reverse (xs : BitVec w) {i} (h : i < w) :
    getMsb (reverse xs) i = getLsb xs i := getMsb'_reverse xs ⟨i, h⟩

lemma getLsb_reverse (xs : BitVec w) {i} (h : i < w) :
    getLsb (reverse xs) i = getMsb xs i := getLsb'_reverse xs ⟨i, h⟩

@[simp]
lemma getLsb_append {xs : BitVec w} {ys : BitVec v} {i} :
    getLsb (xs ++ ys) i = (getLsb ys i || (v ≤ i && getLsb xs (i - v))) := by
  simp only [getLsb, toNat_append, testBit_lor]
  rw [testBit_shiftLeft]
  exact Bool.or_comm _ _

@[simp]
lemma getMsb_append {xs : BitVec w} {ys : BitVec v} {i} :
    getMsb (xs ++ ys) i = (getMsb xs i || (w ≤ i && getMsb ys (i - w))) := by
  by_cases h : i < w + v
  . refine Eq.trans (getMsb'_eq_getLsb'_rev _ ⟨i, h⟩) ?_
    dsimp only [getLsb', Fin.val_rev]
    rw [getLsb_append, Nat.sub_right_comm, add_tsub_cancel_right]
    have H : v ≤ w + v - (i + 1) ↔ i + 1 ≤ w :=
      ⟨(Nat.add_le_add_iff_right _ _ w).mp ∘ Nat.add_le_of_le_sub' h,
        (Nat.le_sub_of_add_le' ∘ (Nat.add_le_add_right . _))⟩
    rw [Bool.decide_congr (Iff.trans H succ_le)]
    rw [lt_add_iff, Decidable.or_iff_not_imp_left] at h
    by_cases h' : i < w
    . simp only [not_le, h', decide_eq_false, decide_eq_true,
                 Bool.false_and, Bool.or_false, Bool.true_and]
      refine Eq.trans ?_ (Eq.symm $ getMsb'_eq_getLsb'_rev xs ⟨i, h'⟩)
      refine Eq.trans (congrArg₂ _ ?_ rfl) (Bool.false_or _)
      exact getLsb_eq_false_of_width_le (H.mpr h')
    . specialize h h'; rw [not_lt] at h'
      simp only [decide_True, decide_False, Bool.true_and, Bool.false_or,
                 getMsb_eq_false_of_width_le h', getLsb_eq_false_of_width_le _,
                 Bool.false_and, Bool.or_false, not_lt.mpr, getMsb, h', h]
      rw [Nat.sub_right_comm, ← Nat.sub_sub]
      refine congrArg (getLsb ys $ . - 1) ?_
      refine Eq.trans (congrArg₂ _ rfl (Nat.add_sub_cancel' h').symm) ?_
      rw [← Nat.sub_sub, add_tsub_cancel_left]
  . have h1 := mt (Nat.lt_add_right i w v) h
    have h2 := mt lt_add_of_tsub_lt_left h
    rw [Bool.eq_iff_iff]
    simp only [getMsb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff,
               h, h1, h2, false_and, and_false, false_or]

lemma reverse_append (xs : BitVec w) (ys : BitVec v) :
    reverse (xs ++ ys) = cast (Nat.add_comm _ _) (reverse ys ++ reverse xs) := by
  apply eq_of_getLsb_eq
  intro i
  refine Eq.trans (getLsb'_reverse _ i) (Eq.trans getMsb_append ?_)
  refine Eq.trans ?_ (Eq.symm $ Eq.trans (getLsb'_cast _ _ i) getLsb_append)
  dsimp only [Fin.coe_cast]
  by_cases h' : i < w
  . simp only [not_le.mpr h', decide_False, Bool.false_and, Bool.or_false]
    exact Eq.symm $ getLsb_reverse xs h'
  . rw [not_lt] at h'
    simp only [h', decide_True, Bool.true_and, Bool.false_or,
               getMsb_eq_false_of_width_le, getLsb_eq_false_of_width_le]
    exact Eq.symm $ getLsb_reverse ys $ Nat.sub_lt_left_of_lt_add h' i.prop

lemma reverse_concat (b : Bool) (xs : BitVec w) :
    reverse (concat xs b) = cons b (reverse xs) :=
  Eq.trans (reverse_append _ _) (congrArg (cast _ $ . ++ _) reverse_bit)

lemma reverse_cons (b : Bool) (xs : BitVec w) :
    reverse (cons b xs) = concat (reverse xs) b :=
  Eq.trans (Eq.symm $ congrArg reverse $ Eq.trans (reverse_concat b _)
                    $ congrArg _ $ reverse_reverse _)
           $ reverse_reverse _

end Std.BitVec
