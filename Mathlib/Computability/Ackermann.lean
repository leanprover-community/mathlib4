/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Computability.Primrec
import Mathlib.Tactic.Linarith

#align_import computability.ackermann from "leanprover-community/mathlib"@"9b2660e1b25419042c8da10bf411aa3c67f14383"

/-!
# Ackermann function

In this file, we define the two-argument Ackermann function `ack`. Despite having a recursive
definition, we show that this isn't a primitive recursive function.

## Main results

- `exists_lt_ack_of_nat_primrec`: any primitive recursive function is pointwise bounded above by
  `ack m` for some `m`.
- `not_primrec₂_ack`: the two-argument Ackermann function is not primitive recursive.

## Proof approach

We very broadly adapt the proof idea from
https://www.planetmath.org/ackermannfunctionisnotprimitiverecursive. Namely, we prove that for any
primitive recursive `f : ℕ → ℕ`, there exists `m` such that `f n < ack m n` for all `n`. This then
implies that `fun n => ack n n` can't be primitive recursive, and so neither can `ack`. We aren't
able to use the same bounds as in that proof though, since our approach of using pairing functions
differs from their approach of using multivariate functions.

The important bounds we show during the main inductive proof (`exists_lt_ack_of_nat_primrec`)
are the following. Assuming `∀ n, f n < ack a n` and `∀ n, g n < ack b n`, we have:

- `∀ n, pair (f n) (g n) < ack (max a b + 3) n`.
- `∀ n, g (f n) < ack (max a b + 2) n`.
- `∀ n, Nat.rec (f n.unpair.1) (fun (y IH : ℕ) => g (pair n.unpair.1 (pair y IH)))
  n.unpair.2 < ack (max a b + 9) n`.

The last one is evidently the hardest. Using `unpair_add_le`, we reduce it to the more manageable

- `∀ m n, rec (f m) (fun (y IH : ℕ) => g (pair m (pair y IH))) n <
  ack (max a b + 9) (m + n)`.

We then prove this by induction on `n`. Our proof crucially depends on `ack_pair_lt`, which is
applied twice, giving us a constant of `4 + 4`. The rest of the proof consists of simpler bounds
which bump up our constant to `9`.
-/


open Nat

/-- The two-argument Ackermann function, defined so that

- `ack 0 n = n + 1`
- `ack (m + 1) 0 = ack m 1`
- `ack (m + 1) (n + 1) = ack m (ack (m + 1) n)`.

This is of interest as both a fast-growing function, and as an example of a recursive function that
isn't primitive recursive. -/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
  termination_by ack m n => (m, n)
#align ack ack

@[simp]
theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]
                                                 -- 🎉 no goals
#align ack_zero ack_zero

@[simp]
theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw [ack]
                                                              -- 🎉 no goals
#align ack_succ_zero ack_succ_zero

@[simp]
theorem ack_succ_succ (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]
                                                                                    -- 🎉 no goals
#align ack_succ_succ ack_succ_succ

@[simp]
theorem ack_one (n : ℕ) : ack 1 n = n + 2 := by
  induction' n with n IH
  -- ⊢ ack 1 zero = zero + 2
  · rfl
    -- 🎉 no goals
  · simp [IH]
    -- 🎉 no goals
#align ack_one ack_one

@[simp]
theorem ack_two (n : ℕ) : ack 2 n = 2 * n + 3 := by
  induction' n with n IH
  -- ⊢ ack 2 zero = 2 * zero + 3
  · rfl
    -- 🎉 no goals
  · simpa [mul_succ]
    -- 🎉 no goals
#align ack_two ack_two

-- Porting note: re-written to get rid of ack_three_aux
@[simp]
theorem ack_three (n : ℕ) : ack 3 n = 2 ^ (n + 3) - 3 := by
  induction' n with n IH
  -- ⊢ ack 3 zero = 2 ^ (zero + 3) - 3
  · rfl
    -- 🎉 no goals
  · rw [ack_succ_succ, IH, ack_two, Nat.succ_add, Nat.pow_succ 2 (n + 3), mul_comm _ 2,
        Nat.mul_sub_left_distrib, ← Nat.sub_add_comm, two_mul 3, Nat.add_sub_add_right]
    have H : 2 * 3 ≤ 2 * 2 ^ 3 := by norm_num
    -- ⊢ 2 * 3 ≤ 2 * 2 ^ (n + 3)
    apply H.trans
    -- ⊢ 2 * 2 ^ 3 ≤ 2 * 2 ^ (n + 3)
    simp [pow_le_pow]
    -- 🎉 no goals
#align ack_three ack_three

theorem ack_pos : ∀ m n, 0 < ack m n
  | 0, n => by simp
               -- 🎉 no goals
  | m + 1, 0 => by
    rw [ack_succ_zero]
    -- ⊢ 0 < ack m 1
    apply ack_pos
    -- 🎉 no goals
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    -- ⊢ 0 < ack m (ack (m + 1) n)
    apply ack_pos
    -- 🎉 no goals
#align ack_pos ack_pos

theorem one_lt_ack_succ_left : ∀ m n, 1 < ack (m + 1) n
  | 0, n => by simp
               -- 🎉 no goals
  | m + 1, 0 => by
    rw [ack_succ_zero]
    -- ⊢ 1 < ack (m + 1) 1
    apply one_lt_ack_succ_left
    -- 🎉 no goals
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    -- ⊢ 1 < ack (m + 1) (ack (m + 1 + 1) n)
    apply one_lt_ack_succ_left
    -- 🎉 no goals
#align one_lt_ack_succ_left one_lt_ack_succ_left

theorem one_lt_ack_succ_right : ∀ m n, 1 < ack m (n + 1)
  | 0, n => by simp
               -- 🎉 no goals
  | m + 1, n => by
    rw [ack_succ_succ]
    -- ⊢ 1 < ack m (ack (m + 1) n)
    cases' exists_eq_succ_of_ne_zero (ack_pos (m + 1) n).ne' with h h
    -- ⊢ 1 < ack m (ack (m + 1) n)
    rw [h]
    -- ⊢ 1 < ack m (succ h✝)
    apply one_lt_ack_succ_right
    -- 🎉 no goals
#align one_lt_ack_succ_right one_lt_ack_succ_right

theorem ack_strictMono_right : ∀ m, StrictMono (ack m)
  | 0, n₁, n₂, h => by simpa using h
                       -- 🎉 no goals
  | m + 1, 0, n + 1, _h => by
    rw [ack_succ_zero, ack_succ_succ]
    -- ⊢ ack m 1 < ack m (ack (m + 1) n)
    exact ack_strictMono_right _ (one_lt_ack_succ_left m n)
    -- 🎉 no goals
  | m + 1, n₁ + 1, n₂ + 1, h => by
    rw [ack_succ_succ, ack_succ_succ]
    -- ⊢ ack m (ack (m + 1) n₁) < ack m (ack (m + 1) n₂)
    apply ack_strictMono_right _ (ack_strictMono_right _ _)
    -- ⊢ n₁ < n₂
    rwa [add_lt_add_iff_right] at h
    -- 🎉 no goals
  termination_by ack_strictMono_right m x y h => (m, x)
#align ack_strict_mono_right ack_strictMono_right

theorem ack_mono_right (m : ℕ) : Monotone (ack m) :=
  (ack_strictMono_right m).monotone
#align ack_mono_right ack_mono_right

theorem ack_injective_right (m : ℕ) : Function.Injective (ack m) :=
  (ack_strictMono_right m).injective
#align ack_injective_right ack_injective_right

@[simp]
theorem ack_lt_iff_right {m n₁ n₂ : ℕ} : ack m n₁ < ack m n₂ ↔ n₁ < n₂ :=
  (ack_strictMono_right m).lt_iff_lt
#align ack_lt_iff_right ack_lt_iff_right

@[simp]
theorem ack_le_iff_right {m n₁ n₂ : ℕ} : ack m n₁ ≤ ack m n₂ ↔ n₁ ≤ n₂ :=
  (ack_strictMono_right m).le_iff_le
#align ack_le_iff_right ack_le_iff_right

@[simp]
theorem ack_inj_right {m n₁ n₂ : ℕ} : ack m n₁ = ack m n₂ ↔ n₁ = n₂ :=
  (ack_injective_right m).eq_iff
#align ack_inj_right ack_inj_right

theorem max_ack_right (m n₁ n₂ : ℕ) : ack m (max n₁ n₂) = max (ack m n₁) (ack m n₂) :=
  (ack_mono_right m).map_max
#align max_ack_right max_ack_right

theorem add_lt_ack : ∀ m n, m + n < ack m n
  | 0, n => by simp
               -- 🎉 no goals
  | m + 1, 0 => by simpa using add_lt_ack m 1
                   -- 🎉 no goals
  | m + 1, n + 1 =>
    calc
      m + 1 + n + 1 ≤ m + (m + n + 2) := by linarith
                                            -- 🎉 no goals
      _ < ack m (m + n + 2) := add_lt_ack _ _
      _ ≤ ack m (ack (m + 1) n) :=
        ack_mono_right m <| le_of_eq_of_le (by rw [succ_eq_add_one]; ring_nf)
                                               -- ⊢ m + n + 2 = m + 1 + n + 1
                                                                     -- 🎉 no goals
        <| succ_le_of_lt <| add_lt_ack (m + 1) n
      _ = ack (m + 1) (n + 1) := (ack_succ_succ m n).symm
  termination_by add_lt_ack m n => (m, n)
#align add_lt_ack add_lt_ack

theorem add_add_one_le_ack (m n : ℕ) : m + n + 1 ≤ ack m n :=
  succ_le_of_lt (add_lt_ack m n)
#align add_add_one_le_ack add_add_one_le_ack

theorem lt_ack_left (m n : ℕ) : m < ack m n :=
  (self_le_add_right m n).trans_lt <| add_lt_ack m n
#align lt_ack_left lt_ack_left

theorem lt_ack_right (m n : ℕ) : n < ack m n :=
  (self_le_add_left n m).trans_lt <| add_lt_ack m n
#align lt_ack_right lt_ack_right

-- we reorder the arguments to appease the equation compiler
private theorem ack_strict_mono_left' : ∀ {m₁ m₂} (n), m₁ < m₂ → ack m₁ n < ack m₂ n
  | m, 0, n => fun h => (not_lt_zero m h).elim
  | 0, m + 1, 0 => fun _h => by simpa using one_lt_ack_succ_right m 0
                                -- 🎉 no goals
  | 0, m + 1, n + 1 => fun h => by
    rw [ack_zero, ack_succ_succ]
    -- ⊢ n + 1 + 1 < ack m (ack (m + 1) n)
    apply lt_of_le_of_lt (le_trans _ <| add_le_add_left (add_add_one_le_ack _ _) m) (add_lt_ack _ _)
    -- ⊢ n + 1 + 1 ≤ m + (m + 1 + n + 1)
    linarith
    -- 🎉 no goals
  | m₁ + 1, m₂ + 1, 0 => fun h => by
    simpa using ack_strict_mono_left' 1 ((add_lt_add_iff_right 1).1 h)
    -- 🎉 no goals
  | m₁ + 1, m₂ + 1, n + 1 => fun h => by
    rw [ack_succ_succ, ack_succ_succ]
    -- ⊢ ack m₁ (ack (m₁ + 1) n) < ack m₂ (ack (m₂ + 1) n)
    exact
      (ack_strict_mono_left' _ <| (add_lt_add_iff_right 1).1 h).trans
        (ack_strictMono_right _ <| ack_strict_mono_left' n h)
  termination_by ack_strict_mono_left' x y => (x, y)

theorem ack_strictMono_left (n : ℕ) : StrictMono fun m => ack m n := fun _m₁ _m₂ =>
  ack_strict_mono_left' n
#align ack_strict_mono_left ack_strictMono_left

theorem ack_mono_left (n : ℕ) : Monotone fun m => ack m n :=
  (ack_strictMono_left n).monotone
#align ack_mono_left ack_mono_left

theorem ack_injective_left (n : ℕ) : Function.Injective fun m => ack m n :=
  (ack_strictMono_left n).injective
#align ack_injective_left ack_injective_left

@[simp]
theorem ack_lt_iff_left {m₁ m₂ n : ℕ} : ack m₁ n < ack m₂ n ↔ m₁ < m₂ :=
  (ack_strictMono_left n).lt_iff_lt
#align ack_lt_iff_left ack_lt_iff_left

@[simp]
theorem ack_le_iff_left {m₁ m₂ n : ℕ} : ack m₁ n ≤ ack m₂ n ↔ m₁ ≤ m₂ :=
  (ack_strictMono_left n).le_iff_le
#align ack_le_iff_left ack_le_iff_left

@[simp]
theorem ack_inj_left {m₁ m₂ n : ℕ} : ack m₁ n = ack m₂ n ↔ m₁ = m₂ :=
  (ack_injective_left n).eq_iff
#align ack_inj_left ack_inj_left

theorem max_ack_left (m₁ m₂ n : ℕ) : ack (max m₁ m₂) n = max (ack m₁ n) (ack m₂ n) :=
  (ack_mono_left n).map_max
#align max_ack_left max_ack_left

theorem ack_le_ack {m₁ m₂ n₁ n₂ : ℕ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) : ack m₁ n₁ ≤ ack m₂ n₂ :=
  (ack_mono_left n₁ hm).trans <| ack_mono_right m₂ hn
#align ack_le_ack ack_le_ack

theorem ack_succ_right_le_ack_succ_left (m n : ℕ) : ack m (n + 1) ≤ ack (m + 1) n := by
  cases' n with n n
  -- ⊢ ack m (zero + 1) ≤ ack (m + 1) zero
  · simp
    -- 🎉 no goals
  · rw [ack_succ_succ, succ_eq_add_one]
    -- ⊢ ack m (n + 1 + 1) ≤ ack m (ack (m + 1) n)
    apply ack_mono_right m (le_trans _ <| add_add_one_le_ack _ n)
    -- ⊢ n + 1 + 1 ≤ m + 1 + n + 1
    linarith
    -- 🎉 no goals
#align ack_succ_right_le_ack_succ_left ack_succ_right_le_ack_succ_left

-- All the inequalities from this point onwards are specific to the main proof.
private theorem sq_le_two_pow_add_one_minus_three (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) - 3 := by
  induction' n with k hk
  -- ⊢ zero ^ 2 ≤ 2 ^ (zero + 1) - 3
  · norm_num
    -- 🎉 no goals
  · cases' k with k k
    -- ⊢ succ zero ^ 2 ≤ 2 ^ (succ zero + 1) - 3
    · norm_num
      -- 🎉 no goals
    · rw [succ_eq_add_one, add_sq, Nat.pow_succ 2, mul_comm _ 2, two_mul (2 ^ _),
          add_tsub_assoc_of_le, add_comm (2 ^ _), add_assoc]
      · apply Nat.add_le_add hk
        -- ⊢ 2 * (k + 1) * 1 + 1 ^ 2 ≤ 2 ^ (k + 2)
        norm_num
        -- ⊢ 2 * (k + 1) + 1 ≤ 2 ^ (k + 2)
        apply succ_le_of_lt
        -- ⊢ 2 * (k + 1) < 2 ^ (k + 2)
        rw [Nat.pow_succ, mul_comm _ 2, mul_lt_mul_left (zero_lt_two' ℕ)]
        -- ⊢ k + 1 < 2 ^ (k + 1)
        apply lt_two_pow
        -- 🎉 no goals
      · rw [Nat.pow_succ, Nat.pow_succ]
        -- ⊢ 3 ≤ 2 ^ k * 2 * 2
        linarith [one_le_pow k 2 zero_lt_two]
        -- 🎉 no goals

theorem ack_add_one_sq_lt_ack_add_three : ∀ m n, (ack m n + 1) ^ 2 ≤ ack (m + 3) n
  | 0, n => by simpa using sq_le_two_pow_add_one_minus_three (n + 2)
               -- 🎉 no goals
  | m + 1, 0 => by
    rw [ack_succ_zero, ack_succ_zero]
    -- ⊢ (ack m 1 + 1) ^ 2 ≤ ack (m + 3) 1
    apply ack_add_one_sq_lt_ack_add_three
    -- 🎉 no goals
  | m + 1, n + 1 => by
    rw [ack_succ_succ, ack_succ_succ]
    -- ⊢ (ack m (ack (m + 1) n) + 1) ^ 2 ≤ ack (m + 3) (ack (m + 3 + 1) n)
    apply (ack_add_one_sq_lt_ack_add_three _ _).trans (ack_mono_right _ <| ack_mono_left _ _)
    -- ⊢ m + 1 ≤ m + 3 + 1
    linarith
    -- 🎉 no goals
#align ack_add_one_sq_lt_ack_add_three ack_add_one_sq_lt_ack_add_three

theorem ack_ack_lt_ack_max_add_two (m n k : ℕ) : ack m (ack n k) < ack (max m n + 2) k :=
  calc
    ack m (ack n k) ≤ ack (max m n) (ack n k) := ack_mono_left _ (le_max_left _ _)
    _ < ack (max m n) (ack (max m n + 1) k) :=
      ack_strictMono_right _ <| ack_strictMono_left k <| lt_succ_of_le <| le_max_right m n
    _ = ack (max m n + 1) (k + 1) := (ack_succ_succ _ _).symm
    _ ≤ ack (max m n + 2) k := ack_succ_right_le_ack_succ_left _ _
#align ack_ack_lt_ack_max_add_two ack_ack_lt_ack_max_add_two

theorem ack_add_one_sq_lt_ack_add_four (m n : ℕ) : ack m ((n + 1) ^ 2) < ack (m + 4) n :=
  calc
    ack m ((n + 1) ^ 2) < ack m ((ack m n + 1) ^ 2) :=
      ack_strictMono_right m <| pow_lt_pow_of_lt_left (succ_lt_succ <| lt_ack_right m n) zero_lt_two
    _ ≤ ack m (ack (m + 3) n) := ack_mono_right m <| ack_add_one_sq_lt_ack_add_three m n
    _ ≤ ack (m + 2) (ack (m + 3) n) := ack_mono_left _ <| by linarith
                                                             -- 🎉 no goals
    _ = ack (m + 3) (n + 1) := (ack_succ_succ _ n).symm
    _ ≤ ack (m + 4) n := ack_succ_right_le_ack_succ_left _ n
#align ack_add_one_sq_lt_ack_add_four ack_add_one_sq_lt_ack_add_four

theorem ack_pair_lt (m n k : ℕ) : ack m (pair n k) < ack (m + 4) (max n k) :=
  (ack_strictMono_right m <| pair_lt_max_add_one_sq n k).trans <|
    ack_add_one_sq_lt_ack_add_four _ _
#align ack_mkpair_lt ack_pair_lt

/-- If `f` is primitive recursive, there exists `m` such that `f n < ack m n` for all `n`. -/
theorem exists_lt_ack_of_nat_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ m, ∀ n, f n < ack m n := by
  induction' hf with f g hf hg IHf IHg f g hf hg IHf IHg f g hf hg IHf IHg
  -- Zero function:
  · exact ⟨0, ack_pos 0⟩
    -- 🎉 no goals
  -- Successor function:
  · refine' ⟨1, fun n => _⟩
    -- ⊢ succ n < ack 1 n
    rw [succ_eq_one_add]
    -- ⊢ 1 + n < ack 1 n
    apply add_lt_ack
    -- 🎉 no goals
  -- Left projection:
  · refine' ⟨0, fun n => _⟩
    -- ⊢ (fun n => (unpair n).fst) n < ack 0 n
    rw [ack_zero, lt_succ_iff]
    -- ⊢ (fun n => (unpair n).fst) n ≤ n
    exact unpair_left_le n
    -- 🎉 no goals
  -- Right projection:
  · refine' ⟨0, fun n => _⟩
    -- ⊢ (fun n => (unpair n).snd) n < ack 0 n
    rw [ack_zero, lt_succ_iff]
    -- ⊢ (fun n => (unpair n).snd) n ≤ n
    exact unpair_right_le n
    -- 🎉 no goals
  all_goals cases' IHf with a ha; cases' IHg with b hb
  -- Pairing:
  · refine'
      ⟨max a b + 3, fun n =>
        (pair_lt_max_add_one_sq _ _).trans_le <|
          (pow_le_pow_of_le_left (add_le_add_right _ _) 2).trans <|
            ack_add_one_sq_lt_ack_add_three _ _⟩
    rw [max_ack_left]
    -- ⊢ max (f n) (g n) ≤ max (ack a n) (ack b n)
    exact max_le_max (ha n).le (hb n).le
    -- 🎉 no goals
  -- Composition:
  · exact
      ⟨max a b + 2, fun n =>
        (ha _).trans <| (ack_strictMono_right a <| hb n).trans <| ack_ack_lt_ack_max_add_two a b n⟩
  -- Primitive recursion operator:
  · -- We prove this simpler inequality first.
    have :
      ∀ {m n},
        rec (f m) (fun y IH => g <| pair m <| pair y IH) n < ack (max a b + 9) (m + n) := by
      intro m n
      -- We induct on n.
      induction' n with n IH
      -- The base case is easy.
      · apply (ha m).trans (ack_strictMono_left m <| (le_max_left a b).trans_lt _)
        linarith
      · -- We get rid of the first `pair`.
        simp only [ge_iff_le]
        apply (hb _).trans ((ack_pair_lt _ _ _).trans_le _)
        -- If m is the maximum, we get a very weak inequality.
        cases' lt_or_le _ m with h₁ h₁
        · rw [max_eq_left h₁.le]
          exact ack_le_ack (Nat.add_le_add (le_max_right a b) <| by norm_num)
                           (self_le_add_right m _)
        rw [max_eq_right h₁]
        -- We get rid of the second `pair`.
        apply (ack_pair_lt _ _ _).le.trans
        -- If n is the maximum, we get a very weak inequality.
        cases' lt_or_le _ n with h₂ h₂
        · rw [max_eq_left h₂.le, add_assoc]
          exact
            ack_le_ack (Nat.add_le_add (le_max_right a b) <| by norm_num)
              ((le_succ n).trans <| self_le_add_left _ _)
        rw [max_eq_right h₂]
        -- We now use the inductive hypothesis, and some simple algebraic manipulation.
        apply (ack_strictMono_right _ IH).le.trans
        rw [add_succ m, add_succ _ 8, succ_eq_add_one, succ_eq_add_one,
            ack_succ_succ (_ + 8), add_assoc]
        exact ack_mono_left _ (Nat.add_le_add (le_max_right a b) le_rfl)
    -- The proof is now simple.
    exact ⟨max a b + 9, fun n => this.trans_le <| ack_mono_right _ <| unpair_add_le n⟩
    -- 🎉 no goals
#align exists_lt_ack_of_nat_primrec exists_lt_ack_of_nat_primrec

theorem not_nat_primrec_ack_self : ¬Nat.Primrec fun n => ack n n := fun h => by
  cases' exists_lt_ack_of_nat_primrec h with m hm
  -- ⊢ False
  exact (hm m).false
  -- 🎉 no goals
#align not_nat_primrec_ack_self not_nat_primrec_ack_self

theorem not_primrec_ack_self : ¬Primrec fun n => ack n n := by
  rw [Primrec.nat_iff]
  -- ⊢ ¬Nat.Primrec fun n => ack n n
  exact not_nat_primrec_ack_self
  -- 🎉 no goals
#align not_primrec_ack_self not_primrec_ack_self

/-- The Ackermann function is not primitive recursive. -/
theorem not_primrec₂_ack : ¬Primrec₂ ack := fun h =>
  not_primrec_ack_self <| h.comp Primrec.id Primrec.id
#align not_primrec₂_ack not_primrec₂_ack
