/-
Copyright (c) 2024 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
import Mathlib.Computability.Timed.Merge
import Mathlib.Computability.Timed.Split
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
/-!
# Timed Merge Sort
  This file defines a new version of Merge Sort that, besides sorting the input list, counts the
  number of operations made through the execution of the algorithm. Also, it presents proofs of
  its time complexity and its equivalence to the one defined in Data/List/Sort.lean
## Main Definition:
  - Timed.mergeSort : list α → (list α × ℕ)
## Main Results:
  - Timed.mergeSort_complexity :
      ∀ l : list α, (Timed.mergeSort r l).snd ≤ 8 * l.length * Nat.log 2 l.length
  - Timed.mergeSort_equivalence :
      ∀ l : list α, (Timed.mergeSort r l).fst = list.mergeSort r l
-/

namespace Timed

universe u

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]
local infixl:50 " ≼ " => r

lemma log_pred (n : Nat) : Nat.log 2 n - 1 = Nat.log 2 (n / 2) :=
  match n with
  | 0 => by simp only [Nat.log_zero_right, Nat.zero_div]
  | 1 => by norm_num
  | (n + 2) => by
    rw [Nat.log]
    split_ifs with h
    · simp
    · simp at h

lemma log_2_le (n : Nat) : 2 * Nat.log 2 n ≤ n :=
  match n with
  | 0     => by simp
  | n + 1 => by
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self' n 0
    rw [Nat.log]
    split_ifs
    · have := log_2_le ((n + 1) / 2); omega
    · simp

lemma sub_left_eq (n m k : Nat) (h : n = m) : n - k = m - k := by rw [h]

@[simp] def mergeSort : List α → (List α × Nat)
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: l => by
    cases r₁: List.split (a :: b :: l) with
    | mk l₁ l₂ =>
      have h := @List.length_split_lt α a b l l₁ l₂ r₁
      have := h.1
      have := h.2
      let ⟨sorted_ls₁, m₁⟩ := mergeSort l₁
      let ⟨sorted_ls₂, m₂⟩ := mergeSort l₂
      let ⟨ls', m⟩ := merge (r · ·) sorted_ls₁ sorted_ls₂
      exact ⟨ls', m₁ + m₂ + m⟩
  termination_by l => List.length l

theorem mergeSort_cons_cons {a b} {l l₁ l₂ : List α}
    (h : List.split (a :: b :: l) = (l₁, l₂)) :
    (mergeSort r (a :: b :: l)).1 = (merge (r · ·) (mergeSort r l₁).1 (mergeSort r l₂).1).1 := by
  simp [mergeSort]
  simp at h
  have ⟨h₁, h₂⟩ := h
  rw [← h₁, ← h₂]

theorem mergeSort_equivalence : ∀ (l : List α), (mergeSort r l).fst = List.mergeSort r l
  | []          => by simp [mergeSort]
  | [a]         => by simp [mergeSort]
  | a :: b :: l => by
      have : (l.split.1).length < l.length + 1 := Nat.lt_add_one_of_le (List.length_split_fst_le l)
      have : (l.split.2).length < l.length + 1 := Nat.lt_add_one_of_le (List.length_split_snd_le l)
      rw [ List.mergeSort_cons_cons r (Prod.ext rfl rfl)
         , mergeSort_cons_cons r (Prod.ext rfl rfl)
         , merge_equivalence
         , mergeSort_equivalence (a :: l.split.1)
         , mergeSort_equivalence (b :: l.split.2)
         ]
  termination_by l => List.length l

theorem mergeSort_cons_cons_snd {a b} {l l₁ l₂ : List α}
  (hs : List.split (a :: b :: l) = (l₁, l₂)) :
    (mergeSort r (a :: b :: l)).snd =
    (mergeSort r l₁).snd + (mergeSort r l₂).snd +
    (merge (r · ·) (mergeSort r l₁).fst (mergeSort r l₂).fst).snd := by
  simp at hs
  simp [mergeSort, hs]

theorem mergeSort_complexity : ∀ l : List α,
    (mergeSort r l).snd ≤ 8 * l.length * Nat.log 2 l.length
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by
    cases e : List.split (a :: b :: l) with
    | mk l₁ l₂ =>
      rw [mergeSort_cons_cons_snd r e]
      cases e1 : mergeSort r l₁ with
      | mk ms1 n1 =>
        cases e2 : mergeSort r l₂ with
        | mk ms2 n2 =>
          have split_lt := @List.length_split_lt α a b l l₁ l₂ e
          have := split_lt.1
          have := split_lt.2

          have sortL1Equiv : (mergeSort (r · ·) l₁).1 = List.mergeSort (r · ·) l₁ :=
            by rw [mergeSort_equivalence]
          have sortL2Equiv : (mergeSort (r · ·) l₂).1 = List.mergeSort (r · ·) l₂ :=
            by rw [mergeSort_equivalence]

          have : ms1 = (mergeSort (r · ·) l₁).1 := by rw [e1]
          have ms1Ident : ms1 = (List.mergeSort (r · ·) l₁) := by rw [this, sortL1Equiv]

          have : ms2 = (mergeSort (r · ·) l₂).1 := by rw [e2]
          have ms2Ident : ms2 = (List.mergeSort (r · ·) l₂) := by rw [this, sortL2Equiv]

          have ms1Length : ms1.length = l₁.length := by rw [ms1Ident, List.length_mergeSort]
          have ms2Length : ms2.length = l₂.length := by rw [ms2Ident, List.length_mergeSort]

          have ⟨l₁_small, l₂_small⟩ := split_halves_length e
          simp at l₁_small
          simp at l₂_small

          have ih1 := mergeSort_complexity l₁
          have ih2 := mergeSort_complexity l₂
          rw [e1] at ih1
          simp at ih1
          rw [e2] at ih2
          simp at ih2

          have : n1 + n2 + (merge.loop (r · ·) ms1 ms2 []).2 ≤
                   8 * ((l.length + 3) / 2) * Nat.log 2 ((l.length + 3) / 2) +
                   8 * ((l.length + 2) / 2) * Nat.log 2 ((l.length + 2) / 2) +
                   (l.length + 2) := by
            calc
              n1 + n2 + (merge.loop (r · ·) ms1 ms2 []).2 ≤
              8 * l₁.length * Nat.log 2 l₁.length +
              8 * l₂.length * Nat.log 2 l₂.length + (merge.loop (r · ·) ms1 ms2 []).2
                := by linarith
              _ ≤
              8 * l₁.length * Nat.log 2 l₁.length +
              8 * l₂.length * Nat.log 2 l₂.length + ms1.length + ms2.length
                := by have := merge_loop_complexity (r · ·) ms1 ms2 []
                      linarith
              _ =
              8 * l₁.length * Nat.log 2 l₁.length +
              8 * l₂.length * Nat.log 2 l₂.length + l₁.length + l₂.length
                := by rw [ms1Length, ms2Length]
              _ =
              8 * l₁.length * Nat.log 2 l₁.length + 8 * l₂.length * Nat.log 2 l₂.length +
              (l.length + 1 + 1)
                := by rw [add_assoc, split_lengths (a :: b :: l) l₁ l₂ e]
                      simp
              _ ≤
              8 * ((l.length + 3) / 2) * Nat.log 2 l₁.length +
              8 * l₂.length * Nat.log 2 l₂.length + (l.length + 2)
                := by have : 8 * l₁.length ≤ 8 * ((l.length + 3) / 2) := by omega
                      have := Nat.mul_le_mul_right (Nat.log 2 l₁.length) this
                      linarith
              _ ≤
              8 * ((l.length + 3) / 2) * Nat.log 2 l₁.length +
              8 * ((l.length + 2) / 2) * Nat.log 2 l₂.length + (l.length + 2)
                := by have : 8 * l₂.length ≤ 8 * ((l.length + 2) / 2) := by omega
                      have := Nat.mul_le_mul_right (Nat.log 2 l₂.length) this
                      linarith
              _ ≤
              8 * ((l.length + 3) / 2) * Nat.log 2 ((l.length + 3) / 2) +
              8 * ((l.length + 2) / 2) * Nat.log 2 l₂.length + (l.length + 2)
                := by have : Nat.log 2 l₁.length ≤ Nat.log 2 ((l.length + 3) / 2)
                        := Nat.log_monotone l₁_small
                      have := Nat.mul_le_mul_left (8 * ((l.length + 3) / 2)) this
                      linarith
              _ ≤
              8 * ((l.length + 3) / 2) * Nat.log 2 ((l.length + 3) / 2) +
              8 * ((l.length + 2) / 2) * Nat.log 2 ((l.length + 2) / 2) + (l.length + 2)
                := by have : Nat.log 2 l₂.length ≤ Nat.log 2 ((l.length + 2) / 2)
                        := Nat.log_monotone l₂_small
                      have := Nat.mul_le_mul_left (8 * ((l.length + 2) / 2)) this
                      linarith
          apply le_trans this

          let N := l.length + 2
          show
            8 * ((N + 1) / 2) * Nat.log 2 ((N + 1) / 2) + 8 * (N / 2) * Nat.log 2 (N / 2) + N
            ≤
            8 * N * Nat.log 2 N

          rw [← log_pred N]

          have cancel2 : forall M : Nat, 8 * (M / 2) ≤ 4 * M := by omega
          have simp_sub : forall (M : Nat) , M ≥ 2 * N → M + 2 * N - 4 * N = M - 2 * N := by omega
          have N_ge_2 : 2 ≤ N := by linarith
          calc
            8 * ((N + 1) / 2) * (Nat.log 2 ((N + 1) / 2)) + 8 * (N / 2) * (Nat.log 2 N - 1) + N ≤
            8 * ((N + 1) / 2) * (Nat.log 2 N) + 8 * (N / 2) * (Nat.log 2 N - 1) + N
              := by simp
                    rw [log_pred]
                    have : (N + 1) / 2 ≤ N := by omega
                    have : Nat.log 2 ((N + 1) / 2) ≤ Nat.log 2 N := Nat.log_monotone this
                    exact Nat.mul_le_mul_left _ this
            _ ≤ 4 * (N + 1) * (Nat.log 2 N) + 8 * (N / 2) * (Nat.log 2 N - 1) + N
              := by simp; exact Nat.mul_le_mul_right _ (cancel2 (N + 1))
            _ ≤ 4 * (N + 1) * (Nat.log 2 N) + 4 * N * (Nat.log 2 N - 1) + N
              := by simp; exact Nat.mul_le_mul_right _ (cancel2 N)
            _ = 4 * N * (Nat.log 2 N) + 4 * (Nat.log 2 N) + 4 * N * (Nat.log 2 N - 1) + N
              := by linarith
            _ ≤ 4 * N * (Nat.log 2 N) + 2 * N + 4 * N * (Nat.log 2 N - 1) + N
              := by have := log_2_le N; linarith
            _ = 4 * N * Nat.log 2 N + 2 * N + 4 * N * Nat.log 2 N - (4 * N) + N
              := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
                    simp
                    have : 4 * N ≤ 4 * N * Nat.log 2 N :=
                      by simp; exact Nat.log_pos (by simp) N_ge_2
                    rw [Nat.add_sub_assoc this _]
            _ = 8 * N * Nat.log 2 N + 2 * N - 4 * N + N := by simp; apply sub_left_eq; linarith
            _ = 8 * N * Nat.log 2 N - 2 * N + N := by
              simp
              apply simp_sub (8 * N * Nat.log 2 N)
              have : 1 ≤ Nat.log 2 N := Nat.log_pos (by simp) N_ge_2
              have := Nat.mul_le_mul_left (2 * N) this
              linarith
            _ ≤ 8 * N * Nat.log 2 N := by
              have : N ≤ 8 * N * Nat.log 2 N := by
                have : 1 ≤ Nat.log 2 N := Nat.log_pos (by simp) N_ge_2
                have := Nat.mul_le_mul_left N this
                linarith
              omega
  termination_by l => List.length l

end Timed
