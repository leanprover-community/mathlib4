/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.NatAntidiagonal

#align_import data.finset.nat_antidiagonal from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `Data.List.NatAntidiagonal` and `Data.Multiset.NatAntidiagonal`, providing an
instance enabling `Finset.antidiagonal` on `Nat`.
-/

open Function

namespace Finset

namespace Nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`. -/
instance instHasAntidiagonal : HasAntidiagonal ℕ where
  antidiagonal n := ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
  mem_antidiagonal {n} {xy} := by
    rw [mem_def, Multiset.Nat.mem_antidiagonal]

lemma antidiagonal_eq_map (n : ℕ) :
    antidiagonal n = (range (n + 1)).map ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.ext_iff.1 h).1⟩ :=
  rfl

lemma antidiagonal_eq_map' (n : ℕ) :
    antidiagonal n =
      (range (n + 1)).map ⟨fun i ↦ (n - i, i), fun _ _ h ↦ (Prod.ext_iff.1 h).2⟩ := by
  rw [← map_swap_antidiagonal, antidiagonal_eq_map, map_map]; rfl

lemma antidiagonal_eq_image (n : ℕ) :
    antidiagonal n = (range (n + 1)).image fun i ↦ (i, n - i) := by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

lemma antidiagonal_eq_image' (n : ℕ) :
    antidiagonal n = (range (n + 1)).image fun i ↦ (n - i, i) := by
  simp only [antidiagonal_eq_map', map_eq_image, Function.Embedding.coeFn_mk]

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp]
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n + 1 := by simp [antidiagonal]
#align finset.nat.card_antidiagonal Finset.Nat.card_antidiagonal

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
-- nolint as this is for dsimp
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} := rfl
#align finset.nat.antidiagonal_zero Finset.Nat.antidiagonal_zero

theorem antidiagonal_succ (n : ℕ) :
    antidiagonal (n + 1) =
      cons (0, n + 1)
        ((antidiagonal n).map
          (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Embedding.refl _)))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val, map_val]
  apply Multiset.Nat.antidiagonal_succ
#align finset.nat.antidiagonal_succ Finset.Nat.antidiagonal_succ

theorem antidiagonal_succ' (n : ℕ) :
    antidiagonal (n + 1) =
      cons (n + 1, 0)
        ((antidiagonal n).map
          (Embedding.prodMap (Embedding.refl _) ⟨Nat.succ, Nat.succ_injective⟩))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val, map_val]
  exact Multiset.Nat.antidiagonal_succ'
#align finset.nat.antidiagonal_succ' Finset.Nat.antidiagonal_succ'

theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      cons (0, n + 2)
        (cons (n + 2, 0)
            ((antidiagonal n).map
              (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩
                ⟨Nat.succ, Nat.succ_injective⟩)) <|
          by simp)
        (by simp) := by
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  rfl
#align finset.nat.antidiagonal_succ_succ' Finset.Nat.antidiagonal_succ_succ'

theorem antidiagonal.fst_lt {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.1 < n + 1 :=
  Nat.lt_succ_of_le <| antidiagonal.fst_le hlk

theorem antidiagonal.snd_lt {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.2 < n + 1 :=
  Nat.lt_succ_of_le <| antidiagonal.snd_le hlk

@[simp] lemma antidiagonal_filter_snd_le_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ a.snd ≤ k) = (antidiagonal k).map
      (Embedding.prodMap ⟨_, add_left_injective (n - k)⟩ (Embedding.refl ℕ)) := by
  ext ⟨i, j⟩
  suffices i + j = n ∧ j ≤ k ↔ ∃ a, a + j = k ∧ a + (n - k) = i by simpa
  refine ⟨fun hi ↦ ⟨k - j, tsub_add_cancel_of_le hi.2, ?_⟩, ?_⟩
  · rw [add_comm, tsub_add_eq_add_tsub h, ← hi.1, add_assoc, Nat.add_sub_of_le hi.2,
      add_tsub_cancel_right]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, hl ▸ Nat.le_add_left j l⟩
    rw [add_assoc, add_comm, add_assoc, add_comm j l, hl]
    exact Nat.sub_add_cancel h

@[simp] lemma antidiagonal_filter_fst_le_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ a.fst ≤ k) = (antidiagonal k).map
      (Embedding.prodMap (Embedding.refl ℕ) ⟨_, add_left_injective (n - k)⟩) := by
  have aux₁ : fun a ↦ a.fst ≤ k = (fun a ↦ a.snd ≤ k) ∘ (Equiv.prodComm ℕ ℕ).symm := rfl
  have aux₂ : ∀ i j, (∃ a b, a + b = k ∧ b = i ∧ a + (n - k) = j) ↔
                      ∃ a b, a + b = k ∧ a = i ∧ b + (n - k) = j :=
    fun i j ↦ by rw [exists_comm]; exact exists₂_congr (fun a b ↦ by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_snd_le_of_le h, map_map]
  ext ⟨i, j⟩
  simpa using aux₂ i j

@[simp] lemma antidiagonal_filter_le_fst_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ k ≤ a.fst) = (antidiagonal (n - k)).map
      (Embedding.prodMap ⟨_, add_left_injective k⟩ (Embedding.refl ℕ)) := by
  ext ⟨i, j⟩
  suffices i + j = n ∧ k ≤ i ↔ ∃ a, a + j = n - k ∧ a + k = i by simpa
  refine ⟨fun hi ↦ ⟨i - k, ?_, tsub_add_cancel_of_le hi.2⟩, ?_⟩
  · rw [← Nat.sub_add_comm hi.2, hi.1]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, Nat.le_add_left k l⟩
    rw [add_right_comm, hl]
    exact tsub_add_cancel_of_le h

@[simp] lemma antidiagonal_filter_le_snd_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ k ≤ a.snd) = (antidiagonal (n - k)).map
      (Embedding.prodMap (Embedding.refl ℕ) ⟨_, add_left_injective k⟩) := by
  have aux₁ : fun a ↦ k ≤ a.snd = (fun a ↦ k ≤ a.fst) ∘ (Equiv.prodComm ℕ ℕ).symm := rfl
  have aux₂ : ∀ i j, (∃ a b, a + b = n - k ∧ b = i ∧ a + k = j) ↔
                      ∃ a b, a + b = n - k ∧ a = i ∧ b + k = j :=
    fun i j ↦ by rw [exists_comm]; exact exists₂_congr (fun a b ↦ by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_le_fst_of_le h, map_map]
  ext ⟨i, j⟩
  simpa using aux₂ i j

/-- The set `antidiagonal n` is equivalent to `Fin (n+1)`, via the first projection. --/
@[simps]
def antidiagonalEquivFin (n : ℕ) : antidiagonal n ≃ Fin (n + 1) where
  toFun := fun ⟨⟨i, j⟩, h⟩ ↦ ⟨i, antidiagonal.fst_lt h⟩
  invFun := fun ⟨i, h⟩ ↦ ⟨⟨i, n - i⟩, by
    rw [mem_antidiagonal, add_comm, tsub_add_cancel_iff_le]
    exact Nat.le_of_lt_succ h⟩
  left_inv := by rintro ⟨⟨i, j⟩, h⟩; ext; rfl
  right_inv x := rfl

end Nat

end Finset
