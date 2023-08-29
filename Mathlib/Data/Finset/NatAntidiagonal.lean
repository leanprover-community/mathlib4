/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.NatAntidiagonal

#align_import data.finset.nat_antidiagonal from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `Data.List.NatAntidiagonal` and `Data.Multiset.NatAntidiagonal`.
-/

open Function

namespace Finset

namespace Nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`. -/
def antidiagonal (n : ℕ) : Finset (ℕ × ℕ) :=
  ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
#align finset.nat.antidiagonal Finset.Nat.antidiagonal

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ x.1 + x.2 = n := by
  rw [antidiagonal, mem_def, Multiset.Nat.mem_antidiagonal]
  -- 🎉 no goals
#align finset.nat.mem_antidiagonal Finset.Nat.mem_antidiagonal

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp]
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n + 1 := by simp [antidiagonal]
                                                                        -- 🎉 no goals
#align finset.nat.card_antidiagonal Finset.Nat.card_antidiagonal

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} := rfl
#align finset.nat.antidiagonal_zero Finset.Nat.antidiagonal_zero

theorem antidiagonal_succ (n : ℕ) :
    antidiagonal (n + 1) =
      cons (0, n + 1)
        ((antidiagonal n).map
          (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Embedding.refl _)))
        (by simp) := by
            -- 🎉 no goals
  apply eq_of_veq
  -- ⊢ (antidiagonal (n + 1)).val = (cons (0, n + 1) (map (Embedding.prodMap { toFu …
  rw [cons_val, map_val]
  -- ⊢ (antidiagonal (n + 1)).val = (0, n + 1) ::ₘ Multiset.map (↑(Embedding.prodMa …
  · apply Multiset.Nat.antidiagonal_succ
    -- 🎉 no goals
#align finset.nat.antidiagonal_succ Finset.Nat.antidiagonal_succ

theorem antidiagonal_succ' (n : ℕ) :
    antidiagonal (n + 1) =
      cons (n + 1, 0)
        ((antidiagonal n).map
          (Embedding.prodMap (Embedding.refl _) ⟨Nat.succ, Nat.succ_injective⟩))
        (by simp) := by
            -- 🎉 no goals
  apply eq_of_veq
  -- ⊢ (antidiagonal (n + 1)).val = (cons (n + 1, 0) (map (Embedding.prodMap (Embed …
  rw [cons_val, map_val]
  -- ⊢ (antidiagonal (n + 1)).val = (n + 1, 0) ::ₘ Multiset.map (↑(Embedding.prodMa …
  exact Multiset.Nat.antidiagonal_succ'
  -- 🎉 no goals
#align finset.nat.antidiagonal_succ' Finset.Nat.antidiagonal_succ'

theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      cons (0, n + 2)
        (cons (n + 2, 0)
            ((antidiagonal n).map
              (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩
                ⟨Nat.succ, Nat.succ_injective⟩)) <|
          by simp)
             -- 🎉 no goals
        (by simp) := by
            -- 🎉 no goals
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  -- ⊢ cons (0, n + 1 + 1) (cons (↑(Embedding.prodMap { toFun := Nat.succ, inj' :=  …
  rfl
  -- 🎉 no goals
#align finset.nat.antidiagonal_succ_succ' Finset.Nat.antidiagonal_succ_succ'

/-- See also `Finset.map.map_prodComm_antidiagonal`. -/
@[simp] theorem map_swap_antidiagonal {n : ℕ} :
    (antidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = antidiagonal n :=
  eq_of_veq <| by simp [antidiagonal, Multiset.Nat.map_swap_antidiagonal]
                  -- 🎉 no goals
#align finset.nat.map_swap_antidiagonal Finset.Nat.map_swap_antidiagonal

@[simp] theorem map_prodComm_antidiagonal {n : ℕ} :
    (antidiagonal n).map (Equiv.prodComm ℕ ℕ) = antidiagonal n :=
  map_swap_antidiagonal

/-- A point in the antidiagonal is determined by its first co-ordinate. -/
theorem antidiagonal_congr {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ antidiagonal n)
    (hq : q ∈ antidiagonal n) : p = q ↔ p.fst = q.fst := by
  refine' ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((add_right_inj q.fst).mp _)⟩
  -- ⊢ q.fst + p.snd = q.fst + q.snd
  rw [mem_antidiagonal] at hp hq
  -- ⊢ q.fst + p.snd = q.fst + q.snd
  rw [hq, ← h, hp]
  -- 🎉 no goals
#align finset.nat.antidiagonal_congr Finset.Nat.antidiagonal_congr

/-- A point in the antidiagonal is determined by its first co-ordinate (subtype version of
`antidiagonal_congr`). This lemma is used by the `ext` tactic. -/
@[ext] theorem antidiagonal_subtype_ext {n : ℕ} {p q : antidiagonal n} (h : p.val.1 = q.val.1) :
    p = q := Subtype.ext ((antidiagonal_congr p.prop q.prop).mpr h)

theorem antidiagonal.fst_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_add]
  -- ⊢ ∃ c, n = kl.fst + c
  use kl.2
  -- ⊢ n = kl.fst + kl.snd
  rwa [mem_antidiagonal, eq_comm] at hlk
  -- 🎉 no goals
#align finset.nat.antidiagonal.fst_le Finset.Nat.antidiagonal.fst_le

theorem antidiagonal.fst_lt {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.1 < n + 1 :=
  Nat.lt_succ_of_le $ antidiagonal.fst_le hlk

theorem antidiagonal.snd_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.2 ≤ n := by
  rw [le_iff_exists_add]
  -- ⊢ ∃ c, n = kl.snd + c
  use kl.1
  -- ⊢ n = kl.snd + kl.fst
  rwa [mem_antidiagonal, eq_comm, add_comm] at hlk
  -- 🎉 no goals
#align finset.nat.antidiagonal.snd_le Finset.Nat.antidiagonal.snd_le

theorem antidiagonal.snd_lt {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.2 < n + 1 :=
  Nat.lt_succ_of_le $ antidiagonal.snd_le hlk

theorem filter_fst_eq_antidiagonal (n m : ℕ) :
    filter (fun x : ℕ × ℕ ↦ x.fst = m) (antidiagonal n) = if m ≤ n then {(m, n - m)} else ∅ := by
  ext ⟨x, y⟩
  -- ⊢ (x, y) ∈ filter (fun x => x.fst = m) (antidiagonal n) ↔ (x, y) ∈ if m ≤ n th …
  simp only [mem_filter, Nat.mem_antidiagonal]
  -- ⊢ x + y = n ∧ x = m ↔ (x, y) ∈ if m ≤ n then {(m, n - m)} else ∅
  split_ifs with h
  -- ⊢ x + y = n ∧ x = m ↔ (x, y) ∈ {(m, n - m)}
  · simp (config := { contextual := true }) [and_comm, eq_tsub_iff_add_eq_of_le h, add_comm]
    -- 🎉 no goals
  · rw [not_le] at h
    -- ⊢ x + y = n ∧ x = m ↔ (x, y) ∈ ∅
    simp only [not_mem_empty, iff_false_iff, not_and, decide_eq_true_eq]
    -- ⊢ x + y = n → ¬x = m
    exact fun hn => ne_of_lt (lt_of_le_of_lt (le_self_add.trans hn.le) h)
    -- 🎉 no goals
#align finset.nat.filter_fst_eq_antidiagonal Finset.Nat.filter_fst_eq_antidiagonal

theorem filter_snd_eq_antidiagonal (n m : ℕ) :
    filter (fun x : ℕ × ℕ ↦ x.snd = m) (antidiagonal n) = if m ≤ n then {(n - m, m)} else ∅ := by
  have : (fun x : ℕ × ℕ ↦ (x.snd = m)) ∘ Prod.swap = fun x : ℕ × ℕ ↦ x.fst = m := by
    ext; simp
  rw [← map_swap_antidiagonal, filter_map]
  -- ⊢ map { toFun := Prod.swap, inj' := (_ : Injective Prod.swap) } (filter ((fun  …
  simp [this, filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]
  -- 🎉 no goals
#align finset.nat.filter_snd_eq_antidiagonal Finset.Nat.filter_snd_eq_antidiagonal

@[simp] lemma antidiagonal_filter_snd_le_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ a.snd ≤ k) = (antidiagonal k).map
      (Embedding.prodMap ⟨_, add_left_injective (n - k)⟩ (Embedding.refl ℕ)) := by
  ext ⟨i, j⟩
  -- ⊢ (i, j) ∈ filter (fun a => a.snd ≤ k) (antidiagonal n) ↔ (i, j) ∈ map (Embedd …
  suffices : i + j = n ∧ j ≤ k ↔ ∃ a, a + j = k ∧ a + (n - k) = i
  -- ⊢ (i, j) ∈ filter (fun a => a.snd ≤ k) (antidiagonal n) ↔ (i, j) ∈ map (Embedd …
  · simpa
    -- 🎉 no goals
  refine' ⟨fun hi ↦ ⟨k - j, tsub_add_cancel_of_le hi.2, _⟩, _⟩
  -- ⊢ k - j + (n - k) = i
  · rw [add_comm, tsub_add_eq_add_tsub h, ← hi.1, add_assoc, Nat.add_sub_of_le hi.2,
      add_tsub_cancel_right]
  · rintro ⟨l, hl, rfl⟩
    -- ⊢ l + (n - k) + j = n ∧ j ≤ k
    refine' ⟨_, hl ▸ Nat.le_add_left j l⟩
    -- ⊢ l + (n - k) + j = n
    rw [add_assoc, add_comm, add_assoc, add_comm j l, hl]
    -- ⊢ n - k + k = n
    exact Nat.sub_add_cancel h
    -- 🎉 no goals

@[simp] lemma antidiagonal_filter_fst_le_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ a.fst ≤ k) = (antidiagonal k).map
      (Embedding.prodMap (Embedding.refl ℕ) ⟨_, add_left_injective (n - k)⟩) := by
  have aux₁ : fun a ↦ a.fst ≤ k = (fun a ↦ a.snd ≤ k) ∘ (Equiv.prodComm ℕ ℕ).symm := rfl
  -- ⊢ filter (fun a => a.fst ≤ k) (antidiagonal n) = map (Embedding.prodMap (Embed …
  have aux₂ : ∀ i j, (∃ a b, a + b = k ∧ b = i ∧ a + (n - k) = j) ↔
                      ∃ a b, a + b = k ∧ a = i ∧ b + (n - k) = j :=
    fun i j ↦ by rw [exists_comm]; exact exists₂_congr (fun a b ↦ by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  -- ⊢ filter (fun a => a.fst ≤ k) (map (Equiv.toEmbedding (Equiv.prodComm ℕ ℕ)) (a …
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_snd_le_of_le h, map_map]
  -- ⊢ map (Embedding.trans (Embedding.prodMap { toFun := fun x => x + (n - k), inj …
  ext ⟨i, j⟩
  -- ⊢ (i, j) ∈ map (Embedding.trans (Embedding.prodMap { toFun := fun x => x + (n  …
  simpa using aux₂ i j
  -- 🎉 no goals

@[simp] lemma antidiagonal_filter_le_fst_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ k ≤ a.fst) = (antidiagonal (n - k)).map
      (Embedding.prodMap ⟨_, add_left_injective k⟩ (Embedding.refl ℕ)) := by
  ext ⟨i, j⟩
  -- ⊢ (i, j) ∈ filter (fun a => k ≤ a.fst) (antidiagonal n) ↔ (i, j) ∈ map (Embedd …
  suffices : i + j = n ∧ k ≤ i ↔ ∃ a, a + j = n - k ∧ a + k = i
  -- ⊢ (i, j) ∈ filter (fun a => k ≤ a.fst) (antidiagonal n) ↔ (i, j) ∈ map (Embedd …
  · simpa
    -- 🎉 no goals
  refine' ⟨fun hi ↦ ⟨i - k, _, tsub_add_cancel_of_le hi.2⟩, _⟩
  -- ⊢ i - k + j = n - k
  · rw [← Nat.sub_add_comm hi.2, hi.1]
    -- 🎉 no goals
  · rintro ⟨l, hl, rfl⟩
    -- ⊢ l + k + j = n ∧ k ≤ l + k
    refine' ⟨_, Nat.le_add_left k l⟩
    -- ⊢ l + k + j = n
    rw [add_right_comm, hl]
    -- ⊢ n - k + k = n
    exact tsub_add_cancel_of_le h
    -- 🎉 no goals

@[simp] lemma antidiagonal_filter_le_snd_of_le {n k : ℕ} (h : k ≤ n) :
    (antidiagonal n).filter (fun a ↦ k ≤ a.snd) = (antidiagonal (n - k)).map
      (Embedding.prodMap (Embedding.refl ℕ) ⟨_, add_left_injective k⟩) := by
  have aux₁ : fun a ↦ k ≤ a.snd = (fun a ↦ k ≤ a.fst) ∘ (Equiv.prodComm ℕ ℕ).symm := rfl
  -- ⊢ filter (fun a => k ≤ a.snd) (antidiagonal n) = map (Embedding.prodMap (Embed …
  have aux₂ : ∀ i j, (∃ a b, a + b = n - k ∧ b = i ∧ a + k = j) ↔
                      ∃ a b, a + b = n - k ∧ a = i ∧ b + k = j :=
    fun i j ↦ by rw [exists_comm]; exact exists₂_congr (fun a b ↦ by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  -- ⊢ filter (fun a => k ≤ a.snd) (map (Equiv.toEmbedding (Equiv.prodComm ℕ ℕ)) (a …
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_le_fst_of_le h, map_map]
  -- ⊢ map (Embedding.trans (Embedding.prodMap { toFun := fun x => x + k, inj' := ( …
  ext ⟨i, j⟩
  -- ⊢ (i, j) ∈ map (Embedding.trans (Embedding.prodMap { toFun := fun x => x + k,  …
  simpa using aux₂ i j
  -- 🎉 no goals

section EquivProd

/-- The disjoint union of antidiagonals `Σ (n : ℕ), antidiagonal n` is equivalent to the product
    `ℕ × ℕ`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[simps]
def sigmaAntidiagonalEquivProd : (Σn : ℕ, antidiagonal n) ≃ ℕ × ℕ where
  toFun x := x.2
  invFun x := ⟨x.1 + x.2, x, mem_antidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    -- ⊢ (fun x => { fst := x.fst + x.snd, snd := { val := x, property := (_ : x ∈ an …
    rw [mem_antidiagonal] at h
    -- ⊢ (fun x => { fst := x.fst + x.snd, snd := { val := x, property := (_ : x ∈ an …
    exact Sigma.subtype_ext h rfl
    -- 🎉 no goals
  right_inv x := rfl
#align finset.nat.sigma_antidiagonal_equiv_prod Finset.Nat.sigmaAntidiagonalEquivProd
#align finset.nat.sigma_antidiagonal_equiv_prod_symm_apply_fst Finset.Nat.sigmaAntidiagonalEquivProd_symm_apply_fst
#align finset.nat.sigma_antidiagonal_equiv_prod_symm_apply_snd_coe Finset.Nat.sigmaAntidiagonalEquivProd_symm_apply_snd_coe
#align finset.nat.sigma_antidiagonal_equiv_prod_apply Finset.Nat.sigmaAntidiagonalEquivProd_apply

end EquivProd

/-- The set `antidiagonal n` is equivalent to `Fin (n+1)`, via the first projection. --/
@[simps]
def antidiagonalEquivFin (n : ℕ) : antidiagonal n ≃ Fin (n + 1) where
  toFun := fun ⟨⟨i, j⟩, h⟩ ↦ ⟨i, antidiagonal.fst_lt h⟩
  invFun := fun ⟨i, h⟩ ↦ ⟨⟨i, n - i⟩, by
    rw [mem_antidiagonal, add_comm, tsub_add_cancel_iff_le]
    -- ⊢ i ≤ n
    exact Nat.le_of_lt_succ h⟩
    -- 🎉 no goals
  left_inv := by rintro ⟨⟨i, j⟩, h⟩; ext; rfl
                 -- ⊢ (fun x =>
                                     -- ⊢ (↑((fun x =>
                                          -- 🎉 no goals
  right_inv x := rfl

end Nat

end Finset
