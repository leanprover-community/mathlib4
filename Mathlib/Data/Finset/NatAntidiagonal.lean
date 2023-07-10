/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.finset.nat_antidiagonal
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `Data.List.NatAntidiagonal` and `Data.Multiset.NatAntidiagonal`.
-/


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
#align finset.nat.mem_antidiagonal Finset.Nat.mem_antidiagonal

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp]
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n + 1 := by simp [antidiagonal]
#align finset.nat.card_antidiagonal Finset.Nat.card_antidiagonal

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} := rfl
#align finset.nat.antidiagonal_zero Finset.Nat.antidiagonal_zero

theorem antidiagonal_succ (n : ℕ) :
    antidiagonal (n + 1) =
      cons (0, n + 1)
        ((antidiagonal n).map
          (Function.Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Function.Embedding.refl _)))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val, map_val]
  · apply Multiset.Nat.antidiagonal_succ
#align finset.nat.antidiagonal_succ Finset.Nat.antidiagonal_succ

theorem antidiagonal_succ' (n : ℕ) :
    antidiagonal (n + 1) =
      cons (n + 1, 0)
        ((antidiagonal n).map
          (Function.Embedding.prodMap (Function.Embedding.refl _) ⟨Nat.succ, Nat.succ_injective⟩))
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
              (Function.Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩
                ⟨Nat.succ, Nat.succ_injective⟩)) <|
          by simp)
        (by simp) := by
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  rfl
#align finset.nat.antidiagonal_succ_succ' Finset.Nat.antidiagonal_succ_succ'

theorem map_swap_antidiagonal {n : ℕ} :
    (antidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = antidiagonal n :=
  eq_of_veq <| by simp [antidiagonal, Multiset.Nat.map_swap_antidiagonal]
#align finset.nat.map_swap_antidiagonal Finset.Nat.map_swap_antidiagonal

/-- A point in the antidiagonal is determined by its first co-ordinate. -/
theorem antidiagonal_congr {n : ℕ} {p q : ℕ × ℕ} (hp : p ∈ antidiagonal n)
    (hq : q ∈ antidiagonal n) : p = q ↔ p.fst = q.fst := by
  refine' ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((add_right_inj q.fst).mp _)⟩
  rw [mem_antidiagonal] at hp hq
  rw [hq, ← h, hp]
#align finset.nat.antidiagonal_congr Finset.Nat.antidiagonal_congr

theorem antidiagonal.fst_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_add]
  use kl.2
  rwa [mem_antidiagonal, eq_comm] at hlk
#align finset.nat.antidiagonal.fst_le Finset.Nat.antidiagonal.fst_le

theorem antidiagonal.snd_le {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.2 ≤ n := by
  rw [le_iff_exists_add]
  use kl.1
  rwa [mem_antidiagonal, eq_comm, add_comm] at hlk
#align finset.nat.antidiagonal.snd_le Finset.Nat.antidiagonal.snd_le

theorem filter_fst_eq_antidiagonal (n m : ℕ) :
    filter (fun x : ℕ × ℕ ↦ x.fst = m) (antidiagonal n) = if m ≤ n then {(m, n - m)} else ∅ := by
  ext ⟨x, y⟩
  simp only [mem_filter, Nat.mem_antidiagonal]
  split_ifs with h
  · simp (config := { contextual := true }) [and_comm, eq_tsub_iff_add_eq_of_le h, add_comm]
  · rw [not_le] at h
    simp only [not_mem_empty, iff_false_iff, not_and, decide_eq_true_eq]
    exact fun hn => ne_of_lt (lt_of_le_of_lt (le_self_add.trans hn.le) h)
#align finset.nat.filter_fst_eq_antidiagonal Finset.Nat.filter_fst_eq_antidiagonal

theorem filter_snd_eq_antidiagonal (n m : ℕ) :
    filter (fun x : ℕ × ℕ ↦ x.snd = m) (antidiagonal n) = if m ≤ n then {(n - m, m)} else ∅ := by
  have : (fun x : ℕ × ℕ ↦ (x.snd = m)) ∘ Prod.swap = fun x : ℕ × ℕ ↦ x.fst = m := by
    ext; simp
  rw [← map_swap_antidiagonal]
  simp [filter_map, this, filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]
#align finset.nat.filter_snd_eq_antidiagonal Finset.Nat.filter_snd_eq_antidiagonal

section EquivProd

/-- The disjoint union of antidiagonals `Σ (n : ℕ), antidiagonal n` is equivalent to the product
    `ℕ × ℕ`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[simps]
def sigmaAntidiagonalEquivProd : (Σn : ℕ, antidiagonal n) ≃ ℕ × ℕ where
  toFun x := x.2
  invFun x := ⟨x.1 + x.2, x, mem_antidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [mem_antidiagonal] at h
    exact Sigma.subtype_ext h rfl
  right_inv x := rfl
#align finset.nat.sigma_antidiagonal_equiv_prod Finset.Nat.sigmaAntidiagonalEquivProd
#align finset.nat.sigma_antidiagonal_equiv_prod_symm_apply_fst Finset.Nat.sigmaAntidiagonalEquivProd_symm_apply_fst
#align finset.nat.sigma_antidiagonal_equiv_prod_symm_apply_snd_coe Finset.Nat.sigmaAntidiagonalEquivProd_symm_apply_snd_coe
#align finset.nat.sigma_antidiagonal_equiv_prod_apply Finset.Nat.sigmaAntidiagonalEquivProd_apply

end EquivProd

end Nat

end Finset
