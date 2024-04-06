/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Fin-indexed tuples of finsets
-/

open Fintype

namespace Fin
variable {n : ℕ} {α : Fin (n + 1) → Type*}

lemma mem_piFinset_succ {x : ∀ i, α i} {s : ∀ i, Finset (α i)} :
    x ∈ piFinset s ↔ x 0 ∈ s 0 ∧ tail x ∈ piFinset (tail s) := by
  simp only [mem_piFinset, forall_fin_succ, tail]

lemma mem_piFinset_succ' {x : ∀ i, α i} {s : ∀ i, Finset (α i)} :
    x ∈ piFinset s ↔ init x ∈ piFinset (init s) ∧ x (last n) ∈ s (last n) := by
  simp only [mem_piFinset, forall_fin_succ', init]

lemma cons_mem_piFinset_cons {x₀ : α 0} {x : ∀ i : Fin n, α i.succ}
    {s₀ : Finset (α 0)} {s : ∀ i : Fin n, Finset (α i.succ)} :
    cons x₀ x ∈ piFinset (cons s₀ s) ↔ x₀ ∈ s₀ ∧ x ∈ piFinset s := by
  simp_rw [mem_piFinset_succ, cons_zero, tail_cons]

lemma snoc_mem_piFinset_snoc {x : ∀ i : Fin n, α i.castSucc} {xₙ : α (.last n)}
    {s : ∀ i : Fin n, Finset (α i.castSucc)} {sₙ : Finset (α $ .last n)} :
    snoc x xₙ ∈ piFinset (snoc s sₙ) ↔ x ∈ piFinset s ∧ xₙ ∈ sₙ := by
  simp_rw [mem_piFinset_succ', init_snoc, snoc_last]

end Fin
