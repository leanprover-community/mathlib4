/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finsupp.Defs

#align_import data.finsupp.indicator from "leanprover-community/mathlib"@"842328d9df7e96fd90fc424e115679c15fb23a71"

/-!
# Building finitely supported functions off finsets

This file defines `Finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `Finsupp.indicator`: Turns a map from a `Finset` into a `Finsupp` from the entire type.
-/


noncomputable section

open Finset Function

variable {ι α : Type*}

namespace Finsupp

variable [Zero α] {s : Finset ι} (f : ∀ i ∈ s, α) {i : ι}

/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : ι →₀ α
    where
  toFun i :=
    haveI := Classical.decEq ι
    if H : i ∈ s then f i H else 0
  support :=
    haveI := Classical.decEq α
    (s.attach.filter fun i : s => f i.1 i.2 ≠ 0).map (Embedding.subtype _)
  mem_support_toFun i := by
    classical simp
    -- 🎉 no goals
#align finsupp.indicator Finsupp.indicator

theorem indicator_of_mem (hi : i ∈ s) (f : ∀ i ∈ s, α) : indicator s f i = f i hi :=
  @dif_pos _ (id _) hi _ _ _
#align finsupp.indicator_of_mem Finsupp.indicator_of_mem

theorem indicator_of_not_mem (hi : i ∉ s) (f : ∀ i ∈ s, α) : indicator s f i = 0 :=
  @dif_neg _ (id _) hi _ _ _
#align finsupp.indicator_of_not_mem Finsupp.indicator_of_not_mem

variable (s i)

@[simp]
theorem indicator_apply [DecidableEq ι] : indicator s f i = if hi : i ∈ s then f i hi else 0 := by
  simp only [indicator, ne_eq, coe_mk]
  -- ⊢ (if H : i ∈ s then f i H else 0) = if hi : i ∈ s then f i hi else 0
  congr
  -- 🎉 no goals
#align finsupp.indicator_apply Finsupp.indicator_apply

theorem indicator_injective : Injective fun f : ∀ i ∈ s, α => indicator s f := by
  intro a b h
  -- ⊢ a = b
  ext i hi
  -- ⊢ a i hi = b i hi
  rw [← indicator_of_mem hi a, ← indicator_of_mem hi b]
  -- ⊢ ↑(indicator s a) i = ↑(indicator s b) i
  exact FunLike.congr_fun h i
  -- 🎉 no goals
#align finsupp.indicator_injective Finsupp.indicator_injective

theorem support_indicator_subset : ((indicator s f).support : Set ι) ⊆ s := by
  intro i hi
  -- ⊢ i ∈ ↑s
  rw [mem_coe, mem_support_iff] at hi
  -- ⊢ i ∈ ↑s
  by_contra h
  -- ⊢ False
  exact hi (indicator_of_not_mem h _)
  -- 🎉 no goals
#align finsupp.support_indicator_subset Finsupp.support_indicator_subset

lemma single_eq_indicator (b : α) : single i b = indicator {i} (fun _ _ => b) := by
  classical
  ext j
  simp [single_apply, indicator_apply, @eq_comm _ j]
#align finsupp.single_eq_indicator Finsupp.single_eq_indicator

end Finsupp
