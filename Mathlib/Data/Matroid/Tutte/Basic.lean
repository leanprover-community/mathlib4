/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Minor.Basic
import Mathlib.Data.Matroid.Rank.ENat
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Tactic.Ring

namespace Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {R : Type*} [CommRing R] (x y : R) {e : α}

variable (M) in
noncomputable def tutte.summand (s : Set α) : R :=
  (x - 1)^(M.eRank.toNat - (M.eRk s).toNat) * (y - 1)^(s.ncard - (M.eRk s).toNat)
-- probably there is a nicer way to define the summands using `relRank`, but this is not yet in
-- mathlib


variable (M) in
noncomputable def tutte : R := ∑ᶠ s ∈ M.E.powerset, tutte.summand M x y s

namespace tutte

theorem summand.contract_isNonloop (h : M.IsNonloop e) (s : Set α) (hs : s ∈ 𝒫 (M.E \ {e})) :
    summand M x y (insert e s) = summand (M ／ {e}) x y s := sorry

theorem summand.contract_isLoop (h : M.IsLoop e) (s : Set α) (hs : s ∈ 𝒫 (M.E \ {e})) :
    summand M x y (insert e s) = (y - 1) * summand (M ／ {e}) x y s := sorry

theorem summand.delete_not_isColoop (h : ¬ M.IsColoop e) (s : Set α) (hs : s ∈ 𝒫 (M.E \ {e})) :
    summand M x y s = summand (M ＼ {e}) x y s := sorry

theorem summand.delete_isColoop (h : M.IsColoop e) (s : Set α) (hs : s ∈ 𝒫 (M.E \ {e})) :
    summand M x y s = (x - 1) * summand (M ＼ {e}) x y s := sorry


theorem delete_isLoop (h : M.IsLoop e) : tutte M x y = y * (tutte (M ＼ {e}) x y) := by
  simp_rw [tutte, finsum_mem_powerset_diff_elem M.ground_finite h.mem_ground]
  rw [finsum_mem_congr rfl (summand.contract_isLoop x y h),
    finsum_mem_congr rfl (summand.delete_not_isColoop x y h.not_isColoop)]
  rw [contract_eq_delete_of_subset_loops, ← mul_finsum_mem]
  · rw [delete_ground]
    ring1
  · exact (M.ground_finite.subset Set.diff_subset).powerset
  · simpa only [Set.singleton_subset_iff] using h

theorem contract_isColoop (h : M.IsColoop e) : tutte M x y = x * (tutte (M ／ {e}) x y) := by
  simp_rw [tutte, finsum_mem_powerset_diff_elem M.ground_finite h.mem_ground]
  rw [finsum_mem_congr rfl (summand.delete_isColoop x y h),
    finsum_mem_congr rfl (summand.contract_isNonloop x y h.isNonloop)]
  rw [contract_eq_delete_of_subset_coloops, ← mul_finsum_mem]
  · rw [delete_ground]
    ring1
  · exact (M.ground_finite.subset Set.diff_subset).powerset
  · simpa only [Set.singleton_subset_iff] using h

theorem delete_contract (h₁ : M.IsNonloop e) (h₂ : ¬ M.IsColoop e) :
    tutte M x y = tutte (M ＼ {e}) x y + (tutte (M ／ {e}) x y) := by
  simp_rw [tutte, finsum_mem_powerset_diff_elem M.ground_finite h₁.mem_ground]
  rw [finsum_mem_congr rfl (summand.contract_isNonloop x y h₁),
    finsum_mem_congr rfl (summand.delete_not_isColoop x y h₂),
    delete_ground, contract_ground]

theorem emptyOn : tutte (emptyOn α) x y = 1 := by simp [tutte, summand, eRank_emptyOn]


end tutte
end Matroid
