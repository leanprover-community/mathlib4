/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Mahler basis of continuous functions

In this file we introduce the Mahler basis function `mahler k`, for `k : ℕ`, which is the unique
continuous map `ℤ_[p] → ℚ_[p]` agreeing with `n ↦ n.choose k` for `n ∈ ℕ`.

In future PR's, we will show that these functions give a Banach basis for the space of continuous
maps `ℤ_[p] → ℚ_[p]`.

## References

* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]
-/

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/--
The `k`-th Mahler basis function, i.e. the unique continuous function `ℤ_[p] → ℚ_[p]`
agreeing with `n ↦ n.choose k` for `n ∈ ℕ`. See [colmez2010], §1.2.1.
-/
noncomputable def mahler (k : ℕ) : C(ℤ_[p], ℚ_[p]) where
  toFun x := (∏ i in range k, (x.1 - i)) / k.factorial
  continuous_toFun := (continuous_finset_prod _ fun _ _ ↦
    (continuous_sub_right _).comp' continuous_subtype_val).div_const _

/-- The function `mahler k` extends `n ↦ n.choose k` on `ℕ`. -/
lemma mahler_natCast_eq (k n : ℕ) : mahler k (n : ℤ_[p]) = n.choose k := by
  rw [mahler, ContinuousMap.coe_mk, div_eq_iff (mod_cast Nat.factorial_ne_zero k),
    mul_comm, ← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose n k,
    Nat.descFactorial_eq_prod_range]
  by_cases hkn : k ≤ n
  · simp only [Nat.cast_prod]
    apply prod_congr rfl (fun i hi ↦ (Nat.cast_sub ?_).symm)
    exact (Finset.mem_range.mp hi).le.trans hkn
  · -- show there's a zero term in both products
    simp only [Nat.cast_prod]
    rw [prod_eq_zero (mem_range.mpr (not_le.mp hkn)) (sub_self (n : ℚ_[p]))]
    rw [prod_eq_zero (mem_range.mpr (not_le.mp hkn)) (mod_cast (Nat.sub_self n))]

/--
The uniform norm of the `k`-th Mahler basis function is 1, for every `k`.
-/
@[simp] lemma norm_mahler_eq (k : ℕ) : ‖(mahler k : C(ℤ_[p], ℚ_[p]))‖ = 1 := by
  apply le_antisymm
  · -- Hard direction: show all values have norm ≤ 1
    refine (mahler k).norm_le_of_nonempty.mpr fun x ↦ ?_
    -- find `n : ℕ` such that `‖mahler k x - mahler k n‖ ≤ 1`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖mahler k x - mahler k n‖ ≤ 1 := by
      simp only [← dist_eq_norm_sub']
      obtain ⟨δ, hδp, hδ⟩ := Metric.continuousAt_iff.mp ((mahler k).continuousAt x) 1 one_pos
      obtain ⟨n, hn'⟩ := PadicInt.denseRange_natCast.exists_dist_lt x hδp
      exact ⟨n, (hδ (dist_comm x n ▸ hn')).le⟩
    -- use ultrametric property to show that `‖mahler k n‖ ≤ 1` implies `‖mahler k x‖ ≤ 1`
    rw [← sub_add_cancel (mahler k x) (mahler k n)]
    refine (IsUltrametricDist.norm_add_le_max _ (mahler k (n : ℤ_[p]))).trans (max_le hn ?_)
    -- finish using the fact that `mahler k n ∈ ℕ`
    simpa only [mahler_natCast_eq, ← PadicInt.coe_natCast, ← PadicInt.norm_def]
      using PadicInt.norm_le_one _
  · -- Easy direction: show norm 1 is attained at `x = k`
    refine (le_of_eq ?_).trans ((mahler k).norm_coe_le_norm k)
    rw [mahler_natCast_eq, Nat.choose_self, Nat.cast_one, norm_one]
