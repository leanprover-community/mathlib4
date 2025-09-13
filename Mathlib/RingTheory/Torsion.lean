/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Torsion groups are the union of all subgroups of roots of unity

-/

variable (M : Type*) [CommMonoid M]

lemma CommGroup.mem_torsion_iff_exists_mem_rootsOfUnity {x : Mˣ} :
    x ∈ CommGroup.torsion Mˣ ↔ ∃ n ≠ 0, x ∈ rootsOfUnity n M := by
  simp [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one, Nat.pos_iff_ne_zero]

lemma rootsOfUnity_le_torsion (k : ℕ) [NeZero k] :
    rootsOfUnity k M ≤ CommGroup.torsion Mˣ := by
  intro
  have : k ≠ 0 := NeZero.out
  grind [CommGroup.mem_torsion_iff_exists_mem_rootsOfUnity]

lemma CommGroup.torsion_eq_biSup_rootsOfUnity :
    CommGroup.torsion Mˣ = ⨆ (n : ℕ) (_hn : n ≠ 0), rootsOfUnity n M := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [CommGroup.mem_torsion] at hx
    -- without `(i := ...)`, timeout at `isDefEq`
    rw [Subgroup.mem_biSup_of_directedOn (i := orderOf x) (orderOf_ne_zero_iff.mpr hx)]
    · use orderOf x
      simp [hx]
    · intro a ha b hb
      use a.lcm b
      simp_all [Function.onFun, rootsOfUnity_le_of_dvd, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
  · simp only [iSup_le_iff]
    intro n hn
    have : NeZero n := ⟨hn⟩
    exact rootsOfUnity_le_torsion M n

-- TODO:
-- lemma CommGroup.torsion_eq_rootsOfUnity_finite_card {R : Type*} [CommRing R] [IsDomain R]
--     [Finite (CommGroup.torsion Rˣ)] :
--     CommGroup.torsion Rˣ = rootsOfUnity (Nat.card (CommGroup.torsion Rˣ)) R := by
--   sorry
