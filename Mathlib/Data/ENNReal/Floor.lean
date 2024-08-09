/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Order.EFloor

/-!
# A floor function on the extended non-negative reals
-/

open Filter BigOperators TopologicalSpace Topology Set ENNReal NNReal ENat

section ENNReal_floor

variable {x y : ℝ≥0∞} {m : ℕ∞} {n : ℕ}

namespace ENNReal

lemma floor_le : (⌊x⌋ᵢ : ℝ≥0∞) ≤ x := ENat.floor_le (zero_le _)

lemma floor_le_of_lt_add_one (h : x < m + 1) :
    ⌊x⌋ᵢ ≤ m := by
  cases' m with l
  · exact le_top
  · apply sSup_le
    intro n hn
    have obs := lt_of_le_of_lt hn h
    cases' n with k
    · exfalso; apply not_top_lt obs
    · exact Nat.cast_le.mpr <| Nat.le_of_lt_succ (by exact_mod_cast obs)

@[simp] lemma floor_coe (n : ℕ∞) :
    ⌊(n : ℝ≥0∞)⌋ᵢ = n :=
  le_antisymm (by exact_mod_cast floor_le (x := n)) (le_sSup (by simp))

@[simp] lemma floor_top : ⌊∞⌋ᵢ = ⊤ := floor_coe ⊤

lemma floor_floor (x : ℝ≥0∞) : ⌊(⌊x⌋ᵢ : ℝ≥0∞)⌋ᵢ = ⌊x⌋ᵢ := by simp

lemma floor_eq_natFloor_toNNReal (x_ne_top : x ≠ ∞) :
    ⌊x⌋ᵢ = ⌊x.toNNReal⌋₊ := by
  apply le_antisymm
  · apply sSup_le
    intro b hb
    by_contra con
    have key : ⌊x.toNNReal⌋₊ + 1 ≤ b := add_one_le_of_lt (not_le.mp con)
    have oops : x.toNNReal < x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_floor_add_one x.toNNReal)
        (show ⌊x.toNNReal⌋₊ + 1 ≤ x from le_trans (by exact_mod_cast key) hb)
    exact (lt_self_iff_false x).mp (by simp [ENNReal.coe_toNNReal x_ne_top] at oops)
  · apply le_sSup
    simp only [mem_setOf_eq, toENNReal_coe]
    apply le_trans _ <| coe_toNNReal_le_self (a := x)
    exact_mod_cast Nat.floor_le (show 0 ≤ x.toNNReal by simp)

lemma floor_lt_top {x : ℝ≥0∞} (x_ne_top : x ≠ ∞) :
    ⌊x⌋ᵢ < ∞ := by
  simpa [floor_eq_natFloor_toNNReal x_ne_top] using (natCast_ne_top ⌊x.toNNReal⌋₊).symm.lt_top'

@[simp] lemma floor_add_one {x : ℝ≥0∞} :
    ⌊x + 1⌋ᵢ = ⌊x⌋ᵢ + 1 := by
  by_cases x_top : x = ∞
  · simp [x_top]
  have obs : x + 1 ≠ ⊤ := add_ne_top.mpr ⟨x_top, one_ne_top⟩
  rw [floor_eq_natFloor_toNNReal x_top, floor_eq_natFloor_toNNReal obs]
  norm_cast
  simp [← Nat.floor_add_one (zero_le x.toNNReal), toNNReal_add x_top one_ne_top]

lemma le_floor_add_one (x : ℝ≥0∞) : x ≤ ⌊x + 1⌋ᵢ := by
  by_cases hx : x = ∞
  · simp [hx]
  have ne_top : x + 1 ≠ ∞ := add_ne_top.mpr ⟨hx, one_ne_top⟩
  simp only [floor_eq_natFloor_toNNReal ne_top, toENNReal_coe]
  nth_rw 1 [← coe_toNNReal hx]
  rw [toNNReal_add hx one_ne_top, one_toNNReal, Nat.floor_add_one (zero_le _)]
  exact_mod_cast (Nat.lt_floor_add_one x.toNNReal).le

lemma lt_floor_add_one {x : ℝ≥0∞} (x_ne_top : x ≠ ∞) : x < ⌊x + 1⌋ᵢ := by
  apply lt_of_le_of_ne (le_floor_add_one x) ?_
  rw [floor_add_one]
  intro con
  apply (lt_self_iff_false (⌊x⌋ᵢ + 1)).mp
  nth_rw 2 [con]
  simp only [ENat.toENNReal_add, toENNReal_one, floor_add_one, floor_coe]
  rw [lt_add_one_iff]
  rw [← ENat.toENNReal_coe_ne_top_iff, ENat.toENNReal_add, toENNReal_one]
  exact ENNReal.add_ne_top.mpr ⟨(floor_lt_top x_ne_top).ne, one_ne_top⟩

lemma sub_one_le_floor (x : ℝ≥0∞) : x - 1 ≤ ⌊x⌋ᵢ := by
  by_cases le_one : x ≤ 1
  · simp [le_one]
  apply (le_floor_add_one (x - 1)).trans (le_of_eq _)
  rw [tsub_add_cancel_of_le (le_of_not_ge le_one)]

/-- The function `floor : ℝ≥0∞ → ℝ≥0∞` is right continuous. -/
lemma rightContinuous_floor (x : ℝ≥0∞) :
    ContinuousWithinAt floor (Set.Ioi x) x := by
  by_cases x_top : x = ∞
  · simp [ContinuousWithinAt, x_top]
  apply (tendsto_congr' ?_).mpr <| tendsto_const_nhds
  filter_upwards [Ico_mem_nhdsWithin_Ioi' (lt_floor_add_one x_top)] with z ⟨x_le_z, z_lt⟩
  apply le_antisymm ?_ (floor_mono x_le_z)
  rw [floor_add_one, floor_eq_natFloor_toNNReal x_top] at z_lt
  apply le_trans _ <| le_of_eq (floor_eq_natFloor_toNNReal x_top).symm
  exact floor_le_of_lt_add_one (by exact_mod_cast z_lt)

end ENNReal

end ENNReal_floor
