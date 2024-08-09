/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Real.ENatENNReal

/-!
# A floor function on the extended non-negative reals
-/

open Filter BigOperators TopologicalSpace Topology Set ENNReal NNReal ENat

section ENat_topology

instance : TopologicalSpace ℕ∞ := TopologicalSpace.induced ENat.toENNReal inferInstance

lemma ENat.continuous_toENNReal : Continuous ENat.toENNReal :=
  continuous_iff_le_induced.mpr fun _ h ↦ h

instance : OrderTopology ℕ∞ := sorry

-- TODO: Move to the appropriate file `Data.ENat.Basic`.
lemma ENat.toENNReal_coe_eq_top_iff {m : ℕ∞} :
    (m : ℝ≥0∞) = ∞ ↔ m = ⊤ := by
  rw [← toENNReal_coe_eq_iff, toENNReal_top]

-- TODO: Move to the appropriate file `Data.ENat.Basic`.
lemma ENat.toENNReal_coe_ne_top_iff {m : ℕ∞} :
    (m : ℝ≥0∞) ≠ ∞ ↔ m ≠ ⊤ :=
  not_iff_not.mpr toENNReal_coe_eq_top_iff

end ENat_topology

section ENNReal_floor

namespace ENNReal

/-- The floor function `ℝ≥0∞ → ℕ∞`: the floor of `x` is the supremum of the extended natural
numbers `n` satisfying `n ≤ x`. -/
noncomputable def floor (x : ℝ≥0∞) : ℕ∞ := sSup {n : ℕ∞ | n ≤ x}

variable {x y : ℝ≥0∞} {n : ℕ} {m : ℕ∞}

lemma floor_eq_sSup_range_toENNReal_inter_Iic :
    floor x = sSup (Set.range (fun (m : ℕ∞) ↦ (m : ℝ≥0∞)) ∩ Iic x) := by
  simp only [floor]
  rw [toENNReal_mono.map_sSup_of_continuousAt ENat.continuous_toENNReal.continuousAt (by simp)]
  congr
  ext m
  simp only [mem_image, mem_setOf_eq, mem_inter_iff, mem_range, mem_Iic]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hx
    refine ⟨⟨n, hn.2⟩, hn.2 ▸ hn.1⟩
  · obtain ⟨n, hn⟩ := hx.1
    refine ⟨n, ⟨hn ▸ hx.2, hn⟩⟩

@[gcongr] lemma floor_mono (h : x ≤ y) : x.floor ≤ y.floor := sSup_le_sSup <| fun _ hx ↦ hx.trans h

/-- The floor function `ℝ≥0∞ → ℝ≥0∞` is increasing. -/
lemma monotone_floor : Monotone floor := fun _ _ h ↦ floor_mono h

lemma floor_le (x : ℝ≥0∞) : floor x ≤ x := by
  simpa only [floor_eq_sSup_range_toENNReal_inter_Iic] using sSup_le fun _ h ↦ h.2

lemma le_floor (h : m ≤ x) : m ≤ x.floor := le_sSup <| by simp [h]

lemma floor_le_of_lt_add_one (h : x < m + 1) :
    x.floor ≤ m := by
  cases' m with l
  · exact le_top
  · apply sSup_le
    intro n hn
    have obs := lt_of_le_of_lt hn h
    cases' n with k
    · exfalso; apply not_top_lt obs
    · exact Nat.cast_le.mpr <| Nat.le_of_lt_succ (by exact_mod_cast obs)

@[simp] lemma floor_coe (n : ℕ∞) :
    floor n = n :=
  le_antisymm (by exact_mod_cast floor_le n) (le_sSup (by simp))

@[simp] lemma floor_zero : floor 0 = 0 := by exact_mod_cast ENNReal.floor_coe 0

@[simp] lemma floor_one : floor 1 = 1 := by exact_mod_cast ENNReal.floor_coe 1

@[simp] lemma floor_top : floor ∞ = ⊤ := floor_coe ⊤

lemma floor_eq_natFloor_toNNReal (x_ne_top : x ≠ ∞) :
    floor x = Nat.floor x.toNNReal := by
  simp only [floor]
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

lemma floor_floor (x : ℝ≥0∞) : (x.floor : ℝ≥0∞).floor = x.floor := by simp

lemma floor_lt_top {x : ℝ≥0∞} (x_ne_top : x ≠ ∞) :
    x.floor < ∞ := by
  simpa [floor_eq_natFloor_toNNReal x_ne_top] using (natCast_ne_top ⌊x.toNNReal⌋₊).symm.lt_top'

@[simp] lemma floor_add_one {x : ℝ≥0∞} :
    (x + 1).floor = x.floor + 1 := by
  by_cases x_top : x = ∞
  · simp [x_top]
  have obs : x + 1 ≠ ⊤ := add_ne_top.mpr ⟨x_top, one_ne_top⟩
  rw [floor_eq_natFloor_toNNReal x_top, floor_eq_natFloor_toNNReal obs]
  norm_cast
  simp [← Nat.floor_add_one (zero_le x.toNNReal), toNNReal_add x_top one_ne_top]

lemma le_floor_add_one (x : ℝ≥0∞) : x ≤ (x + 1).floor := by
  by_cases hx : x = ∞
  · simp [hx]
  have ne_top : x + 1 ≠ ∞ := add_ne_top.mpr ⟨hx, one_ne_top⟩
  simp only [floor_eq_natFloor_toNNReal ne_top, toENNReal_coe]
  nth_rw 1 [← coe_toNNReal hx]
  rw [toNNReal_add hx one_ne_top, one_toNNReal, Nat.floor_add_one (zero_le _)]
  exact_mod_cast (Nat.lt_floor_add_one x.toNNReal).le

lemma lt_floor_add_one {x : ℝ≥0∞} (x_ne_top : x ≠ ∞) : x < floor (x + 1) := by
  apply lt_of_le_of_ne (le_floor_add_one x) ?_
  rw [floor_add_one]
  intro con
  apply (lt_self_iff_false (x.floor + 1)).mp
  nth_rw 2 [con]
  simp only [ENat.toENNReal_add, toENNReal_one, floor_add_one, floor_coe]
  rw [lt_add_one_iff]
  rw [← ENat.toENNReal_coe_ne_top_iff, ENat.toENNReal_add, toENNReal_one]
  exact ENNReal.add_ne_top.mpr ⟨(floor_lt_top x_ne_top).ne, one_ne_top⟩

lemma sub_one_le_floor (x : ℝ≥0∞) : x - 1 ≤ x.floor := by
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
