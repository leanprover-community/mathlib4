/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Instances.ENNReal

/-!
# A floor function on the extended non-negative reals
-/

section ENNReal_floor

open Filter BigOperators TopologicalSpace Topology Set ENNReal NNReal

namespace ENNReal

/-- The floor function `ℝ≥0∞ → ℝ≥0∞`: the floor of `x` is the supremum of the (coerced) natural
numbers `n` satisfying `n ≤ x`. -/
noncomputable def floor (x : ℝ≥0∞) : ℝ≥0∞ :=
  sSup (Set.range (fun (n : ℕ) ↦ (n : ℝ≥0∞)) ∩ Set.Iic x)

variable {x y : ℝ≥0∞} {n : ℕ}

lemma floor_mono (h : x ≤ y) : x.floor ≤ y.floor :=
  sSup_le_sSup <| by simpa using inter_subset_right.trans <| Iic_subset_Iic.mpr h

/-- The floor function `ℝ≥0∞ → ℝ≥0∞` is increasing. -/
lemma monotone_floor : Monotone floor := fun _ _ h ↦ floor_mono h

lemma floor_le (x : ℝ≥0∞) : floor x ≤ x := by simp [floor]

lemma le_floor (h : n ≤ x) : n ≤ x.floor := le_sSup <| by simp [h]

lemma floor_le_of_lt_add_one (h : x < n + 1) :
    x.floor ≤ n := by
  apply sSup_le
  intro z hz
  simp only [mem_inter_iff, mem_range, mem_Iic] at hz
  obtain ⟨⟨m, m_eq_z⟩, z_le_x⟩ := hz
  have obs := lt_of_le_of_lt z_le_x h
  rw [← m_eq_z] at obs ⊢
  exact_mod_cast show m ≤ n from Nat.le_of_lt_succ (by exact_mod_cast obs)

@[simp] lemma floor_coe_eq (n : ℕ) : floor n = n := le_antisymm (floor_le _) (le_sSup (by simp))

@[simp] lemma floor_zero_eq : floor 0 = 0 := by exact_mod_cast ENNReal.floor_coe_eq 0

@[simp] lemma floor_one_eq_one : floor 1 = 1 := by exact_mod_cast ENNReal.floor_coe_eq 1

/-- There exists a natural number on any closed interval of length one in ℝ≥0. -/
lemma _root_.NNReal.exists_nat_mem_Icc (x : ℝ≥0) : ∃ (n : ℕ), ↑n ∈ Set.Icc x (x+1) := by
  refine ⟨FloorSemiring.ceil x, ⟨Nat.le_ceil x, ?_⟩⟩
  apply le_trans ?_ <| add_le_add (Nat.floor_le (zero_le x)) le_rfl
  exact_mod_cast Nat.ceil_le_floor_add_one x

/-- There exists a natural number on any left-closed right-open interval of length one in ℝ≥0. -/
lemma _root_.NNReal.exists_nat_mem_Ico (x : ℝ≥0) : ∃ (n : ℕ), ↑n ∈ Set.Ico x (x+1) := by
  obtain ⟨m, hm⟩ := exists_nat_mem_Icc x
  by_cases h : m = x + 1
  · exact ⟨m-1, ⟨by simp [h], by simp [h]⟩⟩
  · exact ⟨m, ⟨hm.1, lt_of_le_of_ne hm.2 h⟩⟩

lemma range_nat_coe_inter_Iic_top_eq :
    (Set.range (fun (n : ℕ) ↦ (n : ℝ≥0∞))) ∩ Iic ∞ = (Set.range (fun (n : ℕ) ↦ (n : ℝ≥0∞))) := by
  simp only [Iic_top, inter_univ]

lemma range_nat_coe_inter_Iio_top_eq :
    (Set.range (fun (n : ℕ) ↦ (n : ℝ≥0∞))) ∩ Iio ∞ = (Set.range (fun (n : ℕ) ↦ (n : ℝ≥0∞))) :=
  inter_eq_self_of_subset_left <| fun x ↦ by simpa using fun n hn ↦ hn.symm ▸ coe_lt_top (r := n)

@[simp] lemma floor_top_eq :
    floor ∞ = ∞ := by
  refine eq_top_of_forall_nnreal_le ?_
  intro x
  rw [floor, range_nat_coe_inter_Iic_top_eq]
  obtain ⟨n, hn⟩ := exists_nat_mem_Icc x
  exact le_sSup_of_le (mem_range_self n) (by exact_mod_cast hn.1)

lemma _root_.Nat.setOf_le_ENNReal_eq_Iic (x_ne_top : x ≠ ∞) :
    {n : ℕ | n ≤ x} = Iic (Nat.floor x.toNNReal) := by
  apply subset_antisymm
  · intro n n_le_x
    simp only [floor, mem_Iic]
    apply Nat.le_floor
    simpa using (toNNReal_le_toNNReal coe_ne_top x_ne_top).mpr n_le_x
  · intro n n_le_floor
    simp only [mem_Iic, mem_setOf_eq] at *
    apply le_trans ?_ <| @coe_toNNReal_le_self x
    apply le_trans ?_ <| ENNReal.coe_le_coe.mpr <| Nat.floor_le (a := x.toNNReal) (zero_le _)
    exact_mod_cast n_le_floor

private lemma range_nat_coe_inter_Iic_eq (x : ℝ≥0∞) :
    (Set.range (fun (n : ℕ) ↦ (n : ℝ≥0∞))) ∩ Iic x = (fun (n : ℕ) ↦ (n : ℝ≥0∞)) '' {n | n ≤ x} := by
  apply subset_antisymm
  · intro z hz
    simp only [mem_inter_iff, mem_range, mem_Iic, mem_image, mem_setOf_eq] at *
    obtain ⟨n, hn⟩ := hz.1
    exact ⟨n, ⟨hn ▸ hz.2, hn⟩⟩
  · intro z hz
    simp only [mem_image, mem_setOf_eq, mem_inter_iff, mem_range, mem_Iic] at *
    obtain ⟨n, hn⟩ := hz
    exact ⟨⟨n, hn.2⟩, hn.2.symm ▸ hn.1⟩

lemma floor_eq_natFloor_toNNReal (x_ne_top : x ≠ ∞) :
    floor x = Nat.floor x.toNNReal := by
  rw [floor, range_nat_coe_inter_Iic_eq x, Nat.setOf_le_ENNReal_eq_Iic x_ne_top]
  exact le_antisymm (sSup_le (by simp)) (le_sSup (by simp))

@[simp] lemma floor_floor (x : ℝ≥0∞) :
    x.floor.floor = x.floor := by
  by_cases x_top : x = ∞
  · simp [x_top]
  exact le_antisymm (floor_le _) <|
    ((floor_eq_natFloor_toNNReal x_top).symm ▸
      le_floor (x := x.floor) (n := ⌊x.toNNReal⌋₊)) <| le_refl _

lemma _root_.Nat.bddAbove_le_ennreal {x : ℝ≥0∞} (x_ne_top : x ≠ ∞) :
    BddAbove {n : ℕ | n ≤ x} := by
  use Nat.ceil x.toNNReal
  simp only [mem_upperBounds, mem_setOf_eq]
  intro m hm
  have obs : m ≤ x.toNNReal := (toNNReal_le_toNNReal coe_ne_top x_ne_top).mpr hm
  exact_mod_cast obs.trans <| Nat.le_ceil x.toNNReal

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
  obtain ⟨m, le_m, m_lt⟩ := exists_nat_mem_Ico x.toNNReal
  have x_le_m : x ≤ m := by
    rw [← coe_toNNReal hx]
    exact_mod_cast le_m
  apply le_sSup_of_le ?_ x_le_m
  simpa [coe_toNNReal hx] using ENNReal.coe_le_coe.mpr m_lt.le

lemma lt_floor_add_one {x : ℝ≥0∞} (x_ne_top : x ≠ ∞) : x < floor (x + 1) := by
  apply lt_of_le_of_ne (le_floor_add_one x) ?_
  rw [floor_add_one]
  by_contra con
  apply (lt_self_iff_false (x.floor + 1)).mp
  nth_rw 2 [con]
  rw [floor_add_one, floor_floor]
  exact ENNReal.lt_add_right (add_lt_top.mpr ⟨floor_lt_top x_ne_top, by simp⟩).ne one_ne_zero

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
  exact (floor_le_of_lt_add_one z_lt).trans <| le_of_eq (floor_eq_natFloor_toNNReal x_top).symm

end ENNReal

end ENNReal_floor
