/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sqrt

/-!
# The arithmetic-geometric mean

Starting with two nonnegative real numbers, repeatedly replace them with their arithmetic and
geometric means. By the AM-GM inequality, the smaller number (geometric mean) will monotonically
increase and the larger number (arithmetic mean) will monotonically decrease.

The two monotone sequences converge to the same limit – the arithmetic-geometric mean (AGM).
This file defines the AGM in the `NNReal` namespace and proves some of its basic properties.

## References

* https://en.wikipedia.org/wiki/Arithmetic–geometric_mean
-/

@[expose] public section

namespace NNReal

/-- The AM–GM inequality for two `NNReal`s, with means in canonical form. -/
lemma sqrt_mul_le_half_add (x y : ℝ≥0) : sqrt (x * y) ≤ (x + y) / 2 := by
  rw [sqrt_le_iff_le_sq, div_pow, le_div_iff₀' (by positivity), ← mul_assoc]
  norm_num
  exact four_mul_le_sq_add ..

open Function

/-- One step of the iteration defining the arithmetic-geometric mean. -/
noncomputable def agmStep (ga : ℝ≥0 × ℝ≥0) : ℝ≥0 × ℝ≥0 :=
  (sqrt (ga.1 * ga.2), (ga.1 + ga.2) / 2)

variable {g a : ℝ≥0} (h : g ≤ a)

lemma agmStep_iterate_comm {n : ℕ} (hn : n ≠ 0) : agmStep^[n] (g, a) = agmStep^[n] (a, g) := by
  rw [← Nat.sub_one_add_one hn, iterate_add, iterate_one, comp_apply]
  congr 1
  simp only [agmStep, add_comm, mul_comm]

section

include h

lemma agmStep_bounds :
    g ≤ (agmStep (g, a)).1 ∧ (agmStep (g, a)).1 ≤ (agmStep (g, a)).2 ∧ (agmStep (g, a)).2 ≤ a := by
  simp only [agmStep]
  refine ⟨?_, sqrt_mul_le_half_add .., ?_⟩
  · nth_rw 1 [sqrt_mul, ← mul_self_sqrt g]
    gcongr
  · rw [add_div]
    nth_rw 2 [← add_halves a]
    gcongr

lemma agmStep_iterate_bounds (n : ℕ) :
    g ≤ (agmStep^[n] (g, a)).1 ∧ (agmStep^[n] (g, a)).1 ≤ (agmStep^[n] (g, a)).2 ∧
    (agmStep^[n] (g, a)).2 ≤ a := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [iterate_succ', comp_apply]
    obtain ⟨i₁, i₂, i₃⟩ := agmStep_bounds ih.2.1
    exact ⟨ih.1.trans i₁, i₂, i₃.trans ih.2.2⟩

lemma agmStep_iterate_fst_monotone : Monotone fun n ↦ (agmStep^[n] (g, a)).1 := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [iterate_succ', comp_apply]
  exact (agmStep_bounds (agmStep_iterate_bounds h n).2.1).1

lemma agmStep_iterate_snd_antitone : Antitone fun n ↦ (agmStep^[n] (g, a)).2 := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [iterate_succ', comp_apply]
  exact (agmStep_bounds (agmStep_iterate_bounds h n).2.1).2.2

lemma agmStep_iterate_fst_le (n : ℕ) : (agmStep^[n] (g, a)).1 ≤ a := by
  obtain ⟨-, i₂, i₃⟩ := agmStep_iterate_bounds h n
  exact i₂.trans i₃

lemma le_agmStep_iterate_snd (n : ℕ) : g ≤ (agmStep^[n] (g, a)).2 := by
  obtain ⟨i₁, i₂, -⟩ := agmStep_iterate_bounds h n
  exact i₁.trans i₂

lemma bddAbove_range_agmStep_iterate_fst : BddAbove (Set.range fun n ↦ (agmStep^[n] (g, a)).1) := by
  rw [bddAbove_def]
  exact ⟨a, by simpa using agmStep_iterate_fst_le h⟩

lemma bddBelow_range_agmStep_iterate_snd : BddBelow (Set.range fun n ↦ (agmStep^[n] (g, a)).2) := by
  rw [bddBelow_def]
  exact ⟨g, by simpa using le_agmStep_iterate_snd h⟩

end

lemma agmStep_iterate_zero {n : ℕ} : agmStep^[n] (0, a) = (0, a * 2⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [iterate_succ', comp_apply, agmStep, ih, zero_mul, sqrt_zero, zero_add]
    congr
    ring

lemma agmStep_iterate_mul {k : ℝ≥0} {n : ℕ} :
    agmStep^[n] (k * g, k * a) = k • agmStep^[n] (g, a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [iterate_succ', comp_apply, ih, agmStep, Prod.smul_fst, Prod.smul_snd]
    rw [smul_mul_smul, smul_eq_mul, sqrt_mul, sqrt_mul_self, ← smul_eq_mul,
      ← smul_add, smul_div_assoc, Prod.smul_mk]

open Filter Topology

lemma tendsto_agmStep_iterate_zero :
    Tendsto (fun n ↦ (agmStep^[n] (0, a)).1) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ (agmStep^[n] (0, a)).2) atTop (𝓝 0) := by
  simp_rw [agmStep_iterate_zero, tendsto_const_nhds_iff]
  rw [true_and, ← mul_zero a]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)).const_mul a

/-- Iterating `agmStep` drives both components towards a common value. -/
lemma exists_tendsto_agmStep_iterate :
    ∃ M, Tendsto (fun n ↦ (agmStep^[n] (g, a)).1) atTop (𝓝 M) ∧
      Tendsto (fun n ↦ (agmStep^[n] (g, a)).2) atTop (𝓝 M) := by
  wlog h : g ≤ a
  · rw [not_le] at h
    obtain ⟨M, hM₁, hM₂⟩ := this h.le
    refine ⟨M, hM₁.congr' ?_, hM₂.congr' ?_⟩
    all_goals
      rw [EventuallyEq, eventually_atTop]
      refine ⟨1, fun n hn ↦ ?_⟩
      rw [agmStep_iterate_comm (Nat.ne_zero_of_lt hn)]
  rcases (zero_le g).eq_or_lt with gzero | gpos
  · subst gzero
    exact ⟨0, tendsto_agmStep_iterate_zero⟩
  have bdd_g := bddAbove_range_agmStep_iterate_fst h
  have tendsto_g := tendsto_atTop_ciSup (agmStep_iterate_fst_monotone h) bdd_g
  set M := ⨆ n, (agmStep^[n] (g, a)).1
  refine ⟨M, tendsto_g, ?_⟩
  have a_rearrangement (n : ℕ) :
      (agmStep^[n] (g, a)).2 = (agmStep^[n + 1] (g, a)).1 ^ 2 / (agmStep^[n] (g, a)).1 := by
    simp_rw [iterate_succ', comp_apply, agmStep, sq_sqrt]
    rw [mul_div_cancel_left₀ _ (gpos.trans_le (agmStep_iterate_bounds h n).1).ne']
  simp_rw [a_rearrangement]
  rw [← mul_self_div_self M, ← sq]
  refine (Tendsto.pow ?_ 2).div tendsto_g (gpos.trans_le (le_ciSup bdd_g 0)).ne'
  exact (tendsto_add_atTop_iff_nat 1).mpr tendsto_g

/-- The arithmetic-geometric mean of two `NNReal`s. -/
noncomputable def agm (x y : ℝ≥0) : ℝ≥0 :=
  (@exists_tendsto_agmStep_iterate x y).choose

variable {x y : ℝ≥0}

lemma agm_comm : agm x y = agm y x := by
  have tM := (@exists_tendsto_agmStep_iterate x y).choose_spec.1
  have tM' := (@exists_tendsto_agmStep_iterate y x).choose_spec.1
  have eeq : (fun n ↦ (agmStep^[n] (x, y)).1) =ᶠ[atTop] fun n ↦ (agmStep^[n] (y, x)).1 := by
    rw [EventuallyEq, eventually_atTop]
    refine ⟨1, fun n hn ↦ ?_⟩
    rw [agmStep_iterate_comm (Nat.ne_zero_of_lt hn)]
  exact tendsto_nhds_unique (tM.congr' eeq) tM'

lemma agm_mem_Icc_of_le (h : x ≤ y) : agm x y ∈ Set.Icc x y := by
  unfold agm
  set M := (@exists_tendsto_agmStep_iterate x y).choose
  obtain ⟨lM, uM⟩ := (@exists_tendsto_agmStep_iterate x y).choose_spec
  change Tendsto _ _ (𝓝 M) at lM uM
  have bddAbove_fst := bddAbove_range_agmStep_iterate_fst h
  have eM₁ := tendsto_nhds_unique lM <|
    tendsto_atTop_ciSup (agmStep_iterate_fst_monotone h) bddAbove_fst
  have bddBelow_snd := bddBelow_range_agmStep_iterate_snd h
  have eM₂ := tendsto_nhds_unique uM <|
    tendsto_atTop_ciInf (agmStep_iterate_snd_antitone h) bddBelow_snd
  exact ⟨eM₁ ▸ le_ciSup bddAbove_fst 0, eM₂ ▸ ciInf_le bddBelow_snd 0⟩

lemma agm_mem_uIcc : agm x y ∈ Set.uIcc x y := by
  wlog h : x ≤ y
  · rw [not_le] at h
    specialize this h.le
    rwa [Set.uIcc_comm, agm_comm]
  rw [Set.uIcc_of_le h]
  exact agm_mem_Icc_of_le h

lemma agm_self : agm x x = x := by
  simpa using agm_mem_Icc_of_le le_rfl

lemma agm_zero_left : agm 0 x = 0 :=
  tendsto_nhds_unique (@exists_tendsto_agmStep_iterate 0 x).choose_spec.1
    (@tendsto_agmStep_iterate_zero x).1

lemma agm_zero_right : agm x 0 = 0 := by
  rw [agm_comm, agm_zero_left]

/-- The AGM is unchanged if `x` and `y` are replaced by their geometric and arithmetic means. -/
lemma agm_eq_agm_geometric_arithmetic_means : agm x y = agm (sqrt (x * y)) ((x + y) / 2) := by
  let M := (@exists_tendsto_agmStep_iterate x y).choose
  let M' := (@exists_tendsto_agmStep_iterate (agmStep (x, y)).1 (agmStep (x, y)).2).choose
  change M = M'
  have tM : Tendsto _ _ (𝓝 M) := (@exists_tendsto_agmStep_iterate x y).choose_spec.1
  have tM' : Tendsto _ _ (𝓝 M') :=
    (@exists_tendsto_agmStep_iterate (agmStep (x, y)).1 (agmStep (x, y)).2).choose_spec.1
  simp_rw [Prod.mk.eta, ← iterate_succ_apply, Nat.succ_eq_add_one,
    tendsto_add_atTop_iff_nat (f := fun n ↦ (agmStep^[n] (x, y)).1)] at tM'
  exact tendsto_nhds_unique tM tM'

lemma agm_mem_Ioo_of_pos_of_lt (hx : 0 < x) (h : x < y) : agm x y ∈ Set.Ioo x y := by
  rw [agm_eq_agm_geometric_arithmetic_means]
  refine (Set.Icc_subset_Ioo ?_ ?_) <| agm_mem_Icc_of_le (sqrt_mul_le_half_add ..)
  · nth_rw 1 [sqrt_mul, ← mul_self_sqrt x]
    gcongr
  · rw [add_div]
    nth_rw 2 [← add_halves y]
    gcongr

lemma agm_mem_uIoo_of_pos_of_ne (hx : 0 < x) (hy : 0 < y) (h : x ≠ y) : agm x y ∈ Set.uIoo x y := by
  rcases h.lt_or_gt with h | h
  · rw [Set.uIoo_of_lt h]
    exact agm_mem_Ioo_of_pos_of_lt hx h
  · rw [Set.uIoo_of_gt h, agm_comm]
    exact agm_mem_Ioo_of_pos_of_lt hy h

/-- The AGM distributes over multiplication. -/
lemma agm_mul_distrib {k : ℝ≥0} : agm (k * x) (k * y) = k * agm x y := by
  let M := (@exists_tendsto_agmStep_iterate x y).choose
  let M' := (@exists_tendsto_agmStep_iterate (k * x) (k * y)).choose
  change M' = k * M
  have tM : Tendsto _ _ (𝓝 (k • M)) :=
    ((@exists_tendsto_agmStep_iterate x y).choose_spec.1).const_smul k
  have tM' : Tendsto _ _ (𝓝 M') :=
    (@exists_tendsto_agmStep_iterate (k * x) (k * y)).choose_spec.1
  rw [smul_eq_mul] at tM
  simp_rw [agmStep_iterate_mul, Prod.smul_fst] at tM'
  exact tendsto_nhds_unique tM' tM

end NNReal
