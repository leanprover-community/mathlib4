/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Analysis.Complex.Tietze

/-!
# Peano curve

This file proves the existsence of a Peano curve -- continuous sujrective map from the interval
`[0, 1]` to the square `[0, 1] × [0, 1]`.
-/

lemma unitInterval_eq_closedBall : unitInterval = Metric.closedBall 2⁻¹ 2⁻¹ := by
  ext x
  simp only [Set.mem_Icc, Metric.mem_closedBall, dist, abs_le', tsub_le_iff_right, neg_sub,
    le_add_iff_nonneg_right]
  norm_num
  rw [and_comm]

instance : TietzeExtension unitInterval := by
  rw [unitInterval_eq_closedBall]
  apply Metric.instTietzeExtensionClosedBall ℝ
  norm_num

lemma exists_long_peano_curve :
    ∃ f : C(ℝ, unitInterval × unitInterval), Set.univ = f '' cantorSet := by
  obtain ⟨g, hg⟩ := exists_nat_bool_continuous_surjective_of_compact (unitInterval × unitInterval)
  let g' : C(cantorSet, unitInterval × unitInterval) :=
    ⟨g ∘ cantorSet_homeomorph_nat_to_bool, Continuous.comp hg.1 (Homeomorph.continuous _)⟩
  obtain ⟨f, hf⟩ := ContinuousMap.exists_restrict_eq isClosed_cantorSet g'
  use f
  have hg' : Function.Surjective g' := by
    simp only [ContinuousMap.coe_mk, EquivLike.surjective_comp, g']
    exact hg.2
  ext y
  simp only [Set.mem_univ, Set.mem_image, true_iff, g']
  obtain ⟨x, hx⟩ := hg' y
  use x
  have := ContinuousMap.restrict_apply f cantorSet x
  simp [← this, hf, hx]

/-- There is a continuous surjection from the interval to the square. -/
theorem exists_peano_curve :
    ∃ f : C(unitInterval, unitInterval × unitInterval), Function.Surjective f := by
  obtain ⟨f, hf⟩ := exists_long_peano_curve
  let g := ContinuousMap.restrict unitInterval f
  use g
  intro y
  rw [Set.ext_iff] at hf
  specialize hf y
  simp only [Set.mem_univ, Set.mem_image, true_iff] at hf
  obtain ⟨x, hx1, hx2⟩ := hf
  use ⟨x, by simp only [cantorSet, Set.mem_iInter] at hx1; specialize hx1 0; simpa using hx1⟩
  simp [g, hx2]
