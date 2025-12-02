/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff

/-!
# Peano curve
This file proves the existsence of a Peano curve -- continuous surjective map from the interval
`[0, 1]` onto the square `[0, 1] × [0, 1]`.
-/

open scoped unitInterval

/-- There is a continuous function on `ℝ` that maps the Cantor set to the square. -/
lemma exists_long_peano_curve :
    ∃ f : C(ℝ, I × I), Set.SurjOn f cantorSet Set.univ := by
  -- Take a continuous surjection from the Cantor set to the square
  obtain ⟨g, hg1, hg2⟩ := exists_nat_bool_continuous_surjective_of_compact (I × I)
  let g' : C(cantorSet, I × I) :=
    ⟨g ∘ cantorSetHomeomorphNatToBool, Continuous.comp hg1 (Homeomorph.continuous _)⟩
  have hg' : Function.Surjective g' := by
    simp only [ContinuousMap.coe_mk, EquivLike.surjective_comp, g', hg2]
  -- Extend it to whole `ℝ`
  obtain ⟨f, hf⟩ := ContinuousMap.exists_restrict_eq isClosed_cantorSet g'
  use f
  simp only [Set.surjOn_iff_surjective, ← ContinuousMap.coe_restrict, hf, hg']

/-- There is a continuous surjection from the interval to the square. -/
theorem exists_peano_curve :
    ∃ f : C(I, I × I), Function.Surjective f := by
  obtain ⟨f, hf⟩ := exists_long_peano_curve
  -- Restrict the map from `exists_long_peano_curve` to the interval
  use ContinuousMap.restrict I f
  rw [ContinuousMap.coe_restrict, ← Set.surjOn_iff_surjective]
  exact Set.SurjOn.mono cantorSet_subset_unitInterval (by rfl) hf
