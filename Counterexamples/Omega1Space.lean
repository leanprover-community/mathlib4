/-
Copyright (c) 2026 Juanjo Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juanjo Madrigal
-/
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# The space `ω₁`

The space `ω₁` with the order topology, a source of many counterexamples in general topology.
We follow [Munkres2000], where this space is denoted `S_Ω`.

## References

* [J. Munkres, *Topology*][Munkres2000]
-/

open scoped Cardinal Ordinal

namespace Omega1Space

/-- The greatest element `Ω`. -/
noncomputable abbrev Ω : Ordinal := ω₁

/-- The set $S_Ω$ -/
abbrev SΩ : Set Ordinal := Set.Iio Ω

/-- The set $\overline{S_Ω}$. -/
abbrev SΩC : Set Ordinal := Set.Iic Ω

/-- The section below an element. -/
abbrev sec : Ordinal → Set Ordinal := Set.Iio


private lemma countable_section_iff_lt_omega (x : Ordinal) : (sec x).Countable <-> x < Ω := by
  rw [<- Cardinal.le_aleph0_iff_set_countable]
  simp [-Ordinal.lift_card, Cardinal.lt_omega_iff_card_lt]

/-- $S_Ω$ is uncountable. -/
theorem uncountable_section : ¬ SΩ.Countable := by
  grind only [!countable_section_iff_lt_omega]

instance : Uncountable SΩ := by
  rw [uncountable_iff_not_countable]
  exact uncountable_section

/-- Each proper section of $S_Ω$ is countable. -/
theorem countable_section (x : SΩ) : (sec x).Countable := by
  grind only [= Set.mem_Iio, !countable_section_iff_lt_omega]

end Omega1Space
