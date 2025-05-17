/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.RCLike.Basic

/-!
# A collection of specific limit computations for `RCLike`

-/

open Set Algebra Filter
open scoped Topology

namespace RCLike

variable (𝕜 : Type*) [RCLike 𝕜]

theorem tendsto_inverse_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert tendsto_algebraMap_inverse_atTop_nhds_zero_nat 𝕜
  simp

theorem tendsto_ofReal_cobounded_cobounded :
    Tendsto ofReal (Bornology.cobounded ℝ) (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_norm_cobounded_atTop)

theorem tendsto_ofReal_atTop_cobounded :
    Tendsto ofReal atTop (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atTop_atTop)

theorem tendsto_ofReal_atBot_cobounded :
    Tendsto ofReal atBot (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atBot_atTop)

theorem tendsto_natCast_atTop_cobounded :
    Tendsto Nat.cast atTop (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_natCast_atTop_atTop)

variable {𝕜}

theorem tendsto_add_mul_div_add_mul_atTop_nhds (a b c : 𝕜) {d : 𝕜} (hd : d ≠ 0) :
    Tendsto (fun k : ℕ ↦ (a + c * k) / (b + d * k)) atTop (𝓝 (c / d)) := by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k ↦ (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    field_simp [hx]
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add_const _ _
      apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
      exact tendsto_inverse_atTop_nhds_zero_nat 𝕜

/-- Converts criterion for `g : ℕ → K` to criterion for `g ∘ (⌊⬝⌋₊) : ℝ → K` -/
theorem tendsto_mul_comp_nat_floor_of_tendsto_mul {𝕜} [RCLike 𝕜] {g : ℕ → 𝕜} {t : 𝕜}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun x : ℝ ↦ x * g ⌊x⌋₊) atTop (𝓝 t) := by
  apply tendsto_mul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    (hg.comp tendsto_nat_floor_atTop)
  · exact (tendsto_natCast_atTop_cobounded 𝕜).comp tendsto_nat_floor_atTop
  · apply isBoundedUnder_of_eventually_le
    simpa using ⟨0, fun _ h ↦ mod_cast Nat.abs_floor_sub_le h⟩

end RCLike
