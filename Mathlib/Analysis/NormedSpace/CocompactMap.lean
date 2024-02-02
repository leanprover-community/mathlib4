/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Topology.ContinuousFunction.CocompactMap
import Mathlib.Analysis.NormedSpace.Basic

/-!
# CocompactMap

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Filter

variable {𝕜 E F 𝓕 : Type*}
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
  [ProperSpace E] [ProperSpace F]

variable {f : 𝓕}

theorem closedBall_compl_subset_of_mem_cocompact {s : Set E} (hs : s ∈ cocompact E) :
    ∃ (r : ℝ), (Metric.closedBall 0 r)ᶜ ⊆ s := by
  rw [mem_cocompact] at hs
  rcases hs with ⟨t, ht, htcs⟩
  rcases ht.isBounded.subset_closedBall 0 with ⟨r, hr⟩
  use r
  exact (Set.compl_subset_compl.mpr hr).trans htcs

theorem mem_cocompact_of_closedBall_compl_subset {s : Set E}
    (h : ∃ (r : ℝ), (Metric.closedBall 0 r)ᶜ ⊆ s) : s ∈ cocompact E := by
  rw [mem_cocompact]
  rcases h with ⟨r, h⟩
  exact ⟨Metric.closedBall 0 r, isCompact_closedBall 0 r, h⟩

theorem norm_le [CocompactMapClass 𝓕 E F] (ε : ℝ) :
    ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ε < ‖f x‖ := by
  have h := cocompact_tendsto f
  rw [tendsto_def] at h
  specialize h (Metric.closedBall 0 ε)ᶜ (mem_cocompact_of_closedBall_compl_subset ⟨ε, rfl.subset⟩)
  rcases closedBall_compl_subset_of_mem_cocompact h with ⟨r, hr⟩
  use r
  intro x hx
  suffices x ∈ f⁻¹' (Metric.closedBall 0 ε)ᶜ by aesop
  apply hr
  simp [hx]

def Function.funLike : FunLike (E → F) E F where
  coe := id
  coe_injective' := Function.injective_id

theorem tendsto_cocompact_of_norm [iF : FunLike 𝓕 E F]
    (h : ∀ ε : ℝ, ∃ r : ℝ, ∀ (x : E) (_hx : r < ‖x‖), ε < ‖f x‖) :
    Tendsto f (cocompact E) (cocompact F) := by
  rw [tendsto_def]
  intro s hs
  rcases closedBall_compl_subset_of_mem_cocompact hs with ⟨ε, hε⟩
  rcases h ε with ⟨r, hr⟩
  apply mem_cocompact_of_closedBall_compl_subset
  use r
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply hε
  simp [hr x hx]

def toCocompactMapClass_of_norm [ContinuousMapClass 𝓕 E F]
    (h : ∀ (f : 𝓕) (ε : ℝ), ∃ r : ℝ, ∀ (x : E) (_hx : r < ‖x‖), ε < ‖f x‖) :
    CocompactMapClass 𝓕 E F where
  cocompact_tendsto f := tendsto_cocompact_of_norm (h f)

theorem foo_tendsto_cocompact [ProperSpace 𝕜] [BoundedSMul 𝕜 E] {x : E} (hx : x ≠ 0) (c : E) :
    Tendsto (· • x + c) (cocompact 𝕜) (cocompact E) := by
  apply tendsto_cocompact_of_norm (iF := Function.funLike)
  intro ε
  use (‖c‖ + ε)/‖x‖
  intro r hr
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [div_lt_iff hx'] at hr
  have : ε < ‖r‖ * ‖x‖ - ‖c‖ := by linarith
  apply lt_of_lt_of_le this
  rw [sub_le_iff_le_add, ← norm_smul]
  apply norm_le_add_norm_add

def foo [ProperSpace 𝕜] [BoundedSMul 𝕜 E] (x c : E) (hx : x ≠ 0) : CocompactMap 𝕜 E where
  toFun := fun r ↦ r • x + c
  cocompact_tendsto' := foo_tendsto_cocompact hx c
