/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
-/

open Set Pointwise

variable (E 𝕜 : Type*) {s : Set E}
--variable [NontriviallyNormedField 𝕜]
variable [Semiring 𝕜] [ AddCommGroup E]
variable [Module ℝ E] --[SMulCommClass ℝ 𝕜 E]
variable [UniformSpace E] [UniformAddGroup E] [lcs : LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

theorem totallyBounded_convexHull (hs : TotallyBounded s) :
    TotallyBounded (convexHull ℝ s) := by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, ⟨hV₁, hV₂, hV₃⟩⟩ :=
    (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp lcs W hW₁
  obtain ⟨t, ⟨htf, hts⟩⟩ := (totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hs) _ hV₁
  obtain ⟨t', ⟨htf', hts'⟩⟩ := (totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (IsCompact.totallyBounded (Finite.isCompact_convexHull htf)) _ hV₁)
  use t'
  have en {t₁ V₁ : Set E} : (⋃ y ∈ t₁, y +ᵥ V₁) = t₁ + V₁ := iUnion_add_left_image
  simp_rw [en]
  rw [en] at hts'
  rw [en] at hts
  exact ⟨htf', subset_trans (by
      rw [← add_assoc]
      apply le_trans (by
        rw [ ← Convex.convexHull_eq hV₂]
        exact le_trans (convexHull_mono hts) (convexHull_add_subset)
      ) (add_subset_add_right hts'))
      (add_subset_add_left (subset_trans (add_subset_add hV₃ hV₃) (add_subset_iff.mpr hW₂) ))⟩
