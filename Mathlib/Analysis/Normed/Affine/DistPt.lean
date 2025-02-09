/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

/-!
# Distance between a point and an affine subspace.

This file defines the distance between a point and an affine subspace.

## Main definitions

* `AffineSubspace.distPt`

-/


namespace AffineSubspace

open Function

variable {R V P : Type*} [Ring R] [SeminormedAddCommGroup V] [PseudoMetricSpace P] [Module R V]
variable [NormedAddTorsor V P]

/-- The distance between a point and an affine subspace (defaults to 0 if the subspace is empty). -/
noncomputable def distPt (s : AffineSubspace R P) (p : P) : ℝ := ⨅ (x : s), dist p x

variable (R)

@[simp] lemma distPt_bot (p : P) : (⊥ : AffineSubspace R P).distPt p = 0 :=
  Real.iInf_of_isEmpty _

variable {R}

lemma distPt_nonneg (s : AffineSubspace R P) (p : P) : 0 ≤ s.distPt p :=
  Real.iInf_nonneg (fun _ ↦ dist_nonneg)

lemma distPt_le_dist_of_mem {s : AffineSubspace R P} (p : P) {x : P} (h : x ∈ s) :
    s.distPt p ≤ dist p x := by
  refine ciInf_le ⟨0, ?_⟩ (⟨x, h⟩ : s)
  simp [mem_lowerBounds, dist_nonneg]

@[simp] lemma distPt_of_mem {s : AffineSubspace R P} {p : P} (h : p ∈ s) : s.distPt p = 0 :=
  le_antisymm (dist_self p ▸ distPt_le_dist_of_mem p h) (distPt_nonneg _ _)

lemma distPt_anti {s₁ s₂ : AffineSubspace R P} [Nonempty s₁] (h : s₁ ≤ s₂) (p : P) :
    s₂.distPt p ≤ s₁.distPt p := by
  refine le_ciInf fun x ↦ ciInf_le ⟨0, ?_⟩ (⟨↑x, (le_def' _ _).1 h _ x.property⟩ : s₂)
  simp [mem_lowerBounds, dist_nonneg]

variable (R)

lemma distPt_top (p : P) : (⊤ : AffineSubspace R P).distPt p = 0 := by
  simp

@[simp] lemma distPt_span_singleton (x p : P) : (affineSpan R {x}).distPt p = dist p x :=
  ciInf_subsingleton default _

end AffineSubspace
