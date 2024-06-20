/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.AddTorsorBases

/-!
# Convex functions are continuous

This file proves that convex functions from a finite dimensional real normed space are locally
lipschitz, in particular continuous.
-/

open AffineBasis FiniteDimensional Metric Set
open scoped Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {x : E}

/-- We can intercalate a polyhedron between a point and one of its neighborhoods. -/
lemma exists_mem_interior_convexHull_finset (hs : s ∈ 𝓝 x) :
    ∃ t : Finset E, x ∈ interior (convexHull ℝ t : Set E) ∧ convexHull ℝ t ⊆ s := by
  classical
  wlog hx : x = 0
  · obtain ⟨t, ht⟩ := this (s := -x +ᵥ s) (by simpa using vadd_mem_nhds (-x) hs) rfl
    use x +ᵥ t
    simpa [subset_set_vadd_iff, mem_vadd_set_iff_neg_vadd_mem, convexHull_vadd, interior_vadd]
      using ht
  subst hx
  obtain ⟨b⟩ := exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (P := E) (by simp)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  set u : Finset E := -Finset.univ.centroid ℝ b +ᵥ Finset.univ.image b
  have hu₀ : 0 ∈ interior (convexHull ℝ u : Set E) := by
    simpa [u, convexHull_vadd, interior_vadd, mem_vadd_set_iff_neg_vadd_mem]
      using b.centroid_mem_interior_convexHull
  have hu : u.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h ↦ by simp [h] at hu₀
  have hunorm : (u : Set E) ⊆ closedBall 0 (u.sup' hu (‖·‖) + 1) := by
    simp only [subset_def, Finset.mem_coe, mem_closedBall, dist_zero_right, ← sub_le_iff_le_add,
      Finset.le_sup'_iff]
    exact fun x hx ↦ ⟨x, hx, by simp⟩
  set ε' : ℝ := ε / 2 / (u.sup' hu (‖·‖) + 1)
  have hε' : 0 < ε' := by
    dsimp [ε']
    obtain ⟨x, hx⟩ := id hu
    have : 0 ≤ u.sup' hu (‖·‖) := Finset.le_sup'_of_le _ hx (norm_nonneg _)
    positivity
  set t : Finset E := ε' • u
  have hε₀ : 0 < ε / 2 := by positivity
  have htnorm : (t : Set E) ⊆ closedBall 0 (ε / 2) := by
    simp [t, Set.set_smul_subset_iff₀ hε'.ne', hε₀.le, _root_.smul_closedBall, abs_of_nonneg hε'.le]
    simpa [ε',  hε₀.ne'] using hunorm
  refine ⟨t, ?_, ?_⟩
  · simpa [t, interior_smul₀, convexHull_smul, zero_mem_smul_set_iff, hε'.ne']
  calc
    convexHull ℝ t ⊆ closedBall 0 (ε / 2) := convexHull_min htnorm (convex_closedBall ..)
    _ ⊆ ball 0 ε := closedBall_subset_ball (by linarith)
    _ ⊆ s := hεs

variable {f : E → ℝ}

protected lemma ConvexOn.locallyLipschitzOn (hf : ConvexOn ℝ s f) :
    LocallyLipschitzOn (intrinsicInterior ℝ s) f := by
  classical
  simp only [LocallyLipschitzOn, mem_intrinsicInterior, coe_affineSpan, Subtype.exists,
    exists_and_right, exists_eq_right, forall_exists_index]
  rintro x hx hx'
  obtain ⟨t, ht⟩ := exists_mem_interior_convexHull_finset $ mem_interior_iff_mem_nhds.1 hx'

  simp only [mem_intrinsicInterior, coe_affineSpan, Subtype.exists, exists_and_right,
    exists_eq_right] at hx
  -- refine isOpen_interior.continuousOn_iff.2 (fun x hx, _),
  -- obtain ⟨t, hxt, hts⟩ := isOpen_interior.exists_mem_interior_convexHull_finset hx,
  -- set M := t.sup' (convexHull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  -- refine metric.continuous_at_iff.2 (fun ε hε, _),
  -- have : f x ≤ M := le_sup_of_mem_convexHull
  --   (hf.subset (hts.trans interior_subset) $ convex_convexHull _ _) (interior_subset hxt),
  -- refine ⟨ε / (M - f x), _, fun y hy, _⟩,
  -- sorry,
  sorry

protected lemma ConcaveOn.locallyLipschitzOn (hf : ConcaveOn ℝ s f) :
    LocallyLipschitzOn (intrinsicInterior ℝ s) f := by simpa using hf.neg.locallyLipschitzOn

protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn

protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn

protected lemma ConvexOn.continuousOn (hf : ConvexOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := hf.locallyLipschitzOn.continuousOn

protected lemma ConcaveOn.continuousOn (hf : ConcaveOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := hf.locallyLipschitzOn.continuousOn

protected lemma ConvexOn.continuous (hf : ConvexOn ℝ univ f) : Continuous f :=
  hf.locallyLipschitz.continuous

protected lemma ConcaveOn.continuous (hf : ConcaveOn ℝ univ f) : Continuous f :=
  hf.locallyLipschitz.continuous
