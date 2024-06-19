/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Order.LocalExtr

#align_import analysis.convex.extrema from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/


variable {E β : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E] [OrderedAddCommGroup β] [Module ℝ β] [OrderedSMul ℝ β] {s : Set E}

open Set Filter Function

open scoped Classical
open Topology

/-- Helper lemma for the more general case: `IsMinOn.of_isLocalMinOn_of_convexOn`.
-/
theorem IsMinOn.of_isLocalMinOn_of_convexOn_Icc {f : ℝ → β} {a b : ℝ} (a_lt_b : a < b)
    (h_local_min : IsLocalMinOn f (Icc a b) a) (h_conv : ConvexOn ℝ (Icc a b) f) :
    IsMinOn f (Icc a b) a := by
  rintro c hc
  dsimp only [mem_setOf_eq]
  rw [IsLocalMinOn, nhdsWithin_Icc_eq_nhdsWithin_Ici a_lt_b] at h_local_min
  rcases hc.1.eq_or_lt with (rfl | a_lt_c)
  · exact le_rfl
  have H₁ : ∀ᶠ y in 𝓝[>] a, f a ≤ f y :=
    h_local_min.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have H₂ : ∀ᶠ y in 𝓝[>] a, y ∈ Ioc a c := Ioc_mem_nhdsWithin_Ioi (left_mem_Ico.2 a_lt_c)
  rcases (H₁.and H₂).exists with ⟨y, hfy, hy_ac⟩
  rcases (Convex.mem_Ioc a_lt_c).mp hy_ac with ⟨ya, yc, ya₀, yc₀, yac, rfl⟩
  suffices ya • f a + yc • f a ≤ ya • f a + yc • f c from
    (smul_le_smul_iff_of_pos_left yc₀).1 (le_of_add_le_add_left this)
  calc
    ya • f a + yc • f a = f a := by rw [← add_smul, yac, one_smul]
    _ ≤ f (ya * a + yc * c) := hfy
    _ ≤ ya • f a + yc • f c := h_conv.2 (left_mem_Icc.2 a_lt_b.le) hc ya₀ yc₀.le yac
#align is_min_on.of_is_local_min_on_of_convex_on_Icc IsMinOn.of_isLocalMinOn_of_convexOn_Icc

/-- A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
theorem IsMinOn.of_isLocalMinOn_of_convexOn {f : E → β} {a : E} (a_in_s : a ∈ s)
    (h_localmin : IsLocalMinOn f s a) (h_conv : ConvexOn ℝ s f) : IsMinOn f s a := by
  intro x x_in_s
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a x
  have hg0 : g 0 = a := AffineMap.lineMap_apply_zero a x
  have hg1 : g 1 = x := AffineMap.lineMap_apply_one a x
  have hgc : Continuous g := AffineMap.lineMap_continuous
  have h_maps : MapsTo g (Icc 0 1) s := by
    simpa only [g, mapsTo', ← segment_eq_image_lineMap] using h_conv.1.segment_subset a_in_s x_in_s
  have fg_local_min_on : IsLocalMinOn (f ∘ g) (Icc 0 1) 0 := by
    rw [← hg0] at h_localmin
    exact h_localmin.comp_continuousOn h_maps hgc.continuousOn (left_mem_Icc.2 zero_le_one)
  have fg_min_on : IsMinOn (f ∘ g) (Icc 0 1 : Set ℝ) 0 := by
    refine IsMinOn.of_isLocalMinOn_of_convexOn_Icc one_pos fg_local_min_on ?_
    exact (h_conv.comp_affineMap g).subset h_maps (convex_Icc 0 1)
  simpa only [hg0, hg1, comp_apply, mem_setOf_eq] using fg_min_on (right_mem_Icc.2 zero_le_one)
#align is_min_on.of_is_local_min_on_of_convex_on IsMinOn.of_isLocalMinOn_of_convexOn

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
theorem IsMaxOn.of_isLocalMaxOn_of_concaveOn {f : E → β} {a : E} (a_in_s : a ∈ s)
    (h_localmax : IsLocalMaxOn f s a) (h_conc : ConcaveOn ℝ s f) : IsMaxOn f s a :=
  IsMinOn.of_isLocalMinOn_of_convexOn (β := βᵒᵈ) a_in_s h_localmax h_conc
#align is_max_on.of_is_local_max_on_of_concave_on IsMaxOn.of_isLocalMaxOn_of_concaveOn

/-- A local minimum of a convex function is a global minimum. -/
theorem IsMinOn.of_isLocalMin_of_convex_univ {f : E → β} {a : E} (h_local_min : IsLocalMin f a)
    (h_conv : ConvexOn ℝ univ f) : ∀ x, f a ≤ f x := fun x =>
  (IsMinOn.of_isLocalMinOn_of_convexOn (mem_univ a) (h_local_min.on univ) h_conv) (mem_univ x)
#align is_min_on.of_is_local_min_of_convex_univ IsMinOn.of_isLocalMin_of_convex_univ

/-- A local maximum of a concave function is a global maximum. -/
theorem IsMaxOn.of_isLocalMax_of_convex_univ {f : E → β} {a : E} (h_local_max : IsLocalMax f a)
    (h_conc : ConcaveOn ℝ univ f) : ∀ x, f x ≤ f a :=
  IsMinOn.of_isLocalMin_of_convex_univ (β := βᵒᵈ) h_local_max h_conc
#align is_max_on.of_is_local_max_of_convex_univ IsMaxOn.of_isLocalMax_of_convex_univ
