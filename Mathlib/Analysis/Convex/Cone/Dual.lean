/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Geometry.Convex.Cone.Dual

/-!
# Double dual cone and Farkas' lemma

We prove Farkas' lemma, which says that a proper cone `C` in a locally convex topological real
vector space `E` and a point `x₀` not in `C` can be separated by a hyperplane. This is a geometric
interpretation of the Hahn-Banach separation theorem.
We also prove that the double dual of a proper cone is itself.


## Main statements

We prove the following theorems:
* `ConvexCone.innerDual_of_innerDual_eq_self`:
  The `innerDual` of the `innerDual` of a proper convex cone is itself.
* `ProperCone.hyperplane_separation`, `ProperCone.hyperplane_separation_point`: Farkas lemma.
* `ProperCone.dual_dual_flip`, `ProperCone.dual_flip_dual`: The double dual of a proper cone.

## References

* https://en.wikipedia.org/wiki/Hyperplane_separation_theorem
* https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation
-/

assert_not_exists InnerProductSpace

open Set LinearMap Pointwise

namespace ProperCone
variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Module ℝ F]
  {s : Set E} {x₀ : E}

open ConvexCone in
/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem hyperplane_separation
    (C : ProperCone ℝ E) {s : Set E} (hs : Convex ℝ s) (hs' : IsCompact s) (hsC : Disjoint s C) :
    ∃ f : E →L[ℝ] ℝ, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ s, f x < 0 := by
  obtain rfl | ⟨x₀, hx₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨U, V, hUopen, -, hUconv, -, hsU, hCV, hUV⟩ :=
    hsC.exists_open_convexes hs hs' C.convex C.isClosed
  obtain ⟨f, u, h₁, h₂⟩ :=
    geometric_hahn_banach_open (E := E) (s := hull ℝ U) (t := C)
      (hull ℝ U).convex (isOpen_hull hUopen) C.convex
      (disjoint_coe.mpr
      ((disjoint_hull_left_of_convex (C := C) hUconv).2 <| hUV.mono_right hCV))
  obtain rfl : u = 0 := by
    have hu : u ≤ 0 := by simpa using h₂ 0 (zero_mem _)
    have hfx₀ : f x₀ < 0 := (h₁ _ <| subset_hull (hsU hx₀)).trans_le hu
    refine hu.antisymm <| le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    simpa [hfx₀.ne] using (h₁ ((r * (f x₀)⁻¹) • x₀) ((hull ℝ U).smul_mem
      (mul_pos_of_neg_of_neg hr <| inv_neg''.2 hfx₀) <| subset_hull (hsU hx₀))).le
  exact ⟨f, h₂, fun x hxs ↦ h₁ _ (subset_hull (hsU hxs))⟩

open ConvexCone in
/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem hyperplane_separation_point (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
    ∃ f : E →L[ℝ] ℝ, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0 := by
  simpa [*] using C.hyperplane_separation (convex_singleton x₀)

/-- The **double dual of a proper cone** is itself. -/
@[simp] theorem dual_flip_dual (p : ContinuousPerfectPairing ℝ E F) (C : ProperCone ℝ E) :
    dual p.flip (dual p (C : Set E)) = C := by
  refine le_antisymm (fun x ↦ ?_) subset_dual_dual
  simp only [mem_toPointedCone, mem_dual, SetLike.mem_coe]
  contrapose!
  simpa [p.flip.surjective.exists] using C.hyperplane_separation_point

/-- The **double dual of a proper cone** is itself. -/
@[simp] theorem dual_dual_flip (p : ContinuousPerfectPairing ℝ F E) (C : ProperCone ℝ E) :
    dual p (dual p.flip (C : Set E)) = C := C.dual_flip_dual p.flip

end ProperCone
