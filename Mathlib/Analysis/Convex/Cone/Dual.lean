/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The topological dual of a cone and Farkas' lemma

Given a continuous bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`,
we define `ProperCone.dual p C` to be the proper cone in `N` consisting of all points `y` such that
for all `x ∈ s` we have `0 ≤ p x y`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib.Analysis.Convex.Cone.Dual` for that case.

We prove Farkas' lemma, which says that a proper cone `C` in a locally convex topological real
vector space `E` and a point `x₀` not in `C` can be separated by a hyperplane. This is a geometric
interpretation of the Hahn-Banach separation theorem.
As a corollary, we prove that the double dual of a proper cone is itself.

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

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [TopologicalSpace R] [ClosedIciTopology R]
  [IsOrderedRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [TopologicalSpace N]
  {p : M →ₗ[R] N →ₗ[R] R} {s : Set M}

lemma isClosed_dual (hp : ∀ x, Continuous (p x)) : IsClosed (dual p s : Set N) := by
  rw [← s.biUnion_of_singleton]
  simp_rw [dual_iUnion, Submodule.iInf_coe, dual_singleton]
  exact isClosed_biInter fun x hx ↦ isClosed_Ici.preimage <| hp _

end PointedCone

namespace ProperCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [ClosedIciTopology R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  {p : ContinuousPerfectPairing R M N} {s t : Set M} {y : N}

variable (p s) in
/-- The dual cone of a set `s` with respect to a perfect pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
def dual (s : Set M) : ProperCone R N where
  toSubmodule := PointedCone.dual p.toLinearMap s
  isClosed' := PointedCone.isClosed_dual fun _ ↦ p.continuous_toLinearMap_left

@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := .rfl

@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp

@[simp] lemma dual_univ [T1Space N] : dual p univ = ⊥ := by
  refine le_antisymm (fun y hy ↦ (map_eq_zero_iff p.flip p.flip.injective).1 ?_) (by simp)
  ext x
  exact (hy <| mem_univ x).antisymm' <| by simpa using hy <| mem_univ (-x)

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
lemma dual_singleton [OrderClosedTopology R] (x : M) :
    dual p {x} = (positive R R).comap (p x) := by ext; simp

lemma dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop

lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]

lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_swap (α := M)]

lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_swap (α := M)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by
  ext; simp [forall_swap (α := M)]

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

end ProperCone

namespace ProperCone
variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Module ℝ F]
  {K : Set E} {x₀ : E}

open ConvexCone in
/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem hyperplane_separation (C : ProperCone ℝ E) (hKconv : Convex ℝ K) (hKcomp : IsCompact K)
    (hKC : Disjoint K C) : ∃ f : E →L[ℝ] ℝ, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ K, f x < 0 := by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  obtain ⟨f, u, v, hu, huv, hv⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp C.convex C.isClosed hKC
  have hv₀ : v < 0 := by simpa using hv 0 C.zero_mem
  refine ⟨f, fun x hx ↦ ?_, fun x hx ↦ (hu x hx).trans_le <| huv.le.trans hv₀.le⟩
  by_contra! hx₀
  simpa [hx₀.ne] using hv ((v * (f x)⁻¹) • x)
    (C.smul_mem hx <| le_of_lt <| mul_pos_of_neg_of_neg hv₀ <| inv_neg''.2 hx₀)

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
