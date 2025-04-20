/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Geometry.Convex.Cone.Proper
import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The dual of a cone

Given a perfect pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`PointedCone.dual p C` to be the cone in `N` consisting of all points `y` such that for all `x ∈ s`
we have `0 ≤ p x y`.
-/

open Function LinearMap Pointwise Set

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

variable (p s) in
/-- The dual cone of a set `s` with respect to a perfect pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ s` we have `0 ≤ p x y`. -/
def dual (s : Set M) : PointedCone R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)

@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := .rfl

@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp

lemma dual_univ (hp : Injective p.flip) : dual p univ = 0 := by
  refine le_antisymm (fun y hy ↦ (_root_.map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
  exact (hy <| mem_univ x).antisymm' <| by simpa using hy <| mem_univ (-x)

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
lemma dual_singleton (x : M) : dual p {x} = (positive R R).comap (p x) := by ext; simp

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

variable [TopologicalSpace R] [ClosedIciTopology R] [TopologicalSpace N]

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
  -- TODO: This is mathematically incorrect!
  -- `p` should be `M →L[R] N →L[R] R`, not `M →ₗ[R] N →ₗ[R] R`
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

@[simp] lemma dual_univ [T1Space N] : dual p univ = 0 := by
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
