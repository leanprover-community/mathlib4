/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The algebraic dual of a cone

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`PointedCone.dual p C` to be the pointed cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib/Analysis/Convex/Cone/Dual.lean` for that case.

## Implementation notes

We do not provide a `ConvexCone`-valued version of `PointedCone.dual` since the dual cone of any set
always contains `0`, ie is a pointed cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < p x y}` is a candidate to the name
`ConvexCone.dual`.

## TODO

Deduce from `dual_flip_dual_dual_flip` that polyhedral cones are invariant under taking double duals
-/

assert_not_exists TopologicalSpace Real Cardinal

open Function LinearMap Pointwise Set

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

local notation3 "R≥0" => {c : R // 0 ≤ c}

variable (p s) in
/-- The dual cone of a set `s` with respect to a bilinear pairing `p` is the cone consisting of all
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
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by ext; simp

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

variable (s) in
@[simp] lemma dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_le_dual subset_dual_dual) subset_dual_dual

@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip (dual p (dual p.flip s)) = dual p.flip s := dual_dual_flip_dual _

@[simp]
lemma dual_span (s : Set M) : dual p (Submodule.span R≥0 s) = dual p s := by
  refine le_antisymm (dual_le_dual Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact add_nonneg hy hz
  | smul t y _hy hy => rw [map_smul_of_tower, Nonneg.mk_smul, smul_apply]; exact mul_nonneg t.2 hy

end PointedCone
