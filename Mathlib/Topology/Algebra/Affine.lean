/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Algebra.Group.AddTorsor

/-!
# Topological properties of affine spaces and maps

This file contains a few facts regarding the continuity of affine maps.
-/


namespace AffineMap

variable
  {R V P W Q : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

section Ring

variable [Ring R] [Module R V] [Module R W]

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem continuous_linear_iff {f : P →ᵃ[R] Q} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

/-- An affine map is continuous iff its underlying linear map is continuous. See also
`AffineMap.continuous_linear_iff`. -/
@[deprecated continuous_linear_iff (since := "2025-09-13")]
theorem continuous_iff {f : P →ᵃ[R] Q} : Continuous f ↔ Continuous f.linear :=
  continuous_linear_iff.symm

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
theorem isOpenMap_linear_iff {f : P →ᵃ[R] Q} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

variable [TopologicalSpace R] [ContinuousSMul R V]

/-- The line map is continuous. -/
@[continuity, fun_prop]
theorem lineMap_continuous {p q : P} :
    Continuous (lineMap p q : R →ᵃ[R] P) := by
  rw [coe_lineMap]
  fun_prop

end Ring

section CommRing

variable [CommRing R] [Module R V] [ContinuousConstSMul R V]

@[continuity, fun_prop]
theorem homothety_continuous (x : P) (t : R) : Continuous <| homothety x t := by
  rw [coe_homothety]
  fun_prop

variable (R) [TopologicalSpace R] [Module R W] [ContinuousSMul R W] (x : Q) {s : Set Q}

open Topology

theorem _root_.eventually_homothety_mem_of_mem_interior {y : Q} (hy : y ∈ interior s) :
    ∀ᶠ δ in 𝓝 (1 : R), homothety x δ y ∈ s := by
  have cont : Continuous (fun δ : R => homothety x δ y) := lineMap_continuous
  filter_upwards [cont.tendsto' 1 y (by simp) |>.eventually (isOpen_interior.eventually_mem hy)]
    with _ h using interior_subset h

theorem _root_.eventually_homothety_image_subset_of_finite_subset_interior {t : Set Q}
    (ht : t.Finite) (h : t ⊆ interior s) : ∀ᶠ δ in 𝓝 (1 : R), homothety x δ '' t ⊆ s := by
  suffices ∀ y ∈ t, ∀ᶠ δ in 𝓝 (1 : R), homothety x δ y ∈ s by
    simp only [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior R x (h hy)

end CommRing

section Field

variable [Field R] [Module R V] [ContinuousConstSMul R V]

theorem homothety_isOpenMap (x : P) (t : R) (ht : t ≠ 0) : IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

end Field

end AffineMap
