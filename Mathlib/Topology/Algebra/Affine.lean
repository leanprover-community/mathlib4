/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
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

variable {α : Type*} {l : Filter α}

open Topology Filter

theorem _root_.Filter.Tendsto.lineMap {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝 <| AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁

theorem _root_.Filter.Tendsto.midpoint [Invertible (2 : R)] {f₁ f₂ : α → P} {p₁ p₂ : P}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) :
    Tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝 <| midpoint R p₁ p₂) :=
  h₁.lineMap h₂ tendsto_const_nhds


end Ring

section CommRing

variable [CommRing R] [Module R V] [ContinuousConstSMul R V]

@[continuity, fun_prop]
theorem homothety_continuous (x : P) (t : R) : Continuous <| homothety x t := by
  rw [coe_homothety]
  fun_prop

end CommRing

section Field

variable [Field R] [Module R V] [ContinuousConstSMul R V]

theorem homothety_isOpenMap (x : P) (t : R) (ht : t ≠ 0) : IsOpenMap <| homothety x t := by
  apply IsOpenMap.of_inverse (homothety_continuous x t⁻¹) <;> intro e <;>
    simp [← AffineMap.comp_apply, ← homothety_mul, ht]

end Field

end AffineMap
