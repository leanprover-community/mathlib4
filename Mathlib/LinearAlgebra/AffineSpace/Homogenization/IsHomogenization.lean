/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Range
public import Mathlib.LinearAlgebra.AffineSpace.Homogenization.Homogenization

import Mathlib.Algebra.Module.Submodule.EqLocus

/-! This file defines affine homogenization as any vector space linearly equivalent to
`Homogenization`, the canonical homogenization from Mathlib. It also proves every object
that satisfies the axiomatic description from [Gallier2011GeometricMethods] is a homogenization
in the linear equivalence sense (see `ofEmbed`). Use `IsHomogenization` for convenience if you want
to consider an embedding into a vector space that is not the canonical `Homogenization`.

## Implementation notes
* We transport relevant theorems from `Homogenization`.
* The axiomatization in the literature is redundant. The universal property can be proven solely
from the remaning axioms, as is done in `lift`.
* We choose the definition via `LinearEquiv` instead of the axiomatization, since the latter only
classifies homogenizations over a ring. The one presented here can be adapted to semirings if affine
spaces over semirings become necessary.

## References

* [J. Gallier, *Geometric Methods and Applications for Computer Science and
  Engineering*][Gallier2011GeometricMethods]
 -/

public noncomputable section

namespace Affine

section Ring

open Function Submodule

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
/-- A triple of a ring `R`, `R`-affine space `A` and `R`-vector space `W` is a homogenization if
`W` is linearly equivalent to the canonical homogenization. -/
structure IsHomogenization where ofRepr ::
  /-- The linear equivalence between the vector space and the canonical homogenization. -/
  repr : W ≃ₗ[R] Homogenization R A

namespace IsHomogenization

variable (ℋ : IsHomogenization R A W)

/-- The embedding of the affine space into the homogenization. -/
@[expose]
def ofPoint : A →ᵃ[R] W := ℋ.repr.symm.toAffineMap.comp Homogenization.ofPoint

/-- The embedding of the vector space into the homogenization. -/
@[expose]
def ofVector : V →ₗ[R] W := ℋ.repr.symm.toLinearMap ∘ₗ Homogenization.ofVector

theorem ofPoint_injective : Injective ℋ.ofPoint := by
  simpa [ofPoint] using Homogenization.ofPoint_injective

theorem ofVector_injective : Injective ℋ.ofVector := by
  simpa [ofVector] using Homogenization.ofVector_injective

theorem span_range_ofPoint : span R (Set.range ℋ.ofPoint) = ⊤ := by
  simpa [Set.range_comp, ofPoint] using Homogenization.span_range_ofPoint

section

variable {U : Type*} [AddCommGroup U] [Module R U]
variable {F : Type*} [FunLike F W U] [LinearMapClass F R _ _]

-- we duplicate the proof because translating using the typeclass is a pain
theorem hom_ext {f g : F} (h : ∀ x, f (ℋ.ofPoint x) = g (ℋ.ofPoint x)) : f = g := by
  apply LinearMap.ofClass_injective
  rwa [← LinearMap.eqLocus_eq_top, eq_top_iff, ← ℋ.span_range_ofPoint, Submodule.span_le,
    Set.range_subset_iff]

theorem hom_ext_iff {f g : F} : f = g ↔ ∀ x, f (ℋ.ofPoint x) = g (ℋ.ofPoint x) :=
  ⟨by rintro rfl _; rfl, ℋ.hom_ext⟩

end

section

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- An affine map on `A` taking values in a vector space extends uniquely to a linear map on `W`.
-/
def lift : (A →ᵃ[R] U) ≃+ (W →ₗ[R] U) :=
  Homogenization.lift.trans (ℋ.repr.arrowCongrAddEquiv (LinearEquiv.refl ..)).symm

@[simp]
theorem lift_apply_ofPoint (f : A →ᵃ[R] U) (p : A) : ℋ.lift f (ℋ.ofPoint p) = f p := by
  simp [lift, ofPoint]

@[simp]
theorem lift_apply_ofVector (f : A →ᵃ[R] U) (v : V) : ℋ.lift f (ℋ.ofVector v) = f.linear v := by
  simp [lift, ofVector]

end

/-- The linear map that is constantly `1` when restricted to `A`. -/
def weight : W →ₗ[R] R := Homogenization.weight ∘ₗ ℋ.repr.toLinearMap

/-- The homogenization of a point in `A` has weight 1. -/
@[simp]
theorem weight_ofPoint (a₀ : A) : ℋ.weight (ℋ.ofPoint a₀) = 1 := by simp [weight, ofPoint]

/-- The homogenization of a point in `V` has weight 0. -/
@[simp]
theorem weight_ofVector (v : V) : ℋ.weight (ℋ.ofVector v) = 0 := by simp [weight, ofVector]

theorem weight_eq_zero_iff {x : W} : ℋ.weight x = 0 ↔ ∃ v, x = ℋ.ofVector v := by
  simpa [← LinearEquiv.symm_apply_eq, weight, ofVector] using Homogenization.weight_eq_zero_iff

theorem weight_eq_one_iff {x : W} : ℋ.weight x = 1 ↔ ∃ p, x = ℋ.ofPoint p := by
  simpa [← LinearEquiv.symm_apply_eq, weight, ofPoint] using Homogenization.weight_eq_one_iff

-- the following two are in canonical hom in #43448
theorem ofPoint_ne_ofVector [Nontrivial R] (x : A) (v : V) : ℋ.ofPoint x ≠ ℋ.ofVector v :=
  ne_of_apply_ne ℋ.weight <| by simp

theorem ofPoint_ne_zero [Nontrivial R] (x : A) : ℋ.ofPoint x ≠ 0 := by
  simpa using ℋ.ofPoint_ne_ofVector x 0

theorem ofPoint_range_eq_preimage_weight_one : Set.range ℋ.ofPoint = ℋ.weight ⁻¹' {1} := by
  ext; simp [↓weight_eq_one_iff, eq_comm]

theorem ofVector_range_eq_preimage_weight_zero : Set.range ℋ.ofVector = ℋ.weight ⁻¹' {0} := by
  ext; simp [↓weight_eq_zero_iff, eq_comm]

/-- Embedding the underlying vector space is exactly the weight-0 hyperplane. -/
theorem ofVector_range_eq_weight_ker : ℋ.ofVector.range = ℋ.weight.ker := by
  apply SetLike.ext'
  rw [LinearMap.coe_range, ofVector_range_eq_preimage_weight_zero, LinearMap.ker]
  ext x
  simp

theorem repr_comp_ofPoint :
    ℋ.repr ∘ ℋ.ofPoint = Homogenization.ofPoint := by
  ext a; simp [ofPoint]

theorem weight_comp_repr :
    ℋ.weight ∘ₗ ℋ.repr.symm = Homogenization.weight (P := A) := by
  simp [weight, LinearMap.comp_assoc]

open AffineMap LinearEquiv in
/-- The linear equivalence between the underlying vector space and its embedding. -/
def ofVectorRangeEquiv : V ≃ₗ[R] ℋ.ofVector.range where
  toFun v := ⟨ℋ.ofVector v, ℋ.ofVector.mem_range_self v⟩
  map_add' v w := by simp
  map_smul' r v := by simp
  invFun := (ofInjective ℋ.ofVector (linear_injective_iff _ |>.mpr ℋ.ofPoint_injective)).invFun
  left_inv := LinearEquiv.left_inv _
  right_inv := LinearEquiv.right_inv _

/-- The affine equivalence between the affine space space and its embedding. -/
public def ofPointRangeEquiv : A ≃ᵃ[R] ℋ.ofPoint.range :=
  .ofBijective
    ⟨ℋ.ofPoint.injective_rangeRestrict_iff.mpr ℋ.ofPoint_injective, fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩

theorem apply_ofPointRangeEquiv_symm (x : ℋ.ofPoint.range) :
    ℋ.ofPoint (ℋ.ofPointRangeEquiv.symm x) = x := by
  rw [← ℋ.ofPointRangeEquiv.right_inv x]
  congr; exact ℋ.ofPointRangeEquiv.symm_apply_apply _

section

variable {U : Type*} [AddCommGroup U] [Module R U] {f : A →ᵃ[R] U} {g : U →ₗ[R] R}

lemma comp_lift_eq_weight_of_range_preimage (f_range : Set.range f = g ⁻¹' {1}) :
    g ∘ₗ (ℋ.lift f) = ℋ.weight := by
  refine ℋ.hom_ext (fun p ↦ ?_)
  have := f_range ▸ Set.mem_range_self p
  simpa [LinearMap.comp_apply, ofPoint, weight, lift] using this

lemma lift_bijective_of_injective_of_range_preimage (f_inj : Injective f)
    (f_range : Set.range f = g ⁻¹' {1}) : Bijective (ℋ.lift f) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have : ℋ.weight a = 0 := by simp [← ℋ.comp_lift_eq_weight_of_range_preimage f_range, ha]
    obtain ⟨_, rfl⟩ := ℋ.weight_eq_zero_iff.mp this
    rw [ℋ.lift_apply_ofVector] at ha
    simp [(map_eq_zero_iff _ (f.linear_injective_iff.mpr f_inj)).mp ha]
  · intro w
    obtain p₀ := Classical.arbitrary A
    obtain ⟨a, ha⟩ : w - g w • f p₀ + f p₀ ∈ Set.range f := by
      rw [f_range]
      have : g (w - g w • f p₀ + f p₀) = 1 := by
        have : f p₀ ∈ g ⁻¹' {1} := f_range ▸ Set.mem_range_self p₀
        rw [map_add, map_sub, map_smul, this, smul_eq_mul, mul_one, sub_self, zero_add]
      simpa using this
    exact ⟨ℋ.ofVector (a -ᵥ p₀) + g w • ℋ.ofPoint p₀, by simp [ofPoint, ofVector, lift, ha]⟩

end

section Constructions

variable (R A) in
/-- The canonical homogenization is a homogenization. -/
def canonical : IsHomogenization R A (Homogenization R A) := ofRepr <| LinearEquiv.refl ..

/-- Construct a homogenization from an embedding of the affine space `A` into the vector
space `W` and a weight map that is the constant 1-map on the embedded `A`. This follows the
axiomatization in Definition 4.2 of [Gallier2011GeometricMethods]
https://www.cis.upenn.edu/~jean/gma-v2-root.pdf -/
def ofEmbed {embed : A →ᵃ[R] W} (embed_inj : Injective embed) {weight : W →ₗ[R] R}
    (embed_range : Set.range embed = weight ⁻¹' {1}) :
  IsHomogenization R A W where
  repr := by
    apply (LinearEquiv.ofBijective (Homogenization.lift embed) ?_).symm
    exact (lift_bijective_of_injective_of_range_preimage (canonical R A) embed_inj embed_range)

/-- The embedding used in the construction becomes the embedding in the homogenization. -/
theorem ofEmbed_ofPoint {embed : A →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).ofPoint = embed := by
  ext p
  exact Homogenization.lift_apply_ofPoint ..

/-- The weight used in the construction becomes the weight in the homogenization. -/
theorem ofEmbed_weight {embed : A →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).weight = weight := by
  ext w
  unfold IsHomogenization.weight
  have : Homogenization.lift embed ((ofEmbed embed_inj embed_range).repr w) = w := by
    rw [← LinearEquiv.ofBijective_apply]
    exact LinearEquiv.apply_symm_apply _ w
  rw [LinearMap.coe_comp, ← this, ← LinearMap.comp_apply]
  congr
  exact (comp_lift_eq_weight_of_range_preimage (canonical R A) embed_range).symm

/-- A module is a homogenization of the weight-one hyperplane of any linear functional,
provided that hyperplane is nonempty. -/
def ofWeightOne (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    IsHomogenization R ((affineSpan R {1}).comap g.toAffineMap) W :=
  ofEmbed (weight := g) (AffineSubspace.subtype_injective _) (by simp; rfl)

@[simp]
theorem ofWeightOne_weight (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    (ofWeightOne g).weight = g := by
  simp [ofWeightOne, ofEmbed_weight]

end Constructions

end IsHomogenization

end Ring

end Affine
