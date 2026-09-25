/-
Copyright (c) 2026 Olivia Röhrig, Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Range
public import Mathlib.LinearAlgebra.AffineSpace.Homogenization.Basic

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
variable {P : Type*} [AddTorsor V P]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R P W) in
/-- A triple of a ring `R`, `R`-affine space `A` and `R`-vector space `W` is a homogenization if
`W` is linearly equivalent to the canonical homogenization. -/
structure IsHomogenization where ofRepr ::
  /-- The linear equivalence between the vector space and the canonical homogenization. -/
  repr : W ≃ₗ[R] Homogenization R P

namespace IsHomogenization

variable (ℋ : IsHomogenization R P W)

/-- The embedding of the affine space into the homogenization. -/
@[expose]
def ofPoint : P →ᵃ[R] W := ℋ.repr.symm.toAffineMap.comp Homogenization.ofPoint

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
  rwa [← LinearMap.cancel_right ℋ.repr.symm.surjective, Homogenization.hom_ext_iff]

theorem hom_ext_iff {f g : F} : f = g ↔ ∀ x, f (ℋ.ofPoint x) = g (ℋ.ofPoint x) :=
  ⟨by rintro rfl _; rfl, ℋ.hom_ext⟩

end

section

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- An affine map on `A` taking values in a vector space extends uniquely to a linear map on `W`.
-/
def lift : (P →ᵃ[R] U) ≃+ (W →ₗ[R] U) :=
  Homogenization.lift.trans (ℋ.repr.arrowCongrAddEquiv (LinearEquiv.refl ..)).symm

@[simp]
theorem lift_apply_ofPoint (f : P →ᵃ[R] U) (p : P) : ℋ.lift f (ℋ.ofPoint p) = f p := by
  simp [lift, ofPoint]

@[simp]
theorem lift_apply_ofVector (f : P →ᵃ[R] U) (v : V) : ℋ.lift f (ℋ.ofVector v) = f.linear v := by
  simp [lift, ofVector]

@[simp]
theorem lift_symm_apply (f : W →ₗ[R] U) (p : P) : ℋ.lift.symm f p = f (ℋ.ofPoint p) := by
  simp [lift, ofPoint]

end

/-- The linear map that is constantly `1` when restricted to `A`. -/
def weight : W →ₗ[R] R := Homogenization.weight ∘ₗ ℋ.repr.toLinearMap

/-- The homogenization of a point in `A` has weight 1. -/
@[simp]
theorem weight_ofPoint (p : P) : ℋ.weight (ℋ.ofPoint p) = 1 := by simp [weight, ofPoint]

/-- The homogenization of a point in `V` has weight 0. -/
@[simp]
theorem weight_ofVector (v : V) : ℋ.weight (ℋ.ofVector v) = 0 := by simp [weight, ofVector]

theorem weight_eq_zero_iff {w : W} : ℋ.weight w = 0 ↔ ∃ v, w = ℋ.ofVector v := by
  simpa [← LinearEquiv.symm_apply_eq, weight, ofVector] using Homogenization.weight_eq_zero_iff

theorem weight_eq_one_iff {w : W} : ℋ.weight w = 1 ↔ ∃ p, w = ℋ.ofPoint p := by
  simpa [← LinearEquiv.symm_apply_eq, weight, ofPoint] using Homogenization.weight_eq_one_iff

-- the following two are in canonical hom in #43448
theorem ofPoint_ne_ofVector [Nontrivial R] (p : P) (v : V) : ℋ.ofPoint p ≠ ℋ.ofVector v :=
  ne_of_apply_ne ℋ.weight <| by simp

theorem ofPoint_ne_zero [Nontrivial R] (p : P) : ℋ.ofPoint p ≠ 0 := by
  simpa using ℋ.ofPoint_ne_ofVector p 0

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
    ℋ.weight ∘ₗ ℋ.repr.symm = Homogenization.weight (P := P) := by
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
public def ofPointRangeEquiv : P ≃ᵃ[R] ℋ.ofPoint.range :=
  .ofBijective
    ⟨ℋ.ofPoint.injective_rangeRestrict_iff.mpr ℋ.ofPoint_injective, fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩

theorem apply_ofPointRangeEquiv_symm (x : ℋ.ofPoint.range) :
    ℋ.ofPoint (ℋ.ofPointRangeEquiv.symm x) = x := by
  rw [← ℋ.ofPointRangeEquiv.right_inv x]
  congr; exact ℋ.ofPointRangeEquiv.symm_apply_apply _

section

variable {U : Type*} [AddCommGroup U] [Module R U] {f : P →ᵃ[R] U} {g : U →ₗ[R] R}

lemma comp_lift_eq_weight (h : ∀ p, g (f p) = 1) : g ∘ₗ (ℋ.lift f) = ℋ.weight :=
  ℋ.hom_ext <| by simpa

lemma lift_bijective_of_injective_of_range_preimage (f_inj : Injective f)
    (f_range : Set.range f = g ⁻¹' {1}) : Bijective (ℋ.lift f) := by
  have g_f : ∀ p, g (f p) = 1 := Set.range_subset_iff.mp f_range.subset
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have : ℋ.weight a = 0 := by simp [← ℋ.comp_lift_eq_weight g_f, ha]
    obtain ⟨_, rfl⟩ := ℋ.weight_eq_zero_iff.mp this
    rw [ℋ.lift_apply_ofVector] at ha
    simp [(map_eq_zero_iff _ (f.linear_injective_iff.mpr f_inj)).mp ha]
  · intro w
    obtain p₀ := Classical.arbitrary P
    obtain ⟨a, ha⟩ : w - g w • f p₀ + f p₀ ∈ Set.range f := by simp [f_range, g_f]
    exact ⟨ℋ.ofVector (a -ᵥ p₀) + g w • ℋ.ofPoint p₀, by simp [ofPoint, ofVector, lift, ha]⟩

end

section Constructions

variable (R P) in
/-- The canonical homogenization is a homogenization. -/
def ofHomogenization : IsHomogenization R P (Homogenization R P) := ofRepr <| LinearEquiv.refl ..

@[simp]
theorem ofPoint_ofHomogenization : (ofHomogenization R P).ofPoint = Homogenization.ofPoint := by
  ext; simp [ofPoint, ofHomogenization] -- could use a simp lemma LinearMap.id.toAffineMap = AffineMap.id?

@[simp]
theorem ofVector_ofHomogenization : (ofHomogenization R P).ofVector = Homogenization.ofVector := by
  simp [ofVector, ofHomogenization]

@[simp]
theorem weight_ofHomogenization : (ofHomogenization R P).weight = Homogenization.weight := by
  simp [weight, ofHomogenization]

/-- Construct a homogenization from an embedding of the affine space `A` into the vector
space `W` and a weight map that is the constant 1-map on the embedded `A`. This follows the
axiomatization in Definition 4.2 of [Gallier2011GeometricMethods]
https://www.cis.upenn.edu/~jean/gma-v2-root.pdf -/
def ofEmbed {embed : P →ᵃ[R] W} (embed_inj : Injective embed) {weight : W →ₗ[R] R}
    (embed_range : Set.range embed = weight ⁻¹' {1}) :
    IsHomogenization R P W where
  repr := by
    apply (LinearEquiv.ofBijective (Homogenization.lift embed) ?_).symm
    exact lift_bijective_of_injective_of_range_preimage (ofHomogenization R P) embed_inj embed_range

/-- The embedding used in the construction becomes the embedding in the homogenization. -/
@[simp]
theorem ofPoint_ofEmbed {embed : P →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).ofPoint = embed := by
  ext p
  exact Homogenization.lift_apply_ofPoint ..

@[simp]
theorem ofVector_ofEmbed {embed : P →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).ofVector = embed.linear := by
  ext p
  exact Homogenization.lift_apply_ofVector ..

/-- The weight used in the construction becomes the weight in the homogenization. -/
@[simp]
theorem weight_ofEmbed {embed : P →ᵃ[R] W} (embed_inj : Injective embed)
    {weight : W →ₗ[R] R} (embed_range : Set.range embed = weight ⁻¹' {1}) :
    (ofEmbed embed_inj embed_range).weight = weight := by
  refine (ofEmbed embed_inj embed_range).hom_ext fun x => ?_
  rw [weight_ofPoint, ofPoint_ofEmbed, eq_comm]
  exact congr(embed x ∈ $embed_range).mp <| Set.mem_range_self x

/-- A module is a homogenization of the weight-one hyperplane of any linear functional,
provided that hyperplane is nonempty. -/
def ofWeightOne (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    IsHomogenization R ((affineSpan R {1}).comap g.toAffineMap) W :=
  ofEmbed (weight := g) (AffineSubspace.subtype_injective _) (by simp; rfl)

@[simp]
theorem ofPoint_ofWeightOne (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    (ofWeightOne g).ofPoint = ((affineSpan R {1}).comap g.toAffineMap).subtype := by
  simp [ofWeightOne]

@[simp]
theorem ofVector_ofWeightOne (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    (ofWeightOne g).ofVector = ((affineSpan R {1}).comap g.toAffineMap).direction.subtype := by
  simp [ofWeightOne]

@[simp]
theorem weight_ofWeightOne (g : W →ₗ[R] R) [Nonempty ((affineSpan R {1}).comap g.toAffineMap)] :
    (ofWeightOne g).weight = g := by
  simp [ofWeightOne]

end Constructions

end IsHomogenization

end Ring

end Affine
