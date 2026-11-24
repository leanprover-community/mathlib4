/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Geometry.Convex.ConvexSpace.EnvelopingModule
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The enveloping affine space of a convex space

The enveloping module `Convexity.EnvelopingModule K X` of a convex space `X` is one dimension too
big: the canonical map `Convexity.EnvelopingModule.of` lands in the affine hyperplane of elements
of mass `1`, which does not contain `0`. This file defines that hyperplane, the
*enveloping affine space* `Convexity.EnvelopingAffineSpace K X`, and shows that the enveloping
module is its homogenisation: linear maps out of `EnvelopingModule K X` are the same as affine maps
out of `EnvelopingAffineSpace K X`.

## Main declarations

* `Convexity.EnvelopingModule.lift`: The universal property of the enveloping module: an affine map
  from `X` to a module extends to a linear map from `EnvelopingModule K X`.
* `Convexity.EnvelopingModule.mass`: The total mass of an element of the enveloping module.
* `Convexity.envelopingAffineSubspace K X`: The affine subspace of `EnvelopingModule K X` of
  elements of mass `1`.
* `Convexity.EnvelopingAffineSpace K X`: The enveloping affine space of `X`, as a type.
* `Convexity.affineSpan_range_of`: The enveloping affine space is the affine span of `X`.
* `Convexity.direction_envelopingAffineSubspace`: The direction of the enveloping affine space is
  the kernel of the mass.
* `Convexity.EnvelopingAffineSpace.linearMapEquiv`: The enveloping module is the homogenisation of
  the enveloping affine space.
-/

open Finsupp Function

@[expose] public noncomputable section

namespace Convexity
variable {K X M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X]

namespace EnvelopingModule

lemma mkQ_surjective : Surjective (mkQ K X) := Quotient.mk_surjective

/-- Two linear maps out of the enveloping module are equal if they agree on the image of `of`. -/
@[ext]
lemma linearMap_ext [AddCommMonoid M] [Module K M] {L L' : EnvelopingModule K X →ₗ[K] M}
    (h : ∀ x, L (of K x) = L' (of K x)) : L = L' := by
  have : L ∘ₗ mkQ K X = L' ∘ₗ mkQ K X := Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring <| h x
  ext v
  obtain ⟨f, rfl⟩ := mkQ_surjective v
  exact congr($this f)

section lift
variable [AddCommGroup M] [Module K M] [ConvexSpace K M] [IsModuleConvexSpace K M] {f : X → M}

private lemma linearCombination_weights (hf : IsAffineMap K f) (w : StdSimplex K X) :
    linearCombination K f w.weights = f w.sConvexComb := by
  rw [linearCombination_apply, hf.map_sConvexComb, sConvexComb_map, iConvexComb_eq_sum]

lemma linearCombination_eq_of_envelopingRel (hf : IsAffineMap K f) {g h : X →₀ K}
    (hgh : EnvelopingRel K g h) : linearCombination K f g = linearCombination K f h := by
  obtain rfl | ⟨c, w₁, w₂, -, hw, hgh⟩ := hgh
  · rfl
  simpa [linearCombination_weights hf, hw] using congr(linearCombination K f $hgh)

/-- The universal property of the enveloping module: an affine map from a convex space `X` to a
module extends uniquely to a linear map from `EnvelopingModule K X`. -/
def lift (f : X → M) (hf : IsAffineMap K f) : EnvelopingModule K X →ₗ[K] M where
  toFun := Quotient.lift (linearCombination K f) fun _ _ hgh ↦
    linearCombination_eq_of_envelopingRel hf <| mkQ_eq_mkQ.1 <| Quotient.sound hgh
  map_add' v w := by
    obtain ⟨g, rfl⟩ := mkQ_surjective v
    obtain ⟨h, rfl⟩ := mkQ_surjective w
    exact map_add (linearCombination K f) g h
  map_smul' c v := by
    obtain ⟨g, rfl⟩ := mkQ_surjective v
    exact map_smul (linearCombination K f) c g

@[simp] lemma lift_mkQ (hf : IsAffineMap K f) (g : X →₀ K) :
    lift f hf (mkQ K X g) = linearCombination K f g := rfl

@[simp] lemma lift_of (hf : IsAffineMap K f) (x : X) : lift f hf (of K x) = f x := by
  simp [of_apply]

end lift

variable (K X) in
/-- The total mass of an element of the enveloping module. -/
def mass : EnvelopingModule K X →ₗ[K] K := lift (fun _ ↦ 1) (.const _)

@[simp] lemma mass_of (x : X) : mass K X (of K x) = 1 := lift_of ..

lemma mass_mkQ (f : X →₀ K) : mass K X (mkQ K X f) = f.sum fun _ r ↦ r := by
  simp [mass, linearCombination_apply]

end EnvelopingModule

open EnvelopingModule

variable (K X) in
/-- The affine subspace of the enveloping module of a convex space `X` consisting of elements of
mass `1`. It is the affine span of `X`, see `Convexity.affineSpan_range_of`. -/
def envelopingAffineSubspace : AffineSubspace K (EnvelopingModule K X) where
  carrier := {v | mass K X v = 1}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simp_all [vsub_eq_sub, vadd_eq_add]

variable (K X) in
/-- The enveloping affine space of a convex space `X`: the affine subspace of the enveloping module
consisting of elements of mass `1`.

Its homogenisation is `Convexity.EnvelopingModule K X`, see
`Convexity.EnvelopingAffineSpace.linearMapEquiv`. -/
abbrev EnvelopingAffineSpace : Type _ := envelopingAffineSubspace K X

@[simp] lemma mem_envelopingAffineSubspace {v : EnvelopingModule K X} :
    v ∈ envelopingAffineSubspace K X ↔ mass K X v = 1 := .rfl

lemma of_mem_envelopingAffineSubspace (x : X) : of K x ∈ envelopingAffineSubspace K X := mass_of x

/-- The enveloping affine space is the affine span of the image of `X`. -/
lemma affineSpan_range_of :
    affineSpan K (Set.range (of K : X → EnvelopingModule K X)) = envelopingAffineSubspace K X := by
  refine le_antisymm (affineSpan_le.2 <| Set.range_subset_iff.2 of_mem_envelopingAffineSubspace)
    fun v hv ↦ ?_
  obtain ⟨f, rfl⟩ := mkQ_surjective v
  rw [mem_envelopingAffineSubspace, mass_mkQ] at hv
  obtain _ | ⟨⟨x₀⟩⟩ := isEmpty_or_nonempty X
  · simp [Subsingleton.elim f 0] at hv
  have : mkQ K X f = (f.sum fun x r ↦ r • (of K x -ᵥ of K x₀)) +ᵥ of K x₀ := by
    have h₁ : (f.sum fun _ r ↦ r • of K x₀) = of K x₀ := by
      rw [Finsupp.sum, ← Finset.sum_smul (R := K) (M := EnvelopingModule K X)]
      simp_all [Finsupp.sum]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, Finsupp.sum_sub, h₁, sub_add_cancel, mkQ_eq_sum]
  rw [this]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ (mem_affineSpan K <| Set.mem_range_self x₀)
  rw [direction_affineSpan]
  exact Submodule.finsuppSum_mem K _ _ _ fun x _ ↦ Submodule.smul_mem _ _ <|
    vsub_mem_vectorSpan K (Set.mem_range_self x) (Set.mem_range_self x₀)

/-- The direction of the enveloping affine space is the kernel of the mass. -/
lemma direction_envelopingAffineSubspace [Nonempty X] :
    (envelopingAffineSubspace K X).direction = LinearMap.ker (mass K X) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  ext v
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right (of_mem_envelopingAffineSubspace (K := K) x₀),
    LinearMap.mem_ker]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp_all [vsub_eq_sub]
  · exact fun hv ↦ ⟨v + of K x₀, by simp [hv], (add_sub_cancel_right _ _).symm⟩

namespace EnvelopingAffineSpace

instance [Nonempty X] : Nonempty (EnvelopingAffineSpace K X) :=
  ⟨⟨of K (Classical.arbitrary X), of_mem_envelopingAffineSubspace _⟩⟩

variable (K) in
/-- The canonical map from a convex space to its enveloping affine space. -/
def of (x : X) : EnvelopingAffineSpace K X := ⟨EnvelopingModule.of K x, mass_of x⟩

@[simp] lemma coe_of (x : X) : (of K x : EnvelopingModule K X) = EnvelopingModule.of K x := rfl

/-- The canonical map from a cancellative convex space to its enveloping affine space is
injective. -/
lemma of_injective [IsCancelConvexSpace K X] : Injective (of K : X → EnvelopingAffineSpace K X) :=
  fun _ _ h ↦ EnvelopingModule.of_injective congr(Subtype.val $h)

variable [Nonempty X] [AddCommGroup M] [Module K M]

/-- Projection of the enveloping module onto the direction of the enveloping affine space, using
an arbitrary basepoint. -/
def directionProj : EnvelopingModule K X →ₗ[K] (envelopingAffineSubspace K X).direction :=
  .codRestrict _
    (.id - (mass K X).smulRight (EnvelopingModule.of K (Classical.arbitrary X))) fun v ↦ by
      rw [direction_envelopingAffineSubspace, LinearMap.mem_ker]; simp

/-- The linear extension of an affine map out of the enveloping affine space to the enveloping
module. -/
def linearExtend (φ : EnvelopingAffineSpace K X →ᵃ[K] M) :
    EnvelopingModule K X →ₗ[K] M :=
  φ.linear ∘ₗ directionProj + (mass K X).smulRight (φ (of K (Classical.arbitrary X)))

lemma linearExtend_coe (φ : EnvelopingAffineSpace K X →ᵃ[K] M)
    (a : EnvelopingAffineSpace K X) : linearExtend φ a = φ a := by
  have ha : mass K X a = 1 := a.property
  have : directionProj (a : EnvelopingModule K X) = a -ᵥ of K (Classical.arbitrary X) := by
    ext; simp [directionProj, ha, AffineSubspace.coe_vsub, vsub_eq_sub]
  simp [linearExtend, this, ha]

variable (K X M) in
/-- **The enveloping module is the homogenisation of the enveloping affine space**: linear maps
out of `EnvelopingModule K X` are in bijection with affine maps out of
`EnvelopingAffineSpace K X`, by restriction. -/
def linearMapEquiv :
    (EnvelopingModule K X →ₗ[K] M) ≃ₗ[K] (EnvelopingAffineSpace K X →ᵃ[K] M) where
  toFun L := L.toAffineMap.comp (envelopingAffineSubspace K X).subtype
  invFun := linearExtend
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv L := by ext x; exact linearExtend_coe _ (of K x)
  right_inv φ := by ext a; exact linearExtend_coe φ a

@[simp] lemma linearMapEquiv_apply (L : EnvelopingModule K X →ₗ[K] M)
    (a : EnvelopingAffineSpace K X) : linearMapEquiv K X M L a = L a := rfl

@[simp] lemma linearMapEquiv_symm_apply_coe (φ : EnvelopingAffineSpace K X →ᵃ[K] M)
    (a : EnvelopingAffineSpace K X) : (linearMapEquiv K X M).symm φ a = φ a :=
  linearExtend_coe φ a

end EnvelopingAffineSpace
end Convexity
