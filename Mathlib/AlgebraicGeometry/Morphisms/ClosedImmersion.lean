/-
Copyright (c) 2023 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Christian Merten, Jonas van der Schaaf
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!

# Closed immersions of schemes

A morphism of schemes `f : X ⟶ Y` is a closed immersion if the underlying map of topological spaces
is a closed immersion and the induced morphisms of stalks are all surjective.

## Main definitions

* `IsClosedImmersion` : The property of scheme morphisms stating `f : X ⟶ Y` is a closed immersion.

## TODO

* Show closed immersions of affines are induced by surjective ring maps
* Show closed immersions are stable under pullback
* Show closed immersions are precisely the proper monomorphisms
* Define closed immersions of locally ringed spaces, where we also assume that the kernel of `O_X →
  f_*O_Y` is locally generated by sections as an `O_X`-module, and relate it to this file. See
  https://stacks.math.columbia.edu/tag/01HJ.

-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is a closed immersion if the underlying
topological map is a closed embedding and the induced stalk maps are surjective. -/
@[mk_iff]
class IsClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop where
  base_closed : ClosedEmbedding f.1.base
  surj_on_stalks : ∀ x, Function.Surjective (f.stalkMap x)

namespace IsClosedImmersion

lemma closedEmbedding {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] : ClosedEmbedding f.1.base :=
  IsClosedImmersion.base_closed

lemma eq_inf : @IsClosedImmersion = (topologically ClosedEmbedding) ⊓
    stalkwise (fun f ↦ Function.Surjective f) := by
  ext X Y f
  rw [isClosedImmersion_iff]
  rfl

lemma iff_isPreimmersion {X Y : Scheme} {f : X ⟶ Y} :
    IsClosedImmersion f ↔ IsPreimmersion f ∧ IsClosed (Set.range f.1.base) := by
  rw [and_comm, isClosedImmersion_iff, isPreimmersion_iff, ← and_assoc, closedEmbedding_iff,
    @and_comm (Embedding _)]

lemma of_isPreimmersion {X Y : Scheme} (f : X ⟶ Y) [IsPreimmersion f]
    (hf : IsClosed (Set.range f.1.base)) : IsClosedImmersion f :=
  iff_isPreimmersion.mpr ⟨‹_›, hf⟩

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : IsPreimmersion f :=
  (iff_isPreimmersion.mp ‹_›).1

/-- Isomorphisms are closed immersions. -/
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f where
  base_closed := Homeomorph.closedEmbedding <| TopCat.homeoOfIso (asIso f.1.base)
  surj_on_stalks := fun _ ↦ (ConcreteCategory.bijective_of_isIso _).2

instance : MorphismProperty.IsMultiplicative @IsClosedImmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨hg.base_closed.comp hf.base_closed, fun x ↦ ?_⟩
    rw [Scheme.stalkMap_comp]
    exact (hf.surj_on_stalks x).comp (hg.surj_on_stalks (f.1.1 x))

/-- Composition of closed immersions is a closed immersion. -/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion f]
    [IsClosedImmersion g] : IsClosedImmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

/-- Composition with an isomorphism preserves closed immersions. -/
instance respectsIso : MorphismProperty.RespectsIso @IsClosedImmersion := by
  constructor <;> intro X Y Z e f hf <;> infer_instance

/-- Given two commutative rings `R S : CommRingCat` and a surjective morphism
`f : R ⟶ S`, the induced scheme morphism `specObj S ⟶ specObj R` is a
closed immersion. -/
theorem spec_of_surjective {R S : CommRingCat} (f : R ⟶ S) (h : Function.Surjective f) :
    IsClosedImmersion (Spec.map f) where
  base_closed := PrimeSpectrum.closedEmbedding_comap_of_surjective _ _ h
  surj_on_stalks x := by
    haveI : (RingHom.toMorphismProperty (fun f ↦ Function.Surjective f)).RespectsIso := by
      rw [← RingHom.toMorphismProperty_respectsIso_iff]
      exact surjective_respectsIso
    apply (MorphismProperty.arrow_mk_iso_iff
      (RingHom.toMorphismProperty (fun f ↦ Function.Surjective f))
      (Scheme.arrowStalkMapSpecIso f x)).mpr
    exact surjective_localRingHom_of_surjective f h x.asIdeal

/-- For any ideal `I` in a commutative ring `R`, the quotient map `specObj R ⟶ specObj (R ⧸ I)`
is a closed immersion. -/
instance spec_of_quotient_mk {R : CommRingCat.{u}} (I : Ideal R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Any morphism between affine schemes that is surjective on global sections is a
closed immersion. -/
lemma of_surjective_of_isAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : Function.Surjective (Scheme.Γ.map f.op)) : IsClosedImmersion f := by
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (arrowIsoSpecΓOfIsAffine f)]
  apply spec_of_surjective
  exact h

/-- If `f ≫ g` is a closed immersion, then `f` is a closed immersion. -/
theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsClosedImmersion g]
    [IsClosedImmersion (f ≫ g)] : IsClosedImmersion f where
  base_closed := by
    have h := closedEmbedding (f ≫ g)
    rw [Scheme.comp_val_base] at h
    apply closedEmbedding_of_continuous_injective_closed (Scheme.Hom.continuous f)
    · exact Function.Injective.of_comp h.inj
    · intro Z hZ
      rw [ClosedEmbedding.closed_iff_image_closed (closedEmbedding g),
        ← Set.image_comp]
      exact ClosedEmbedding.isClosedMap h _ hZ
  surj_on_stalks x := by
    have h := (f ≫ g).stalkMap_surjective x
    simp_rw [Scheme.comp_val, Scheme.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

instance {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : QuasiCompact f where
  isCompact_preimage _ _ hU' := base_closed.isCompact_preimage hU'

end IsClosedImmersion

/-- Being a closed immersion is local at the target. -/
instance IsClosedImmersion.isLocalAtTarget : IsLocalAtTarget @IsClosedImmersion :=
  eq_inf ▸ inferInstance

end AlgebraicGeometry
