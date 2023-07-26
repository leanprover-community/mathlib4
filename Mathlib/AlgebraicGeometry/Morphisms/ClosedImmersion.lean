/-
Copyright (c) 2023 Jonas van der Schaaf. All rights
reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Amelia Livingston
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.RingTheory.LocalProperties

/-!
# Closed immersions of presheafed spaces

## Main definitions

## Implementation notes

## TODO

-/
universe v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {C : Type u} [Category.{v} C] [ConcreteCategory C] [HasColimits C]

/-- A morphism of presheafed spaces `X ⟶ Y` is a closed immersion if the underlying
topological map is a closed embedding and the induced stalk maps are surjective. -/
class PresheafedSpace.IsClosedImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  base_closed : ClosedEmbedding f.base
  surj_on_stalks : ∀ x : X, Function.Surjective (PresheafedSpace.stalkMap f x)

abbrev SheafedSpace.IsClosedImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsClosedImmersion f

abbrev LocallyRingedSpace.IsClosedImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsClosedImmersion f.1

namespace PresheafedSpace.IsClosedImmersion

open PresheafedSpace

local notation "IsClosedImmersion" => PresheafedSpace.IsClosedImmersion

instance id {X : PresheafedSpace C} : IsClosedImmersion (𝟙 X) := by
  constructor
  . apply closedEmbedding_id
  . intro x r
    use r
    rw [PresheafedSpace.stalkMap.id]
    exact Function.funext_iff.1 coe_id _

/- The file `OpenImmersion.Basic` doesn't use this `MorphismProperty` stuff,
but `Morphisms.FiniteType` does. I've emulated the latter for now, but maybe
emulating open immersions is more appropriate since they're initially defined for
presheafed spaces rather than schemes too. Will think tomorrow.
Also at the moment the naming/namespacing is a mix of those two files... - Amelia -/

/-- Suppose we have maps of presheafed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` which are both
closed immersions. Then their composition `f ≫ g : X ⟶ Z` should also be a
closed immersion. -/
theorem isClosedImmersion_stableUnderComposition :
    MorphismProperty.StableUnderComposition (@PresheafedSpace.IsClosedImmersion C _ _ _) := by
  rintro X Y Z f g ⟨hf_closed, hf_surj⟩ ⟨hg_closed, hg_surj⟩
  constructor
  . exact hg_closed.comp hf_closed
  . intro x
    rw [PresheafedSpace.stalkMap.comp]
    convert (hf_surj x).comp (hg_surj (f x))
    exact coe_comp _ _

instance isClosedImmersionComp {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : IsClosedImmersion f] [hg : IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) :=
  isClosedImmersion_stableUnderComposition f g hf hg

/-- Isomorphisms are closed immersions. -/
instance ofIsIso {X Y : PresheafedSpace C} (f : X ⟶ Y) [hf : IsIso f] :
    IsClosedImmersion f := by
  constructor
  . let f_top_iso := TopCat.homeoOfIso (asIso f.base)
    exact Homeomorph.closedEmbedding f_top_iso
  . intro x
    apply (ConcreteCategory.bijective_of_isIso _).2

variable (R : CommRingCat) (M : Submonoid R)

/-- Composition with an iso preserves closed embeddings. This is a direct
corollary from `iso_is_closed_immersion` and
`isClosedImmersion_stableUnderComposition`. -/
lemma isClosedImmersion_respectsIso :
    MorphismProperty.RespectsIso (@PresheafedSpace.IsClosedImmersion C _ _ _) := by
  constructor <;> intro X Y Z e f hf <;> apply isClosedImmersion_stableUnderComposition
  <;> infer_instance -- not sure of formatting convention here

end PresheafedSpace.IsClosedImmersion

-- This needs moving to different file
/- A surjective hom `R →+* S` induces a surjective hom `R_{f⁻¹(P)} →+* S_P`.
This is just an application of `localizationPreserves_surjective`, modulo the fact that
`IsLocalization f((f⁻¹(P))ᶜ) R_P`, since `f((f⁻¹(P))ᶜ)` is just `Pᶜ`... -/
lemma surjective_localRingHom_of_surjective {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    (h : Function.Surjective f) (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) :=
  @localizationPreserves_surjective R S _ _ f ((P.comap f).primeCompl)
    (Localization.AtPrime (P.comap f)) (Localization.AtPrime P) _ _ _ _ _
    ((Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization) h

/- This should probably be in a new file, a la `OpenImmersion.Scheme` - Amelia -/

abbrev Scheme.IsClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpace.IsClosedImmersion f

-- will check naming convention - Amelia
/-- Given two commutative rings `R S : CommRingCat` and a surjective morphism
`f : R ⟶ S`, the induced scheme morphism `specObj S ⟶ specObj R` is a
closed immersion. -/
lemma spec_of_surjective_isClosedImmersion {R S : CommRingCat} (f : R ⟶ S)
    (h : Function.Surjective f) :
    Scheme.IsClosedImmersion (Scheme.specMap (CommRingCat.ofHom f)) := by
  constructor
  . apply PrimeSpectrum.closedEmbedding_comap_of_surjective _ _ h
  . intro x
    erw [←localRingHom_comp_stalkIso, CommRingCat.coe_comp, CommRingCat.coe_comp]
    show Function.Surjective (_ ∘ _)
    apply Function.Surjective.comp (Function.Surjective.comp _ _) _
    . let stalk_iso := (StructureSheaf.stalkIso S x).inv
      exact (ConcreteCategory.bijective_of_isIso stalk_iso).2
    . exact surjective_localRingHom_of_surjective f h x.asIdeal
    . let stalk_iso := (StructureSheaf.stalkIso ((CommRingCat.of R))
        ((PrimeSpectrum.comap (CommRingCat.ofHom f)) x)).hom
      exact (ConcreteCategory.bijective_of_isIso stalk_iso).2

instance spec_of_mk_isClosedImmersion {R : CommRingCat.{u}} (I : Ideal R) :
  Scheme.IsClosedImmersion (Scheme.specMap (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
spec_of_surjective_isClosedImmersion (CommRingCat.ofHom (Ideal.Quotient.mk I))
  Ideal.Quotient.mk_surjective

end AlgebraicGeometry
