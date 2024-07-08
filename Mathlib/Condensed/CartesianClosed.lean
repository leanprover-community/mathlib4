import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Closed.Ideal
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.Condensed.Discrete
import Mathlib.Condensed.Limits
import Mathlib.Condensed.TopCatAdjunction

universe u

noncomputable section

open CategoryTheory Condensed CondensedSet Limits CompactlyGenerated

instance : CartesianClosed (CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) :=
  let e : CompHaus.{u}ᵒᵖ ⥤ Type (u+1) ≌ (ULiftHom.{u+1} (CompHaus.{u}))ᵒᵖ ⥤ Type (u+1) :=
    Functor.asEquivalence ((whiskeringLeft _ _ _).obj ULiftHom.equiv.op.inverse)
  -- We need to make `CompHaus` a small category relative to `Type (u+1)`.
  cartesianClosedOfEquiv e.symm

instance :
    Reflective (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))) where
  map_surjective := (fullyFaithfulSheafToPresheaf _ _).map_surjective
  map_injective := (fullyFaithfulSheafToPresheaf _ _).map_injective
  adj := sheafificationAdjunction _ _

instance :
    PreservesLimitsOfShape (Discrete (WalkingPair))
      (reflector (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))) :=
  inferInstanceAs (PreservesLimitsOfShape _ (presheafToSheaf _ _))

instance : CartesianClosed (CondensedSet.{u}) :=
  cartesianClosedOfReflective (sheafToPresheaf _ _)

example :
    condensedSetToTopCat ⋙ (forget TopCat) ≅ Condensed.underlying _ :=
  Iso.refl _

instance : PreservesLimits (Condensed.underlying (Type (u + 1))) :=
  (discreteUnderlyingAdj _).rightAdjointPreservesLimits

-- TODO: this is not true, but perhaps it is for finite limits?
instance : ReflectsLimits (forget TopCat.{u}) := sorry

instance : PreservesLimits condensedSetToTopCat.{u} :=
  have : PreservesLimits (condensedSetToTopCat ⋙ (forget TopCat)) :=
    inferInstanceAs (PreservesLimits (Condensed.underlying (Type (u + 1))))
  preservesLimitsOfReflectsOfPreserves condensedSetToTopCat (forget TopCat)

example :
    condensedSetToCompactlyGenerated ⋙ compactlyGeneratedToTop ≅ condensedSetToTopCat :=
  Iso.refl _

instance : HasLimits CompactlyGenerated.{u, u+1} :=
  hasLimits_of_reflective compactlyGeneratedToCondensedSet

instance : PreservesLimits condensedSetToCompactlyGenerated :=
  have : PreservesLimits (condensedSetToCompactlyGenerated ⋙ compactlyGeneratedToTop) :=
    inferInstanceAs (PreservesLimits condensedSetToTopCat)
  preservesLimitsOfReflectsOfPreserves condensedSetToCompactlyGenerated compactlyGeneratedToTop

instance : PreservesLimitsOfShape (Discrete WalkingPair)
    condensedSetToCompactlyGenerated :=
  inferInstance

instance : ExponentialIdeal compactlyGeneratedToCondensedSet :=
  have : PreservesLimitsOfShape (Discrete WalkingPair)
      (reflector compactlyGeneratedToCondensedSet) :=
    inferInstanceAs (PreservesLimitsOfShape _ condensedSetToCompactlyGenerated)
  exponentialIdeal_of_preservesBinaryProducts _

instance : CartesianClosed CompactlyGenerated.{u, u+1} :=
  cartesianClosedOfReflective compactlyGeneratedToCondensedSet
