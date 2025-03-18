/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Riccardo Brasca, Filippo A. E. Nuccio
-/
import Mathlib.Condensed.Module
import Mathlib.Condensed.Equivalence
/-!

# The explicit sheaf condition for condensed sets

We give the following three explicit descriptions of condensed objects:

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `Stonean`.

* `Condensed.ofSheafProfinite`: A finite-product-preserving presheaf on `Profinite`, satisfying
  `EqualizerCondition`.

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `CompHaus`, satisfying
  `EqualizerCondition`.

The property `EqualizerCondition` is defined in `Mathlib/CategoryTheory/Sites/RegularSheaves.lean`
and it says that for any effective epi `X ⟶ B` (in this case that is equivalent to being a
continuous surjection), the presheaf `F` exhibits `F(B)` as the equalizer of the two maps
`F(X) ⇉ F(X ×_B X)`

We also give variants for condensed objects in concrete categories whose forgetful functor
reflects finite limits (resp. products), where it is enough to check the sheaf condition after
postcomposing with the forgetful functor.
-/

universe u

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

namespace Condensed

variable {A : Type*} [Category A]

/-- The condensed object associated to a finite-product-preserving presheaf on `Stonean`. -/
noncomputable def ofSheafStonean
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] :
    Condensed A :=
  StoneanCompHaus.equivalence A |>.functor.obj {
    val := F
    cond := by
      rw [isSheaf_iff_preservesFiniteProducts_of_projective F]
      exact ⟨fun _ ↦ inferInstance⟩ }

/--
The condensed object associated to a presheaf on `Stonean` whose postcomposition with the
forgetful functor preserves finite products.
-/
noncomputable def ofSheafForgetStonean
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    [HasForget A] [ReflectsFiniteProducts (CategoryTheory.forget A)]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)] :
    Condensed A :=
  StoneanCompHaus.equivalence A |>.functor.obj {
    val := F
    cond := by
      apply isSheaf_coherent_of_projective_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_of_projective]
      exact ⟨fun _ ↦ inferInstance⟩ }

/--
The condensed object associated to a presheaf on `Profinite` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafProfinite
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A :=
  ProfiniteCompHaus.equivalence A |>.functor.obj {
    val := F
    cond := by
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩ }

/--
The condensed object associated to a presheaf on `Profinite` whose postcomposition with the
forgetful functor preserves finite products and satisfies the equalizer condition.
-/
noncomputable def ofSheafForgetProfinite
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    [HasForget A] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) :
    Condensed A :=
  ProfiniteCompHaus.equivalence A |>.functor.obj {
    val := F
    cond := by
      apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
      exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩ }

/--
The condensed object associated to a presheaf on `CompHaus` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafCompHaus
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A where
  val := F
  cond := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩

/--
The condensed object associated to a presheaf on `CompHaus` whose postcomposition with the
forgetful functor preserves finite products and satisfies the equalizer condition.
-/
noncomputable def ofSheafForgetCompHaus
    [HasForget A] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : Condensed A where
  val := F
  cond := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ ↦ inferInstance⟩, hF⟩

/-- A condensed object satisfies the equalizer condition. -/
theorem equalizerCondition (X : Condensed A) : EqualizerCondition X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.2

/-- A condensed object preserves finite products. -/
noncomputable instance (X : Condensed A) : PreservesFiniteProducts X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp
    X.cond |>.1

/-- A condensed object regarded as a sheaf on `Profinite` preserves finite products. -/
noncomputable instance (X : Sheaf (coherentTopology Profinite.{u}) A) :
    PreservesFiniteProducts X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp
    X.cond |>.1

/-- A condensed object regarded as a sheaf on `Profinite` satisfies the equalizer condition. -/
theorem equalizerCondition_profinite (X : Sheaf (coherentTopology Profinite.{u}) A) :
    EqualizerCondition X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.2

/-- A condensed object regarded as a sheaf on `Stonean` preserves finite products. -/
noncomputable instance (X : Sheaf (coherentTopology Stonean.{u}) A) :
    PreservesFiniteProducts X.val :=
  isSheaf_iff_preservesFiniteProducts_of_projective X.val |>.mp X.cond

end Condensed

namespace CondensedSet

/-- A `CondensedSet` version of `Condensed.ofSheafStonean`. -/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u + 1)) [PreservesFiniteProducts F] :
    CondensedSet :=
  Condensed.ofSheafStonean F

/-- A `CondensedSet` version of `Condensed.ofSheafProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafProfinite F hF

/-- A `CondensedSet` version of `Condensed.ofSheafCompHaus`. -/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafCompHaus F hF

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R]

/-- A `CondensedMod` version of `Condensed.ofSheafStonean`. -/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafStonean F

/-- A `CondensedMod` version of `Condensed.ofSheafProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafProfinite F hF

/-- A `CondensedMod` version of `Condensed.ofSheafCompHaus`. -/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  Condensed.ofSheafCompHaus F hF

end CondensedMod
