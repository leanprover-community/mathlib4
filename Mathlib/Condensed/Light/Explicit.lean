/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.Condensed.Light.Module
/-!

# The explicit sheaf condition for light condensed sets

We give explicit description of light condensed sets:

* `LightCondensed.ofSheafLightProfinite`: A finite-product-preserving presheaf on `LightProfinite`,
  satisfying `EqualizerCondition`.

The property `EqualizerCondition` is defined in `Mathlib/CategoryTheory/Sites/RegularExtensive.lean`
and it says that for any effective epi `X ⟶ B` (in this case that is equivalent to being a
continuous surjection), the presheaf `F` exhibits `F(B)` as the equalizer of the two maps
`F(X) ⇉ F(X ×_B X)`
-/

universe v u w

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

variable {A : Type*} [Category A]

namespace LightCondensed

/--
The light condensed object associated to a presheaf on `LightProfinite` which preserves finite
products and satisfies the equalizer condition.
-/
@[simps]
noncomputable def ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : LightCondensed A where
    val := F
    cond := by
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨⟨fun _ _ ↦ inferInstance⟩⟩, hF⟩

/--
The light condensed object associated to a presheaf on `LightProfinite` whose postcomposition with
the forgetful functor preserves finite products and satisfies the equalizer condition.
-/
@[simps]
noncomputable def ofSheafForgetLightProfinite
    [ConcreteCategory A] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : LightCondensed A where
  val := F
  cond := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨⟨fun _ _ ↦ inferInstance⟩⟩, hF⟩

/-- A light condensed object satisfies the equalizer condition. -/
theorem equalizerCondition (X : LightCondensed A) : EqualizerCondition X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.2

/-- A light condensed object preserves finite products. -/
noncomputable instance (X : LightCondensed A) : PreservesFiniteProducts X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.1.some

end LightCondensed

namespace LightCondSet

/-- A `LightCondSet` version of `LightCondensed.ofSheafLightProfinite`. -/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

/-- A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`. -/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondMod.{u} R :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondMod

namespace LightCondAb

/-- A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`. -/
noncomputable abbrev ofSheafLightProfinite (F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondAb :=
  LightCondMod.ofSheafLightProfinite ℤ F hF

end LightCondAb
