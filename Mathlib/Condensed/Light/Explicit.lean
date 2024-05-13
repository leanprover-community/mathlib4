/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Coherent.Equivalence
import Mathlib.Condensed.Explicit
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

namespace LightProfinite

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : LightProfinite.{u}ᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition_general]

end LightProfinite

namespace LightCondensed

/--
The condensed set associated to a presheaf on `Profinite` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : LightCondensed A where
    val := F
    cond := by
      rw [LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨⟨fun _ _ ↦ inferInstance⟩⟩, hF⟩

end LightCondensed

namespace LightCondSet

/-- A `LightCondSet` version of `LightCondensed.ofSheafLightProfinite`. -/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
  LightCondensed.ofSheafLightProfinite F hF

/-- A light condensed set satisfies the equalizer condition. -/
theorem equalizerCondition (X : LightCondSet) : EqualizerCondition X.val :=
  LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    X.val |>.mp X.cond |>.2

/-- A light condensed set preserves finite products. -/
noncomputable instance (X : LightCondSet.{u}) : PreservesFiniteProducts X.val :=
  LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    X.val |>.mp X.cond |>.1.some

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
