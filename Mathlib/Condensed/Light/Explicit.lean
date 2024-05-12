/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Coherent.Equivalence
import Mathlib.Condensed.Explicit
import Mathlib.Condensed.Light.Basic
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

namespace LightProfinite

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : LightProfinite.{u}ᵒᵖ ⥤ Type w) :
    IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  rw [isSheaf_coherent_iff_regular_and_extensive]
  apply and_congr
  · rw [isSheaf_iff_isSheaf_of_type, extensiveTopology, isSheaf_iff_preservesFiniteProducts]
  · rw [← equalizerCondition_iff_isSheaf]

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    {A : Type*} [Category A] (G : A ⥤ Type w)
    [HasLimitsOfSize.{u, u+1} A] [PreservesLimitsOfSize.{u, u+1} G]
    [G.ReflectsIsomorphisms] (F : LightProfinite.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts (F ⋙ G)) ∧ EqualizerCondition (F ⋙ G) := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp (coherentTopology LightProfinite) F G,
    isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]

end LightProfinite

namespace LightCondensed

variable {A : Type*} [Category A] (G : A ⥤ Type w)
    [HasLimitsOfSize.{u, u+1} A] [PreservesLimitsOfSize.{u, u+1} G]
    [G.ReflectsIsomorphisms]

noncomputable instance : PreservesLimitsOfSize.{0, 0} G :=
  preservesLimitsOfSizeShrink.{0, u+1, 0, u} _

/--
The condensed set associated to a presheaf on `Profinite` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition (F ⋙ G)) : LightCondensed A where
    val := F
    cond := by
      rw [LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition' G F]
      exact ⟨⟨⟨fun _ _ ↦ inferInstance⟩⟩, hF⟩

end LightCondensed

-- namespace LightCondSet

-- /-- A `LightCondSet` version of `LightCondensed.ofSheafLightProfinite`. -/
-- noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
--     [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
--   LightCondensed.ofSheafLightProfinite (𝟭 _) F hF

-- /-- A light condensed set satisfies the equalizer condition. -/
-- theorem equalizerCondition (X : LightCondSet) : EqualizerCondition X.val :=
--   LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
--     (𝟭 _) X.val |>.mp X.cond |>.2

-- /-- A light condensed set preserves finite products. -/
-- noncomputable instance (X : LightCondSet.{u}) : PreservesFiniteProducts X.val :=
--   LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
--     (𝟭 _) X.val |>.mp X.cond |>.1.some

-- end LightCondSet

-- namespace LightCondAb

-- /-- A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`. -/
-- noncomputable abbrev ofSheafProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u})
--     [PreservesFiniteProducts F] (hF : EqualizerCondition (F ⋙ forget _)) : LightCondAb :=
--   LightCondensed.ofSheafLightProfinite (forget _) F hF

-- end LightCondAb
