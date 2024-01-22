/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CoherentEquivalence
import Mathlib.Condensed.Explicit
import Mathlib.Condensed.Light.Abelian
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

universe v u

open CategoryTheory Limits Opposite Functor Presieve regularCoverage

namespace LightProfinite

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  let e := equivSmallModel LightProfinite.{u}
  rw [← isSheaf_iff_isSheaf_of_type, e.precoherent_isSheaf_iff (Type u) F]
  haveI : HasFiniteCoproducts (SmallModel.{u, u, u+1} LightProfinite) :=
    ⟨fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.inverse⟩
  haveI : HasPullbacks (SmallModel.{u, u, u+1} LightProfinite) :=
    Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  haveI : FinitaryExtensive (SmallModel.{u, u, u+1} LightProfinite) :=
    finitaryExtensive_of_preserves_and_reflects e.inverse
  rw [isSheaf_iff_isSheaf_of_type, isSheaf_coherent_iff_regular_and_extensive]
  apply and_congr
  · rw [isSheaf_iff_preservesFiniteProducts]
    have : IsEquivalence e.inverse.op := (inferInstance : IsEquivalence e.op.inverse)
    have : IsEquivalence e.functor.op := (inferInstance : IsEquivalence e.op.functor)
    refine ⟨fun ⟨h⟩ ↦ ⟨⟨fun J _ ↦ ?_⟩⟩, fun ⟨h⟩ ↦ ⟨⟨fun J _ ↦ ?_⟩⟩⟩
    · have : PreservesLimitsOfShape (Discrete J) ((e.op.functor ⋙ e.op.inverse) ⋙ F) :=
        (inferInstance : PreservesLimitsOfShape _ (e.functor.op ⋙ e.inverse.op ⋙ F))
      exact preservesLimitsOfShapeOfNatIso (isoWhiskerRight e.op.unitIso F).symm
    · infer_instance
  · rw [EqualizerCondition.isSheaf_iff]
    exact (equalizerCondition_iff_of_equivalence F e).symm

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    {A : Type (u+1)} [Category.{u} A] (G : A ⥤ Type u)
    [h : HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] (F : LightProfinite.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts (F ⋙ G)) ∧ EqualizerCondition (F ⋙ G) := by
  let e := equivSmallModel LightProfinite.{u}
  rw [e.precoherent_isSheaf_iff, Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology _)
    (e.inverse.op ⋙ F) G]
  change Presheaf.IsSheaf _ (e.inverse.op ⋙ F ⋙ G) ↔ _
  rw [← e.precoherent_isSheaf_iff, isSheaf_iff_isSheaf_of_type,
    isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]

end LightProfinite

namespace LightCondensed

variable {A : Type (u+1)} [Category.{u} A] (G : A ⥤ Type u) [HasLimits A] [PreservesLimits G]
    [ReflectsIsomorphisms G]

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

namespace LightCondSet

/-- A `LightCondSet` version of `LightCondensed.ofSheafLightProfinite`. -/
noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
  LightCondensed.ofSheafLightProfinite (𝟭 _) F hF

/-- A light condensed set satisfies the equalizer condition. -/
theorem equalizerCondition (X : LightCondSet) : EqualizerCondition X.val :=
  LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    (𝟭 _) X.val |>.mp X.cond |>.2

/-- A light condensed set preserves finite products. -/
noncomputable instance (X : LightCondSet) : PreservesFiniteProducts X.val :=
  LightProfinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    (𝟭 _) X.val |>.mp X.cond |>.1.some

end LightCondSet

namespace LightCondAb

/-- A `LightCondAb` version of `LightCondensed.ofSheafLightProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u})
    [PreservesFiniteProducts F] (hF : EqualizerCondition (F ⋙ forget _)) : LightCondAb :=
  LightCondensed.ofSheafLightProfinite (forget _) F hF

end LightCondAb
