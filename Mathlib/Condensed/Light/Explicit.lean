/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Riccardo Brasca, Filippo A. E. Nuccio
-/
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.Condensed.Explicit
import Mathlib.Condensed.Light.Abelian
/-!

# The explicit sheaf condition for light condensed sets


-/

universe v u

open CategoryTheory Limits Opposite Functor Presieve regularCoverage

namespace LightProfinite

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  -- let e := equivSmallModel LightProfinite.{u}
  rw [isSheaf_coherent_iff_regular_and_extensive]
  apply and_congr
  · let J := (extensiveCoverage LightProfinite).toGrothendieck
    have h₁ := isSheaf_iff_preservesFiniteProducts (F ⋙ uliftFunctor.{u+1})
    have h₂ := Presheaf.isSheaf_of_isSheaf_comp J F uliftFunctor.{u+1}
    have h₃ : GrothendieckTopology.HasSheafCompose J uliftFunctor.{u+1, u} := inferInstance
    have : (Presheaf.IsSheaf _ (F ⋙ _)) ↔ Presheaf.IsSheaf _ F := ⟨h₂, h₃.isSheaf F⟩
    rw [isSheaf_iff_isSheaf_of_type, isSheaf_iff_isSheaf_of_type] at this
    rw [← this, h₁]
    refine ⟨fun ⟨h⟩ ↦ ⟨⟨fun J _ ↦ ?_⟩⟩, fun ⟨h⟩ ↦ ⟨⟨fun J _ ↦ ?_⟩⟩⟩
    · exact preservesLimitsOfShapeOfReflectsOfPreserves _ uliftFunctor
    · infer_instance
  · exact EqualizerCondition.isSheaf_iff F

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    {A : Type (u+1)} [Category.{u} A] (G : A ⥤ Type u)
    [h : HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] (F : LightProfinite.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (coherentTopology LightProfinite) F ↔
    Nonempty (PreservesFiniteProducts (F ⋙ G)) ∧ EqualizerCondition (F ⋙ G) := by
  -- haveI : HasLimitsOfSize.{u, u+1} A := sorry (false in general)
  -- have : PreservesLimitsOfSize.{u, u + 1} G := sorry
  -- rw [Presheaf.isSheaf_iff_isSheaf_comp (s := G)]
  let J := coherentTopology LightProfinite
  have h₂ := Presheaf.isSheaf_of_isSheaf_comp J (F ⋙ G) uliftFunctor.{u+1}
  -- have h₂' := Presheaf.isSheaf_of_isSheaf_comp J F (G ⋙ uliftFunctor.{u+1})
  have h₃' : GrothendieckTopology.HasSheafCompose J (G ⋙ uliftFunctor.{u+1, u}) := inferInstance
  have h₃ : GrothendieckTopology.HasSheafCompose J uliftFunctor.{u+1, u} := inferInstance
  have : (Presheaf.IsSheaf _ (F ⋙ (G ⋙ uliftFunctor.{u+1}))) ↔ Presheaf.IsSheaf _ (F ⋙ G) :=
    ⟨h₂, h₃.isSheaf (F ⋙ G)⟩
  -- rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology LightProfinite) F (G ⋙ uliftFunctor.{u+1}),
  --   isSheaf_iff_isSheaf_of_type, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  sorry

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

#exit

namespace CondensedSet

/-- A `CondensedSet` version of `Condensed.ofSheafStonean`. -/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)) [PreservesFiniteProducts F] :
    CondensedSet :=
  Condensed.ofSheafStonean (𝟭 _) F

/-- A `CondensedSet` version of `Condensed.ofSheafProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafProfinite (𝟭 _) F hF

/-- A `CondensedSet` version of `Condensed.ofSheafCompHaus`. -/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafCompHaus (𝟭 _) F hF

/-- A condensed set satisfies the equalizer condition. -/
theorem equalizerCondition (X : CondensedSet) : EqualizerCondition X.val :=
  CompHaus.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition' (𝟭 _) X.val |>.mp X.cond |>.2

/-- A condensed set preserves finite products. -/
noncomputable instance (X : CondensedSet) : PreservesFiniteProducts X.val :=
  CompHaus.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition' (𝟭 _) X.val |>.mp
    X.cond |>.1.some

end CondensedSet

namespace CondensedAb

/-- A `CondensedAb` version of `Condensed.ofSheafStonean`. -/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ AddCommGroupCat.{u+1})
    [PreservesFiniteProducts F] : CondensedAb :=
  Condensed.ofSheafStonean (forget _) F

/-- A `CondensedAb` version of `Condensed.ofSheafProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u+1})
    [PreservesFiniteProducts F] (hF : EqualizerCondition (F ⋙ forget _)) : CondensedAb :=
  Condensed.ofSheafProfinite (forget _) F hF

/-- A `CondensedAb` version of `Condensed.ofSheafCompHaus`. -/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ AddCommGroupCat.{u+1})
    [PreservesFiniteProducts F] (hF : EqualizerCondition (F ⋙ forget _)) : CondensedAb :=
  Condensed.ofSheafCompHaus (forget _) F hF

end CondensedAb
