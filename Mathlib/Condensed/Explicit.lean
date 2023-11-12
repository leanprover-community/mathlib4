/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Riccardo Brasca, Filippo A. E. Nuccio
-/

import Mathlib.Condensed.Equivalence
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Stonean.EffectiveEpi

/-!

We give the following three explicit descriptions of condensed sets:

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `Stonean`.

* `Condensed.ofSheafProfinite`: A finite-product-preserving presheaf on `Profinite`, satisfying
  `EqualizerCondition`.

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `CompHaus`, satisfying
  `EqualizerCondition`.

The property `EqualizerCondition` is defined in `Mathlib/CategoryTheory/Sites/RegularExtensive`
and it says that for any effective epi `X ⟶ B` (in this case that is equivalent to being a
continuous surjection), the presheaf `F` exhibits `F(B)` as the equalizer of the two maps
`F(X) ⇉ F(X ×_B X)`
-/

universe v u

open CategoryTheory Limits Opposite Functor Presieve

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type (max u v)) [Preregular C]
  [FinitaryPreExtensive C] [Precoherent C]

theorem isSheaf_coherent_iff_regular_and_extensive : IsSheaf (coherentTopology C) F ↔
    IsSheaf (extensiveCoverage C).toGrothendieck F ∧
    IsSheaf (regularCoverage C).toGrothendieck F := by
  rw [← extensive_regular_generate_coherent]
  exact isSheaf_sup (extensiveCoverage C) (regularCoverage C) F

end CategoryTheory

namespace CompHaus

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) :
    IsSheaf (coherentTopology CompHaus) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  rw [isSheaf_coherent_iff_regular_and_extensive]
  apply and_congr
  · exact isSheaf_iff_preservesFiniteProducts F
  · exact isSheaf_iff_equalizerCondition F

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    {A : Type (u+2)} [Category.{u+1} A] (G : A ⥤ Type (u+1))
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] (F : CompHaus.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (coherentTopology CompHaus) F ↔
    Nonempty (PreservesFiniteProducts (F ⋙ G)) ∧ EqualizerCondition (F ⋙ G) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology CompHaus) F G,
    isSheaf_iff_isSheaf_of_type, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]

instance {A B : Type*} [Category A] [Category B] (F : B ⥤ A) (E : A)  [PreservesFiniteProducts F] :
    PreservesFiniteProducts (F ⋙ coyoneda.obj (op E)) :=
  ⟨fun J _ ↦ @compPreservesLimitsOfShape _ _ _ _ _ _ _ _ F (coyoneda.obj (op E))
    (PreservesFiniteProducts.preserves J) ((preservesLimitsOfSizeShrink _).preservesLimitsOfShape)⟩

end CompHaus

namespace Profinite

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) :
    IsSheaf (coherentTopology Profinite) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  rw [isSheaf_coherent_iff_regular_and_extensive]
  apply and_congr
  · exact isSheaf_iff_preservesFiniteProducts F
  · exact isSheaf_iff_equalizerCondition F

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition'
    {A : Type (u+2)} [Category.{u+1} A] (G : A ⥤ Type (u+1))
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] (F : Profinite.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (coherentTopology Profinite) F ↔
    Nonempty (PreservesFiniteProducts (F ⋙ G)) ∧ EqualizerCondition (F ⋙ G) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology Profinite) F G,
    isSheaf_iff_isSheaf_of_type, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]

end Profinite

namespace Stonean

theorem isSheaf_iff_preservesFiniteProducts
    (F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)) :
    IsSheaf (coherentTopology Stonean) F ↔ Nonempty (PreservesFiniteProducts F) := by
  rw [isSheaf_coherent_iff_regular_and_extensive, and_iff_left ?_]
  · exact CategoryTheory.isSheaf_iff_preservesFiniteProducts F
  · rw [Presieve.isSheaf_coverage]
    intro X R ⟨Y, hR⟩
    have _ : R.regular := ⟨Y, hR⟩
    exact isSheafFor_regular_of_projective R F

theorem isSheaf_iff_preservesFiniteProducts'
    {A : Type (u+2)} [Category.{u+1} A] (G : A ⥤ Type (u+1))
    [HasLimits A] [PreservesLimits G] [ReflectsIsomorphisms G] (F : Stonean.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (coherentTopology Stonean) F ↔
    Nonempty (PreservesFiniteProducts (F ⋙ G)) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (coherentTopology Stonean) F G,
    isSheaf_iff_isSheaf_of_type, isSheaf_iff_preservesFiniteProducts]

end Stonean

namespace Condensed

/-- The condensed set associated to a finite-product-preserving presheaf on `Stonean`. -/
noncomputable def ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)) [PreservesFiniteProducts F] :
    CondensedSet.{u} :=
  StoneanCompHaus.equivalence (Type (u+1)) |>.functor.obj {
    val := F
    cond := by
      rw [Stonean.isSheaf_iff_preservesFiniteProducts' (𝟭 _) F, Functor.comp_id]
      exact ⟨inferInstance⟩ }

/--
The condensed set associated to a presheaf on `Profinite` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : CondensedSet.{u} :=
  ProfiniteCompHaus.equivalence (Type (u+1)) |>.functor.obj {
    val := F
    cond := by
      rw [Profinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition' (𝟭 _) F,
        Functor.comp_id]
      exact ⟨⟨inferInstance⟩, hF⟩ }

/--
The condensed set associated to a presheaf on `CompHaus` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : CondensedSet.{u} where
  val := F
  cond := by
    rw [CompHaus.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition' (𝟭 _) F,
        Functor.comp_id]
    exact ⟨⟨inferInstance⟩, hF⟩

end Condensed
