/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Riccardo Brasca, Filippo A. E. Nuccio
-/
import Mathlib.Condensed.Module
import Mathlib.Condensed.Equivalence
/-!

# The explicit sheaf condition for condensed sets

We give the following three explicit descriptions of condensed sets:

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `Stonean`.

* `Condensed.ofSheafProfinite`: A finite-product-preserving presheaf on `Profinite`, satisfying
  `EqualizerCondition`.

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `CompHaus`, satisfying
  `EqualizerCondition`.

The property `EqualizerCondition` is defined in `Mathlib/CategoryTheory/Sites/RegularSheaves.lean`
and it says that for any effective epi `X ⟶ B` (in this case that is equivalent to being a
continuous surjection), the presheaf `F` exhibits `F(B)` as the equalizer of the two maps
`F(X) ⇉ F(X ×_B X)`
-/

universe v u w

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

variable {A : Type*} [Category A]

namespace CompHaus

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : CompHaus.{u}ᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology CompHaus) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition_general]

end CompHaus

namespace Profinite

theorem isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
    (F : Profinite.{u}ᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology Profinite) F ↔
    Nonempty (PreservesFiniteProducts F) ∧ EqualizerCondition F := by
  rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition_general]

end Profinite

namespace Stonean

theorem isSheaf_iff_preservesFiniteProducts
    (F : Stonean.{u}ᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology Stonean) F ↔ Nonempty (PreservesFiniteProducts F) := by
  rw [isSheaf_coherent_iff_regular_and_extensive, and_iff_left ?_]
  · rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  · exact isSheaf_of_projective F

end Stonean

namespace Condensed

variable {A : Type*} [Category A] (G : A ⥤ Type w)

/-- The condensed set associated to a finite-product-preserving presheaf on `Stonean`. -/
noncomputable def ofSheafStonean
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] :
    Condensed A :=
  StoneanCompHaus.equivalence A |>.functor.obj {
    val := F
    cond := by
      rw [Stonean.isSheaf_iff_preservesFiniteProducts F]
      exact ⟨⟨fun _ _ ↦ inferInstance⟩⟩ }

/--
The condensed set associated to a presheaf on `Profinite` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafProfinite
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A :=
  ProfiniteCompHaus.equivalence A |>.functor.obj {
    val := F
    cond := by
      rw [Profinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨⟨fun _ _ ↦ inferInstance⟩⟩, hF⟩ }

/--
The condensed set associated to a presheaf on `CompHaus` which preserves finite products and
satisfies the equalizer condition.
-/
noncomputable def ofSheafCompHaus
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A where
  val := F
  cond := by
    rw [CompHaus.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨⟨fun _ _ ↦ inferInstance⟩⟩, hF⟩

end Condensed

namespace CondensedSet

/-- A `CondensedSet` version of `Condensed.ofSheafStonean`. -/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u+1)) [PreservesFiniteProducts F] :
    CondensedSet :=
  Condensed.ofSheafStonean F

/-- A `CondensedSet` version of `Condensed.ofSheafProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafProfinite F hF

/-- A `CondensedSet` version of `Condensed.ofSheafCompHaus`. -/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u+1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafCompHaus F hF

/-- A condensed set satisfies the equalizer condition. -/
theorem equalizerCondition (X : CondensedSet) : EqualizerCondition X.val :=
  CompHaus.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.2

/-- A condensed set preserves finite products. -/
noncomputable instance (X : CondensedSet) : PreservesFiniteProducts X.val :=
  CompHaus.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp
    X.cond |>.1.some

/-- A condensed set regarded as a sheaf on `Profinite` preserves finite products. -/
noncomputable instance (Y : Sheaf (coherentTopology Profinite.{u}) (Type (u+1))) :
    PreservesFiniteProducts Y.val :=
  Profinite.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition Y.val |>.mp
    Y.cond |>.1.some

/-- A condensed set regarded as a sheaf on `Stonean` preserves finite products. -/
noncomputable instance (Y : Sheaf (coherentTopology Stonean.{u}) (Type (u+1))) :
    PreservesFiniteProducts Y.val :=
  Stonean.isSheaf_iff_preservesFiniteProducts Y.val |>.mp Y.cond |>.some

end CondensedSet

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

/-- A `CondensedMod` version of `Condensed.ofSheafStonean`. -/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u+1} R)
    [PreservesFiniteProducts F] : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u+1} (ModuleCat R) := hasLimitsOfSizeShrink.{u, u+1, u+1, u+1} _
  Condensed.ofSheafStonean F

/-- A `CondensedMod` version of `Condensed.ofSheafProfinite`. -/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u+1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u+1} (ModuleCat R) := hasLimitsOfSizeShrink.{u, u+1, u+1, u+1} _
  Condensed.ofSheafProfinite F hF

/-- A `CondensedMod` version of `Condensed.ofSheafCompHaus`. -/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u+1} (ModuleCat R) := hasLimitsOfSizeShrink.{u, u+1, u+1, u+1} _
  Condensed.ofSheafCompHaus F hF

end CondensedMod
