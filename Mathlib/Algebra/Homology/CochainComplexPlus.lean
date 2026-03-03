/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Bounded below cochain complexes

In this file, we consider the full subcategory `CochainComplex.Plus C`
of `CochainComplex C ℤ` consisting of bounded below cocahin complexes
in a category `C`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category* C]

/-- The property of cochain complexes that are bounded below. -/
protected def plus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyGE n

instance [HasZeroMorphisms C] : (CochainComplex.plus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyGE_of_iso e n⟩

/-- The full subcategory of `CochainComplex C ℤ` consisting of bounded below complexes. -/
abbrev Plus [HasZeroMorphisms C] :=
  (CochainComplex.plus C).FullSubcategory

namespace Plus

section

variable [HasZeroMorphisms C]

/-- The inclusion of the full subcategory of bounded below cochain complexes. -/
abbrev ι : Plus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

/-- The inclusion of the full subcategory of bounded below cochain complexes. -/
def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance (J : Type) [Category J] [FinCategory J] [HasLimitsOfShape J C] :
    (CochainComplex.plus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_tgt _ _)

instance (J : Type) [Category J] [FinCategory J] [HasColimitsOfShape J C] :
    (CochainComplex.plus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_src _ _)

instance [HasFiniteLimits C] : HasFiniteLimits (Plus C) where
  out J _ _ := by infer_instance

instance [HasFiniteColimits C] : HasFiniteColimits (Plus C) where
  out J _ _ := by infer_instance

variable {C} in
lemma mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom :=
  ⟨fun _ ↦ inferInstanceAs (Mono ((ι C).map f)),
    fun _ ↦ Functor.mono_of_mono_map (ι C) (by assumption)⟩

/-- The class of quasi-isomorphisms in the category of bounded
below cochain complexes. -/
def quasiIso [CategoryWithHomology C] : MorphismProperty (Plus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

instance [CategoryWithHomology C] : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance

instance [CategoryWithHomology C] : (quasiIso C).IsStableUnderRetracts := by
  dsimp [quasiIso]
  infer_instance


end

instance [Preadditive C] : (CochainComplex.plus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun K ⟨k, hk⟩ ↦ ⟨k - n, K.isStrictlyGE_shift k n _ (by lia)⟩⟩

end Plus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

/-- The functor on categories of bounded below cochain complexes that
is induced by a functor (which preserves zero morphisms). -/
@[simps!]
def mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Plus.ι]
    infer_instance)

/-- The isomorphism between `F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D`
and `CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _` when `F : C ⥤ D`
is a functor which preserves zero morphisms -/
@[simps!]
def mapCochainComplexPlusCompι :
    F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D ≅
      CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory
