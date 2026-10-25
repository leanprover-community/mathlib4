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
# Bounded above cochain complexes

In this file, we consider the full subcategory `CochainComplex.Minus C`
of `CochainComplex C ℤ` consisting of bounded above cochain complexes
in a category `C`.

This file should be kept in sync with `Mathlib/Algebra/Homology/CochainComplexPlus.lean`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category* C]

/-- The property of cochain complexes that are bounded above. -/
protected def minus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyLE n

lemma minus_iff [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    CochainComplex.minus C K ↔ ∃ (n : ℤ), K.IsStrictlyLE n := Iff.rfl

instance [HasZeroMorphisms C] : (CochainComplex.minus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyLE_of_iso e n⟩

/-- The full subcategory of `CochainComplex C ℤ` consisting of bounded above complexes. -/
abbrev Minus [HasZeroMorphisms C] :=
  (CochainComplex.minus C).FullSubcategory

namespace Minus

section

variable [HasZeroMorphisms C]

/-- The inclusion of the full subcategory of bounded above cochain complexes. -/
abbrev ι : Minus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

/-- The inclusion of the full subcategory of bounded above cochain complexes
is fully faithful. -/
def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance (J : Type*) [SmallCategory J] [FinCategory J] [HasLimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyLE_of_le _ _ (Finset.le_max' _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_tgt _ _)

instance (J : Type*) [SmallCategory J] [FinCategory J] [HasColimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ (n : ℤ), ∀ (j : J), (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by grind⟩, fun j ↦
        (p.diag.obj j).isStrictlyLE_of_le _ _ (Finset.le_max' _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext
      (fun j ↦ (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_src _ _)

instance [HasFiniteLimits C] : HasFiniteLimits (Minus C) where
  out J _ _ := by infer_instance

instance [HasFiniteColimits C] : HasFiniteColimits (Minus C) where
  out J _ _ := by infer_instance

variable {C} in
lemma mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : Minus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom :=
  ⟨fun _ ↦ inferInstanceAs (Mono ((ι C).map f)),
    fun _ ↦ Functor.mono_of_mono_map (ι C) (by assumption)⟩

instance [HasLimitsOfShape WalkingCospan C] {X Y : Minus C} (f : X ⟶ Y) [Mono f] :
    Mono f.hom := by
  rwa [← mono_iff]

/-- The class of quasi-isomorphisms in the category of bounded
above cochain complexes. -/
def quasiIso [CategoryWithHomology C] : MorphismProperty (Minus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

lemma quasiIso_iff [CategoryWithHomology C] {X Y : Minus C} (f : X ⟶ Y) :
    quasiIso C f ↔ QuasiIso f.hom := Iff.rfl

instance [CategoryWithHomology C] : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance

instance [CategoryWithHomology C] : (quasiIso C).IsStableUnderRetracts := by
  dsimp [quasiIso]
  infer_instance

end

instance [Preadditive C] : (CochainComplex.minus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun K ⟨k, hk⟩ ↦ ⟨k - n, K.isStrictlyLE_shift k n _ (by lia)⟩⟩

instance [Preadditive C] [CategoryWithHomology C] :
    (CochainComplex.Minus.quasiIso C).IsCompatibleWithShift ℤ where
  condition a := by
    ext K L f
    have := MorphismProperty.IsCompatibleWithShift.iff (HomologicalComplex.quasiIso _ _) f.hom a
    simp only [HomologicalComplex.mem_quasiIso_iff,
      MorphismProperty.inverseImage_iff, quasiIso_iff] at this ⊢
    rw [← this]
    exact quasiIso_iff_of_arrow_mk_iso _ _
      (((Functor.mapArrowFunctor _ _).mapIso ((Minus.ι C).commShiftIso a)).app (Arrow.mk f))

end Minus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

/-- The functor on categories of bounded above cochain complexes that
is induced by a functor (which preserves zero morphisms). -/
@[implicit_reducible, simps! obj_obj map_hom]
def mapCochainComplexMinus : CochainComplex.Minus C ⥤ CochainComplex.Minus D :=
  ObjectProperty.lift _ (CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Minus.ι]
    infer_instance)

/-- The isomorphism between `F.mapCochainComplexMinus ⋙ CochainComplex.Minus.ι D`
and `CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _` when `F : C ⥤ D`
is a functor which preserves zero morphisms -/
@[simps! hom_app inv_app]
def mapCochainComplexMinusCompι :
    F.mapCochainComplexMinus ⋙ CochainComplex.Minus.ι D ≅
      CochainComplex.Minus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

section

variable [Preadditive C] [Preadditive D] [F.Additive]

noncomputable instance : F.mapCochainComplexMinus.CommShift ℤ :=
  ObjectProperty.commShiftLift ..

instance : NatTrans.CommShift F.mapCochainComplexMinusCompι.hom ℤ :=
  ObjectProperty.commShift_liftCompιIso_hom ..

open HomologicalComplex in
lemma homotopyEquivalences_mapCochainComplexMinus_map {K L : CochainComplex.Minus C} (f : K ⟶ L)
    (hf : homotopyEquivalences C (.up ℤ) f.hom) :
    homotopyEquivalences D (.up ℤ) (F.mapCochainComplexMinus.map f).hom :=
  F.homotopyEquivalences_mapHomologicalComplex_map _ hf

end

end Functor

namespace NatTrans

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {F₁ F₂ F₃ : C ⥤ D} [F₁.Additive] [F₂.Additive] [F₃.Additive]

/-- The natural transformation `F₁.mapCochainComplexMinus ⟶ F₂.mapCochainComplexMinus`
induced by a natural transformation `F₁ ⟶ F₂`. -/
@[simps! app_hom]
def mapCochainComplexMinus (τ : F₁ ⟶ F₂) :
    F₁.mapCochainComplexMinus ⟶ F₂.mapCochainComplexMinus where
  app K := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex τ _).app _)

@[simp]
lemma mapCochainComplexMinus_add (τ τ' : F₁ ⟶ F₂) :
    (τ + τ').mapCochainComplexMinus = τ.mapCochainComplexMinus + τ'.mapCochainComplexMinus := rfl

variable (F₁) in
@[simp]
lemma mapCochainComplexMinus_id :
    NatTrans.mapCochainComplexMinus (𝟙 F₁) = 𝟙 _ := by cat_disch

@[reassoc]
lemma mapCochainComplexMinus_comp (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    (τ ≫ τ').mapCochainComplexMinus =
      τ.mapCochainComplexMinus ≫ τ'.mapCochainComplexMinus := by cat_disch

instance (τ : F₁ ⟶ F₂) : τ.mapCochainComplexMinus.CommShift ℤ :=
  NatTrans.CommShift.of_comp_faithful (ObjectProperty.ι _) (by
    have :
        Functor.whiskerRight τ.mapCochainComplexMinus (CochainComplex.Minus.ι D) =
          F₁.mapCochainComplexMinusCompι.hom ≫ Functor.whiskerLeft _ (τ.mapHomologicalComplex _) ≫
            F₂.mapCochainComplexMinusCompι.inv := by cat_disch
    rw [this]
    infer_instance)

end NatTrans

end CategoryTheory
