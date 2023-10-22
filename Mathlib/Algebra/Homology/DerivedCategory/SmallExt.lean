import Mathlib.Algebra.Homology.DerivedCategory.LargeExt
import Mathlib.Logic.Small.Group

universe w w' w'' v u u' u''

noncomputable def addEquivShrink (α : Type v) [AddCommGroup α] [Small.{w} α] :
    α ≃+ Shrink α where
  toEquiv := equivShrink α
  map_add' := by simp

namespace CategoryTheory

open Limits

section

variable {C : Type*} [Category C]

@[simps]
def equivHomOfIsos {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    (X ⟶ Y) ≃ (X' ⟶ Y') where
  toFun f := e.inv ≫ f ≫ e'.hom
  invFun g := e.hom ≫ g ≫ e'.inv
  left_inv := by aesop_cat
  right_inv := by aesop_cat

@[simps!]
def addEquivHomOfIsos [Preadditive C] {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := equivHomOfIsos e e'
  map_add' := by aesop_cat

end

namespace Functor

variable {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [Full F] [Faithful F]

@[simps]
def equivHomOfFullOfFaithful (X Y : C) : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := by aesop_cat
  right_inv := by aesop_cat

@[simps!]
def addEquivHomOfFullOfFaithful [Preadditive C] [Preadditive D] [F.Additive] (X Y : C) :
    (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) where
  toEquiv := F.equivHomOfFullOfFaithful X Y
  map_add' f g := by aesop_cat

end Functor

section

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{w'} D] (L : C ⥤ D) [L.IsLocalization W]
  {D' : Type u''} [Category.{w''} D'] (L' : C ⥤ D') [L'.IsLocalization W]
  (X Y : C)

namespace MorphismProperty

class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

noncomputable def localizationsEquivHom :
    (L.obj X ⟶ L.obj Y) ≃ (L'.obj X ⟶ L'.obj Y) :=
  ((Localization.uniq L L' W).functor.equivHomOfFullOfFaithful (L.obj X) (L.obj Y)).trans
    (equivHomOfIsos ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

noncomputable def localizationsAddEquivHom [Preadditive C] [Preadditive D] [Preadditive D']
    [L.Additive] [L'.Additive] [HasFiniteProducts C] [HasFiniteProducts D] :
    (L.obj X ⟶ L.obj Y) ≃+ (L'.obj X ⟶ L'.obj Y) := by
  have : (Localization.uniq L L' W).functor.Additive := by
    rw [← Localization.functor_additive_iff L W L' (Localization.uniq L L' W).functor]
    infer_instance
  exact ((Localization.uniq L L' W).functor.addEquivHomOfFullOfFaithful (L.obj X) (L.obj Y)).trans
    (addEquivHomOfIsos ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  have e := localizationsEquivHom W W.Q L X Y
  constructor
  · intro h
    have := h.small
    exact small_map e.symm
  · intro h
    exact ⟨small_map e⟩

end MorphismProperty

end

namespace Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]

class HasSmallExt : Prop where
  hasSmallLocalizedHom (X Y : C) (n : ℕ) :
    MorphismProperty.HasSmallLocalizedHom.{w}
      (HomologicalComplex.qis C (ComplexShape.up ℤ))
      ((CochainComplex.singleFunctor C 0).obj X)
      ((CochainComplex.singleFunctor C (-n)).obj Y)

lemma hasSmallExt_iff_hasSmallLocalizedHom :
    HasSmallExt.{w} C ↔
      ∀ (X Y : C) (n : ℕ), MorphismProperty.HasSmallLocalizedHom.{w}
      (HomologicalComplex.qis C (ComplexShape.up ℤ))
      ((CochainComplex.singleFunctor C 0).obj X)
      ((CochainComplex.singleFunctor C (-n)).obj Y) :=
  ⟨fun h => h.hasSmallLocalizedHom, fun h => ⟨h⟩⟩

variable {C}

noncomputable def largeExtAddEquivHom [HasDerivedCategory.{w'} C] (X Y : C) (n : ℕ) :
    LargeExt X Y n ≃+
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-n)).obj Y)) :=
  addEquivHomOfIsos
    (((SingleFunctors.evaluation _ _ 0).mapIso
      (DerivedCategory.singleFunctorsPostCompQIso C)).app X)
    (((DerivedCategory.singleFunctors C).shiftIso n (-n) 0 (by linarith)).app Y ≪≫
      ((SingleFunctors.evaluation _ _ (-n : ℤ)).mapIso
      (DerivedCategory.singleFunctorsPostCompQIso C)).app Y)

variable (C)

lemma hasSmallExt_iff_small_largeExt [HasDerivedCategory.{w'} C] :
    HasSmallExt.{w} C ↔ ∀ (X Y : C) (n : ℕ), Small.{w} (LargeExt X Y n) := by
  suffices ∀ (X Y : C) (n : ℕ), Small.{w}
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-n)).obj Y)) ↔
      Small.{w} (LargeExt X Y n) by
    simp only [hasSmallExt_iff_hasSmallLocalizedHom,
      MorphismProperty.hasSmallLocalizedHom_iff _ DerivedCategory.Q, this]
  intro X Y n
  exact small_congr (largeExtAddEquivHom X Y n).symm

instance [HasDerivedCategory.{w} C] : HasSmallExt.{w} C := by
  rw [hasSmallExt_iff_small_largeExt]
  intro X Y n
  infer_instance

instance : HasSmallExt.{max u v} C := by
  have : HasDerivedCategory.{max u v} C :=
    MorphismProperty.HasLocalization.standard _
  infer_instance

instance [HasDerivedCategory.{w'} C] [h : HasSmallExt.{w} C] (X Y : C) (n : ℕ) :
    Small.{w} (LargeExt X Y n) := by
  rw [hasSmallExt_iff_small_largeExt] at h
  infer_instance

variable {C}

def SmallExt [HasSmallExt.{w} C] (X Y : C) (n : ℕ) : Type w :=
  have : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  Shrink (LargeExt.{max u v} X Y n)

noncomputable instance [HasSmallExt.{w} C] (X Y : C) (n : ℕ) :
    AddCommGroup (SmallExt.{w} X Y n) := by
  dsimp [SmallExt]
  infer_instance

abbrev newExt [HasSmallExt.{v} C] (X Y : C) (n : ℕ) : Type v := SmallExt.{v} X Y n

noncomputable def smallExtEquivLargeExt [HasSmallExt.{w} C] [HasDerivedCategory.{w'} C]
    (X Y : C) (n : ℕ) :
    SmallExt.{w} X Y n ≃+ LargeExt.{w'} X Y n := by
  letI : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  exact (addEquivShrink (LargeExt.{max u v} X Y n)).symm.trans
    ((largeExtAddEquivHom.{max u v} X Y n).trans
    ((MorphismProperty.localizationsAddEquivHom
      (HomologicalComplex.qis C (ComplexShape.up ℤ)) _ _ _ _).trans
    ((largeExtAddEquivHom.{w'} X Y n)).symm))

end Abelian

end CategoryTheory
