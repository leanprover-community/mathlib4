import Mathlib.Algebra.Homology.DerivedCategory.LargeExt

universe w w' w'' v u u' u''

namespace CategoryTheory

section

variable {C : Type*} [Category C]

def homEquivOfIsos {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') :
    (X ⟶ Y) ≃ (X' ⟶ Y') where
  toFun f := e.inv ≫ f ≫ e'.hom
  invFun g := e.hom ≫ g ≫ e'.inv
  left_inv := by aesop_cat
  right_inv := by aesop_cat

end

namespace Functor

variable {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [Full F] [Faithful F]

def homEquiv (X Y : C) : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := by aesop_cat
  right_inv := by aesop_cat

end Functor

section

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{w'} D] (L : C ⥤ D) [L.IsLocalization W]
  {D' : Type u''} [Category.{w''} D'] (L' : C ⥤ D') [L'.IsLocalization W]
  (X Y : C)

namespace MorphismProperty

class HasSmallLocalizedHom : Prop where
  small : Small.{w} (W.Q.obj X ⟶ W.Q.obj Y)

noncomputable def localizationsHomEquiv :
    (L.obj X ⟶ L.obj Y) ≃ (L'.obj X ⟶ L'.obj Y) :=
  ((Localization.uniq L L' W).functor.homEquiv (L.obj X) (L.obj Y)).trans
    (homEquivOfIsos ((Localization.compUniqFunctor L L' W).app X)
      ((Localization.compUniqFunctor L L' W).app Y))

lemma hasSmallLocalizedHom_iff :
    HasSmallLocalizedHom.{w} W X Y ↔ Small.{w} (L.obj X ⟶ L.obj Y) := by
  have e := localizationsHomEquiv W W.Q L X Y
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

lemma hasSmallExt_iff_small_largeExt [HasDerivedCategory.{w'} C] :
    HasSmallExt.{w} C ↔ ∀ (X Y : C) (n : ℕ), Small.{w} (LargeExt X Y n) := by
  suffices ∀ (X Y : C) (n : ℕ), Small.{w}
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-n)).obj Y)) ↔
      Small.{w} (LargeExt X Y n) by
    simp only [hasSmallExt_iff_hasSmallLocalizedHom,
      MorphismProperty.hasSmallLocalizedHom_iff _ DerivedCategory.Q, this]
  intro X Y n
  apply small_congr
  apply homEquivOfIsos
  · exact ((SingleFunctors.evaluation _ _ 0).mapIso
      (DerivedCategory.singleFunctorsPostCompQIso C)).symm.app X
  · exact ((SingleFunctors.evaluation _ _ (-n : ℤ)).mapIso
      (DerivedCategory.singleFunctorsPostCompQIso C)).symm.app Y ≪≫
      ((DerivedCategory.singleFunctors C).shiftIso n (-n) 0 (by linarith)).symm.app Y

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

abbrev newExt [HasSmallExt.{v} C] (X Y : C) (n : ℕ) : Type v := SmallExt.{v} X Y n

/-def smallExtEquivLargeExt [HasDerivedCategory.{w'} C] (X Y : C) (n : ℕ) :
    SmallExt X Y n ≃ LargeExt X Y n := by
  sorry-/

end Abelian

end CategoryTheory
