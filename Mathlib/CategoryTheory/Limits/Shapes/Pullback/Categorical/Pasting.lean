/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Square

/-! # Pasting calculus of Categorical pullback squares.

In this file, we prove that the well-known pasting calculus for
pullbacks extends to categorical pullbacks.
More precisely, given a diagram of categories

```
  C₁ - T₁ -> C₂ - T₂ -> C₃
  |          |          |
  V₁         V₂         V₃
  |          |          |
  ∨          ∨          ∨
  C₄ - B₁ -> C₅ - B₂ -> C₆
```

with natural isomorphisms filling in the squares,
assuming the rightmost square is a categorical pullback square,
then the left square is a categorical pullback square if and only
if the outer square is a categorical pullback square.

-/

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.Limits

open Limits.CategoricalPullback
open scoped Limits.CategoricalPullback

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {C₄ : Type u₄} {C₅ : Type u₅} {C₆ : Type u₆}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{v₄} C₄] [Category.{v₅} C₅] [Category.{v₆} C₆]

namespace CatPullbackSquare

section hComp

-- This prevents some degree of defeq abuse
seal functorEquiv.inverse functorEquiv.counitIsoAppFst
  functorEquiv.counitIsoAppSnd

variable (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃)
  (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
  (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆)
  [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂]
  [CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂)]
  (h : CatCommSq.iso (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) =
    (CatCommSq.hComp T₁ T₂ V₁ V₂ V₃ B₁ B₂).iso)
  [CatPullbackSquare T₂ V₂ V₃ B₂]

section

variable [CatPullbackSquare T₁ V₁ V₂ B₁]

/-- (impl.) A `CatCommSqOver` that describes a functor `V₃ ⊡ (B₁ ⋙ B₂) ⥤ C₂` -/
@[simps]
def hComp.S₀ : CatCommSqOver V₃ B₂ (V₃ ⊡ (B₁ ⋙ B₂)) where
  fst := π₁ _ _
  snd := π₂ _ _ ⋙ B₁
  iso := CatCommSq.iso (π₁ _ _) (π₂ _ _) V₃ (B₁ ⋙ B₂) ≪≫
    (Functor.associator _ _ _).symm

/-- (impl.) A `CatCommSqOver` that describes the functor `V₃ ⊡ (B₁ ⋙ B₂) ⥤ C₁`
that will be used as the quasi-inverse to the canonical functor
`C₁ ⥤ V₃ ⊡ (B₁ ⋙ B₂)` induced by the horizontal composite square. -/
@[simps]
def hComp.S₁ : CatCommSqOver V₂ B₁ (V₃ ⊡ (B₁ ⋙ B₂)) where
  fst := functorEquiv T₂ V₂ V₃ B₂ (V₃ ⊡ (B₁ ⋙ B₂))|>.inverse.obj <|
    hComp.S₀ V₃ B₁ B₂
  snd := π₂ _ _
  iso := functorEquivInverseWhiskeringIsoSnd _ _ _ _ _|>.app _

/-- The functor `V₃ ⊡ (B₁ ⋙ B₂) ⥤ C₁` that
will be used as the quasi-inverse to the canonical functor `C₁ ⥤ V₃ ⊡ (B₁ ⋙ B₂)`
induced by the horizontal composite square. -/
abbrev hCompInverse : V₃ ⊡ (B₁ ⋙ B₂) ⥤ C₁ :=
  functorEquiv T₁ V₁ V₂ B₁ _|>.inverse.obj <| hComp.S₁ T₂ V₂ V₃ B₁ B₂

/-- (Impl.) the counit isomorphism for the `CatPullbackSquare` structure on
the horizontal composition of two categorical pullback squares. -/
def hCompCounitIso :
    hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂ ⋙
      (CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
        (.ofSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂)) ≅
    𝟭 (V₃ ⊡ (B₁ ⋙ B₂)) :=
  mkNatIso (π₁ V₃ (B₁ ⋙ B₂)) (π₂ V₃ (B₁ ⋙ B₂)) V₃ (B₁ ⋙ B₂) (V₃ ⊡ (B₁ ⋙ B₂))
    ((hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator _ (π₁ V₃ (B₁ ⋙ B₂)) ≪≫
      (hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).isoWhiskerLeft
        (Iso.refl _ : _ ≅ T₁ ⋙ T₂) ≪≫
        ((hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator T₁ T₂).symm ≪≫
        (Functor.isoWhiskerRight
          (functorEquivInverseWhiskeringIsoFst
            T₁ V₁ V₂ B₁ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₁ T₂ V₂ V₃ B₁ B₂)
          T₂) ≪≫
        (functorEquivInverseWhiskeringIsoFst
          T₂ V₂ V₃ B₂ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₀ V₃ B₁ B₂) ≪≫
        (π₁ V₃ (B₁ ⋙ B₂)).leftUnitor.symm)
    ((hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator _ (π₂ V₃ (B₁ ⋙ B₂)) ≪≫
      (hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).isoWhiskerLeft
        (Iso.refl _ : _ ≅ V₁) ≪≫
      (functorEquivInverseWhiskeringIsoSnd
        T₁ V₁ V₂ B₁ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₁ T₂ V₂ V₃ B₁ B₂) ≪≫
      (π₂ V₃ (B₁ ⋙ B₂)).leftUnitor.symm)
    (by
      ext x
      have coh1 := counitCoherence_hom_app T₁ V₁ (hComp.S₁ T₂ V₂ V₃ B₁ B₂) x
      have coh2 := counitCoherence_hom_app T₂ V₂ (hComp.S₀ V₃ B₁ B₂) x
      simp only [Functor.comp_obj, functorEquiv_functor_obj_fst, hComp.S₁_snd,
        Functor.whiskeringRight_obj_obj, π₂_obj, Functor.id_obj, hComp.S₁_fst,
        hComp.S₁_iso, Iso.app_hom,
        functorEquivInverseWhiskeringIsoSnd_hom_app_app, hComp.S₀_snd,
        functorEquiv_functor_obj_snd, hComp.S₀_fst, π₁_obj, hComp.S₀_iso,
        Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, catCommSq_iso_hom_app,
        Functor.associator_inv_app, Category.comp_id] at coh1 coh2
      simp [h, coh2, ← Functor.map_comp, coh1])

/-- (Impl.) the unit isomorphism for the `CatPullbackSquare` structure on
the horizontal composition of two categorical pullback squares. -/
def hCompUnitIso :
    𝟭 C₁ ≅
    (CatCommSqOver.toFunctorToCategoricalPullback _ _ _|>.obj <|
      .ofSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂)) ⋙
      hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂ :=
  letI U := (CatCommSqOver.toFunctorToCategoricalPullback V₃ (B₁ ⋙ B₂) C₁).obj
    (CatCommSqOver.ofSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂))
  letI Ψ :
      𝟭 C₁ ⋙ T₁ ≅
      U ⋙ (functorEquiv T₂ V₂ V₃ B₂ V₃ ⊡ (B₁ ⋙ B₂)).inverse.obj
        (hComp.S₀ V₃ B₁ B₂) :=
    mkNatIso T₂ V₂ V₃ B₂ _
      ((𝟭 C₁).associator T₁ T₂ ≪≫ (T₁ ⋙ T₂).leftUnitor ≪≫
        Functor.isoWhiskerLeft U
          (functorEquivInverseWhiskeringIsoFst
            T₂ V₂ V₃ B₂ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₀ V₃ B₁ B₂).symm ≪≫
        (U.associator _ T₂).symm)
      ((𝟭 C₁).associator T₁ V₂ ≪≫ (T₁ ⋙ V₂).leftUnitor ≪≫
        (CatCommSq.iso T₁ V₁ V₂ B₁) ≪≫
        (Functor.isoWhiskerRight (Iso.refl _ : _ ≅ V₁) B₁) ≪≫
        (Functor.associator U (π₂ V₃ (B₁ ⋙ B₂)) B₁) ≪≫
        U.isoWhiskerLeft
          (functorEquivInverseWhiskeringIsoSnd
            T₂ V₂ V₃ B₂ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₀ V₃ B₁ B₂).symm ≪≫
        (U.associator _ V₂).symm)
  mkNatIso T₁ V₁ V₂ B₁ C₁
    (Ψ ≪≫
      U.isoWhiskerLeft
        (functorEquivInverseWhiskeringIsoFst
          T₁ V₁ V₂ B₁ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₁ T₂ V₂ V₃ B₁ B₂).symm ≪≫
        (U.associator (hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂) T₁).symm)
    (V₁.leftUnitor ≪≫
      U.isoWhiskerLeft
        (functorEquivInverseWhiskeringIsoSnd
          T₁ V₁ V₂ B₁ (V₃ ⊡ (B₁ ⋙ B₂))|>.app <| hComp.S₁ T₂ V₂ V₃ B₁ B₂).symm ≪≫
      (U.associator (hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂) V₁).symm)

/-- If two `CatPullbackSquare`s are pasted horizontally, the resulting square
is a `CatPullbackSquare`. -/
def hComp : CatPullbackSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  inverse := hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂
  unitIso := hCompUnitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
  counitIso := hCompCounitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
  functorEquiv_inverse_obj_unitIso_comp x := by
    ext <;> dsimp [hCompUnitIso, hCompCounitIso]
    · simp [← Functor.map_comp_assoc]
    · simp

end

section

variable [CatPullbackSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂)]

/-- (impl.) A `CatCommSq` that defines a functor `V₂ ⊡ B₁ ⥤ C₁` that
will be inverse to the canonical functor. -/
@[simps]
def ofHComp.S₀ : CatCommSqOver V₃ (B₁ ⋙ B₂) V₂ ⊡ B₁ where
  fst := π₁ _ _ ⋙ T₂
  snd := π₂ _ _
  iso :=
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (π₁ _ _) (CatCommSq.iso T₂ V₂ V₃ B₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatCommSq.iso (π₁ V₂ B₁) (π₂ V₂ B₁) V₂ B₁) B₂ ≪≫
    Functor.associator _ _ _

/-- (impl.) A functor `V₂ ⊡ B₁ ⥤ C₁` that will be inverse of the canonical
morphism to the categorical pullaback. -/
abbrev ofHCompInverse : V₂ ⊡ B₁ ⥤ C₁ :=
    functorEquiv (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _|>.inverse.obj <|
      ofHComp.S₀ T₂ V₂ V₃ B₁ B₂

/-- (impl.) The unit isomorphism for the equivalence `V₂ ⊡ B₁ ≌ C₁` that will
exhibit the left square as a categorical pullback square if the outer and right
squares are categorical pullback squares. -/
def ofHCompUnitIso :
    𝟭 C₁ ≅
    (CatCommSqOver.toFunctorToCategoricalPullback _ _ _|>.obj <|
      .ofSquare T₁ V₁ V₂ B₁) ⋙
      (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂) :=
  letI U := CatCommSqOver.toFunctorToCategoricalPullback V₂ B₁ C₁|>.obj <|
    .ofSquare T₁ V₁ V₂ B₁
  mkNatIso (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _
    ((T₁ ⋙ T₂).leftUnitor ≪≫
      Functor.isoWhiskerRight (.refl _ : _ ≅ T₁) T₂ ≪≫
      U.associator (π₁ V₂ B₁) T₂ ≪≫
      Functor.isoWhiskerLeft U
        (functorEquivInverseWhiskeringIsoFst
          (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _|>.app <| ofHComp.S₀ T₂ V₂ V₃ B₁ B₂).symm ≪≫
      (U.associator (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂) (T₁ ⋙ T₂)).symm)
    (V₁.leftUnitor ≪≫
      Functor.isoWhiskerLeft U
        (functorEquivInverseWhiskeringIsoSnd
          (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _|>.app <| ofHComp.S₀ T₂ V₂ V₃ B₁ B₂).symm ≪≫
      (U.associator (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂) V₁).symm)
    (by
      ext x
      simpa [U, h] using
        (counitCoherence_inv_app (T₁ ⋙ T₂) V₁ (ofHComp.S₀ T₂ V₂ V₃ B₁ B₂)
          (U.obj x)))

/-- (impl.) The counit isomorphism for the equivalence `V₂ ⊡ B₁ ≌ C₁` that will
exhibit the left square as a categorical pullback square if the outer and right
squares are categorical pullback squares. -/
def ofHCompCounitIso :
    ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂ ⋙
      (CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
        (.ofSquare T₁ V₁ V₂ B₁) ≅
    𝟭 (V₂ ⊡ B₁) :=
  letI Ψ : (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂) ⋙ T₁ ≅ π₁ V₂ B₁ :=
    mkNatIso T₂ V₂ V₃ B₂ _
      ((ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator T₁ T₂ ≪≫
        (functorEquivInverseWhiskeringIsoFst
          (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _|>.app <| ofHComp.S₀ T₂ V₂ V₃ B₁ B₂))
      ((ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator T₁ V₂ ≪≫
        (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).isoWhiskerLeft
          (CatCommSq.iso T₁ V₁ V₂ B₁) ≪≫
        (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂|>.associator V₁ B₁).symm ≪≫
        Functor.isoWhiskerRight
          (functorEquivInverseWhiskeringIsoSnd
            (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _|>.app <| ofHComp.S₀ T₂ V₂ V₃ B₁ B₂) B₁ ≪≫
        (CatCommSq.iso (π₁ V₂ B₁) (π₂ V₂ B₁) V₂ B₁).symm)
      (by
        ext x
        simpa [h] using
          counitCoherence_hom_app (T₁ ⋙ T₂) V₁
            (ofHComp.S₀ T₂ V₂ V₃ B₁ B₂) x =≫
            (B₂.map x.iso.inv))
  mkNatIso (π₁ V₂ B₁) (π₂ V₂ B₁) V₂ B₁ _
    ((ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator _ (π₁ V₂ B₁) ≪≫
      (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).isoWhiskerLeft (.refl _ : _ ≅ T₁) ≪≫
      Ψ ≪≫ (π₁ V₂ B₁).leftUnitor.symm)
    ((ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).associator _ (π₂ V₂ B₁) ≪≫
      (ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂).isoWhiskerLeft (.refl _ : _ ≅ V₁) ≪≫
      (functorEquivInverseWhiskeringIsoSnd
        (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) _|>.app <| ofHComp.S₀ T₂ V₂ V₃ B₁ B₂) ≪≫
        (π₂ V₂ B₁).leftUnitor.symm)
    (by
      ext x
      simp [Ψ])

/-- If two `CatCommSq`s are pasted horizontally and if the right outer squares
are `CatPullbackSquare`s, then the left square is a `CatPullbackSquare`. -/
def ofHComp : CatPullbackSquare T₁ V₁ V₂ B₁ where
  inverse := ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂
  unitIso := ofHCompUnitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
  counitIso := ofHCompCounitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
  functorEquiv_inverse_obj_unitIso_comp x := by
    ext <;> dsimp [ofHCompUnitIso, ofHCompCounitIso]
    · apply IsCatPullbackSquare.hom_ext T₂ V₂ V₃ B₂
      · simp [← Functor.comp_map]
      · simp [← Functor.map_comp_assoc]
    · simp

end

end hComp

section vComp

-- This prevents some degree of defeq abuse
seal functorEquiv.inverse functorEquiv.counitIsoAppFst
  functorEquiv.counitIsoAppSnd

variable (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃)
  (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
  (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆)
  [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃]
  [CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃]
  (h : CatCommSq.iso H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ =
    (CatCommSq.vComp L₁ L₂ H₁ H₂ H₃ R₁ R₂).iso)
  [CatPullbackSquare H₂ L₂ R₂ H₃]

section

variable [CatPullbackSquare H₁ L₁ R₁ H₂]

/-- (impl.) A `CatCommSqOver` that describes a functor `(R₁ ⋙ R₂) ⊡ H₃ ⥤ C₃` -/
@[simps]
def vComp.S₀ : CatCommSqOver R₂ H₃ ((R₁ ⋙ R₂) ⊡ H₃) where
  fst := π₁ _ _ ⋙ R₁
  snd := π₂ _ _
  iso := Functor.associator _ _ _ ≪≫
    CatCommSq.iso (π₁ _ _) (π₂ _ _) (R₁ ⋙ R₂) H₃

/-- (impl.) A `CatCommSqOver` that describes the functor `(R₁ ⋙ R₂) ⊡ H₃ ⥤ C₁`
that will be used as the quasi-inverse to the canonical functor
`C₁ ⥤ (R₁ ⋙ R₂) ⊡ H₃` induced by the vertical composite square. -/
@[simps]
def vComp.S₁ : CatCommSqOver R₁ H₂ ((R₁ ⋙ R₂) ⊡ H₃) where
  fst := π₁ _ _
  snd := functorEquiv H₂ L₂ R₂ H₃ ((R₁ ⋙ R₂) ⊡ H₃)|>.inverse.obj <|
    vComp.S₀ H₃ R₁ R₂
  iso := (functorEquivInverseWhiskeringIsoFst H₂ L₂ R₂ H₃ _|>.app <|
    vComp.S₀ H₃ R₁ R₂).symm

/-- The functor `(R₁ ⋙ R₂) ⊡ H₃ ⥤ C₁` that
will be used as the quasi-inverse to the canonical functor `C₁ ⥤ (R₁ ⋙ R₂) ⊡ H₃`
induced by the vertical composite square. -/
abbrev vCompInverse : (R₁ ⋙ R₂) ⊡ H₃ ⥤ C₁ :=
  functorEquiv H₁ L₁ R₁ H₂ _|>.inverse.obj <| vComp.S₁ L₂ H₂ H₃ R₁ R₂

/-- (Impl.) the counit isomorphism for the `CatPullbackSquare` structure on
the vertical composition of two categorical pullback squares. -/
def vCompCounitIso :
    vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂ ⋙
      (CatCommSqOver.toFunctorToCategoricalPullback (R₁ ⋙ R₂) H₃ C₁).obj
        (.ofSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃) ≅
    𝟭 ((R₁ ⋙ R₂) ⊡ H₃) :=
  mkNatIso (π₁ (R₁ ⋙ R₂) H₃) (π₂ (R₁ ⋙ R₂) H₃) (R₁ ⋙ R₂) H₃ ((R₁ ⋙ R₂) ⊡ H₃)
    ((vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator _ (π₁ (R₁ ⋙ R₂) H₃) ≪≫
      (vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).isoWhiskerLeft
        (Iso.refl _ : _ ≅ H₁) ≪≫
      (functorEquivInverseWhiskeringIsoFst
        H₁ L₁ R₁ H₂ ((R₁ ⋙ R₂) ⊡ H₃)|>.app <| vComp.S₁ L₂ H₂ H₃ R₁ R₂) ≪≫
      (π₁ (R₁ ⋙ R₂) H₃).leftUnitor.symm)
    ((vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator _ (π₂ (R₁ ⋙ R₂) H₃) ≪≫
      (vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).isoWhiskerLeft
        (Iso.refl _ : _ ≅ L₁ ⋙ L₂) ≪≫
        ((vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator L₁ L₂).symm ≪≫
        (Functor.isoWhiskerRight
          (functorEquivInverseWhiskeringIsoSnd
            H₁ L₁ R₁ H₂ ((R₁ ⋙ R₂) ⊡ H₃)|>.app <| vComp.S₁ L₂ H₂ H₃ R₁ R₂)
          L₂) ≪≫
        (functorEquivInverseWhiskeringIsoSnd
          H₂ L₂ R₂ H₃ _|>.app <| vComp.S₀ H₃ R₁ R₂) ≪≫
        (π₂ (R₁ ⋙ R₂) H₃).leftUnitor.symm)
    (by
      ext x
      have coh1 := (congrArg (fun t ↦ R₂.map t) <|
        counitCoherence_hom_app H₁ L₁ (vComp.S₁ L₂ H₂ H₃ R₁ R₂) x) =≫
          (R₂.map <|
            (functorEquiv H₂ L₂ R₂ H₃ (R₁ ⋙ R₂) ⊡ H₃|>.counitIso.hom.app <|
              vComp.S₀ H₃ R₁ R₂).fst.app x)
      have coh2 := counitCoherence_hom_app H₂ L₂ (vComp.S₀ H₃ R₁ R₂) x
      simp only [Functor.comp_obj, functorEquiv_functor_obj_fst, Functor.id_obj,
        vComp.S₀_fst, π₁_obj, vComp.S₁_snd, Functor.whiskeringRight_obj_obj,
        vComp.S₁_fst, vComp.S₁_iso, Iso.symm_hom, Iso.app_inv,
        functorEquivInverseWhiskeringIsoFst_inv_app_app, ← Functor.map_comp,
        Category.assoc, CatCommSqOver.Iso.inv_hom_id_app_fst_app,
        Category.comp_id, functorEquiv_functor_obj_snd, vComp.S₀_snd, π₂_obj,
        vComp.S₀_iso, Iso.trans_hom, NatTrans.comp_app, Category.id_comp,
        Functor.associator_hom_app, catCommSq_iso_hom_app] at coh1 coh2
      dsimp
      simp only [functorEquivInverseWhiskeringIsoFst_hom_app_app, vComp.S₁_fst,
        Category.comp_id, Category.id_comp, coh1, h,
        CatCommSq.vComp_iso_hom_app, vComp.S₁_snd, vComp.S₀_snd,
        functorEquivInverseWhiskeringIsoSnd_hom_app_app, Category.assoc]
      simp [coh2])

/-- (Impl.) the unit isomorphism for the `CatPullbackSquare` structure on
the vertical composition of two categorical pullback squares. -/
def vCompUnitIso :
    𝟭 C₁ ≅
    (CatCommSqOver.toFunctorToCategoricalPullback (R₁ ⋙ R₂) H₃ C₁).obj
        (.ofSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃) ⋙
      vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂ :=
  letI U := (CatCommSqOver.toFunctorToCategoricalPullback (R₁ ⋙ R₂) H₃ C₁).obj
    (.ofSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃)
  letI Ψ :
      𝟭 C₁ ⋙ L₁ ≅
      U ⋙ (functorEquiv H₂ L₂ R₂ H₃ ((R₁ ⋙ R₂) ⊡ H₃)).inverse.obj
        (vComp.S₀ H₃ R₁ R₂) :=
    mkNatIso H₂ L₂ R₂ H₃ _
      ((𝟭 C₁).associator L₁ H₂ ≪≫ (L₁ ⋙ H₂).leftUnitor ≪≫
        (CatCommSq.iso H₁ L₁ R₁ H₂).symm ≪≫
        (Functor.isoWhiskerRight (Iso.refl _ : _ ≅ H₁) R₁) ≪≫
        (U.associator (π₁ (R₁ ⋙ R₂) H₃) R₁) ≪≫
        U.isoWhiskerLeft
          (functorEquivInverseWhiskeringIsoFst
            H₂ L₂ R₂ H₃ ((R₁ ⋙ R₂) ⊡ H₃)|>.app <| vComp.S₀ H₃ R₁ R₂).symm ≪≫
        (Functor.associator _ _ _).symm)
      ((𝟭 C₁).associator L₁ L₂ ≪≫ (L₁ ⋙ L₂).leftUnitor ≪≫
        U.isoWhiskerLeft
          (functorEquivInverseWhiskeringIsoSnd
            H₂ L₂ R₂ H₃ ((R₁ ⋙ R₂) ⊡ H₃)|>.app <| vComp.S₀ H₃ R₁ R₂).symm ≪≫
        (Functor.associator _ _ _).symm)
      (by ext x; simp [U, h, ← Functor.map_comp_assoc])
  mkNatIso H₁ L₁ R₁ H₂ C₁
    (H₁.leftUnitor ≪≫
      U.isoWhiskerLeft
        (functorEquivInverseWhiskeringIsoFst
          H₁ L₁ R₁ H₂ ((R₁ ⋙ R₂) ⊡ H₃)|>.app <| vComp.S₁ L₂ H₂ H₃ R₁ R₂).symm ≪≫
      (Functor.associator _ _ _).symm)
    (Ψ ≪≫
      U.isoWhiskerLeft
        (functorEquivInverseWhiskeringIsoSnd
          H₁ L₁ R₁ H₂ ((R₁ ⋙ R₂) ⊡ H₃)|>.app <| vComp.S₁ L₂ H₂ H₃ R₁ R₂).symm ≪≫
        (Functor.associator _ _ _).symm)

/-- If two `CatPullbackSquare`s are pasted vertically, the resulting square
is a `CatPullbackSquare`. -/
def vComp : CatPullbackSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  inverse := vCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂
  unitIso := vCompUnitIso L₁ L₂ H₁ H₂ H₃ R₁ R₂ h
  counitIso := vCompCounitIso L₁ L₂ H₁ H₂ H₃ R₁ R₂ h
  functorEquiv_inverse_obj_unitIso_comp x := by
    ext <;> dsimp [vCompUnitIso, vCompCounitIso]
    · simp
    · simp [← Functor.map_comp_assoc]

end

section

variable [CatPullbackSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃]

/-- (impl.) A `CatCommSq` that defines a functor `R₁ ⊡ H₂ ⥤ C₁` that
will be inverse to the canonical functor. -/
@[simps]
def ofVComp.S₀ : CatCommSqOver (R₁ ⋙ R₂) H₃ (R₁ ⊡ H₂) where
  fst := π₁ _ _
  snd := π₂ _ _ ⋙ L₂
  iso :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CatCommSq.iso (π₁ R₁ H₂) (π₂ R₁ H₂) R₁ H₂) R₂ ≪≫
    (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (π₂ R₁ H₂) (CatCommSq.iso H₂ L₂ R₂ H₃) ≪≫
    (Functor.associator _ _ _).symm

/-- (impl.) A functor `R₁ ⊡ H₂ ⥤ C₁` that will be inverse of the canonical
morphism to the categorical pullaback. -/
abbrev ofVCompInverse : R₁ ⊡ H₂ ⥤ C₁ :=
    functorEquiv H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _|>.inverse.obj <|
      ofVComp.S₀ L₂ H₂ H₃ R₁ R₂

/-- (impl.) The unit isomorphism for the equivalence `R₁ ⊡ H₂ ≌ C₁` that will
exhibit the left square as a categorical pullback if the outer square and right
squares are categorical pullback squares. -/
def ofVCompUnitIso :
    𝟭 C₁ ≅
    (CatCommSqOver.toFunctorToCategoricalPullback R₁ H₂ C₁|>.obj <|
      .ofSquare H₁ L₁ R₁ H₂) ⋙
      ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂ :=
  letI U := CatCommSqOver.toFunctorToCategoricalPullback R₁ H₂ C₁|>.obj <|
    .ofSquare H₁ L₁ R₁ H₂
  mkNatIso H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _
    (H₁.leftUnitor ≪≫
      U.isoWhiskerLeft
        (functorEquivInverseWhiskeringIsoFst
          H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _|>.app <| ofVComp.S₀ L₂ H₂ H₃ R₁ R₂).symm ≪≫
      (U.associator (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂) H₁).symm)
    ((L₁ ⋙ L₂).leftUnitor ≪≫
      Functor.isoWhiskerRight (.refl _ : _ ≅ L₁) L₂ ≪≫
      U.associator (π₂ R₁ H₂) L₂ ≪≫
      U.isoWhiskerLeft
        (functorEquivInverseWhiskeringIsoSnd
          H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _|>.app <| ofVComp.S₀ L₂ H₂ H₃ R₁ R₂).symm ≪≫
      (U.associator (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂) (L₁ ⋙ L₂)).symm)
    (by
      ext x
      simpa [U, h] using
        (counitCoherence_inv_app H₁ (L₁ ⋙ L₂) (ofVComp.S₀ L₂ H₂ H₃ R₁ R₂)
          (U.obj x)))

/-- (impl.) The counit isomorphism for the equivalence `R₁ ⊡ H₂ ≌ C₁` that will
exhibit the left square as a categorical pullback if the outer square and right
squares are categorical pullback squares. -/
def ofVCompCounitIso :
    ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂ ⋙
      (CatCommSqOver.toFunctorToCategoricalPullback R₁ H₂ C₁).obj
        (.ofSquare H₁ L₁ R₁ H₂) ≅
    𝟭 (R₁ ⊡ H₂) :=
  letI Ψ : (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂) ⋙ L₁ ≅ π₂ R₁ H₂ :=
    mkNatIso H₂ L₂ R₂ H₃ _
      ((ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator L₁ H₂ ≪≫
        (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).isoWhiskerLeft
          (CatCommSq.iso H₁ L₁ R₁ H₂).symm ≪≫
        (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂|>.associator H₁ R₁).symm ≪≫
        Functor.isoWhiskerRight
          (functorEquivInverseWhiskeringIsoFst
            H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _|>.app <| ofVComp.S₀ L₂ H₂ H₃ R₁ R₂) R₁ ≪≫
        (CatCommSq.iso (π₁ R₁ H₂) (π₂ R₁ H₂) R₁ H₂))
      ((ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator L₁ L₂ ≪≫
        (functorEquivInverseWhiskeringIsoSnd
          H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _|>.app <| ofVComp.S₀ L₂ H₂ H₃ R₁ R₂))
      (by
        ext x
        haveI := counitCoherence_inv_app H₁ (L₁ ⋙ L₂)
            (ofVComp.S₀ L₂ H₂ H₃ R₁ R₂) x =≫
          H₃.map ((functorEquiv H₁ (L₁ ⋙ L₂) _ _ _|>.counitIso.hom.app <|
            ofVComp.S₀ L₂ H₂ H₃ R₁ R₂).snd.app x)
        dsimp at this
        simp only [h, CatCommSq.vComp_iso_hom_app, Category.assoc,
          Category.comp_id, Category.id_comp, ← Functor.map_comp,
          CatCommSqOver.Iso.inv_hom_id_app_snd_app, Functor.id_obj,
          ofVComp.S₀_snd, Functor.comp_obj, π₂_obj, Functor.map_id] at this
        simp [← this, ← Functor.map_comp_assoc, -Functor.map_comp])
  mkNatIso (π₁ R₁ H₂) (π₂ R₁ H₂) R₁ H₂ _
    ((ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator _ (π₁ R₁ H₂) ≪≫
      (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).isoWhiskerLeft (.refl _ : _ ≅ H₁) ≪≫
      (functorEquivInverseWhiskeringIsoFst
        H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ _|>.app <| ofVComp.S₀ L₂ H₂ H₃ R₁ R₂) ≪≫
        (π₁ R₁ H₂).leftUnitor.symm)
    ((ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).associator _ (π₂ R₁ H₂) ≪≫
      (ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂).isoWhiskerLeft (.refl _ : _ ≅ L₁) ≪≫
      Ψ ≪≫ (π₂ R₁ H₂).leftUnitor.symm)
    (by
      ext x
      simp [Ψ])

/-- If two `CatCommSq`s are pasted vertically and if the bottom outer squares
are `CatPullbackSquare`s, then the top square is a `CatPullbackSquare`. -/
def ofVComp : CatPullbackSquare H₁ L₁ R₁ H₂ where
  inverse := ofVCompInverse L₁ L₂ H₁ H₂ H₃ R₁ R₂
  unitIso := ofVCompUnitIso L₁ L₂ H₁ H₂ H₃ R₁ R₂ h
  counitIso := ofVCompCounitIso L₁ L₂ H₁ H₂ H₃ R₁ R₂ h
  functorEquiv_inverse_obj_unitIso_comp x := by
    ext <;> dsimp [ofVCompUnitIso, ofVCompCounitIso]
    · simp
    · apply IsCatPullbackSquare.hom_ext H₂ L₂ R₂ H₃
      · simp [← Functor.map_comp_assoc]
      · simp [← Functor.comp_map]

end

end vComp

end CatPullbackSquare

namespace IsCatPullbackSquare

lemma isCatPullbackSquare_hComp_iff
    (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃)
    (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆)
    [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂]
    [CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂)]
    (h : CatCommSq.iso (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) =
      (CatCommSq.hComp T₁ T₂ V₁ V₂ V₃ B₁ B₂).iso)
    [hᵣ : IsCatPullbackSquare T₂ V₂ V₃ B₂] :
    IsCatPullbackSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) ↔
      IsCatPullbackSquare T₁ V₁ V₂ B₁ where
  mp h' :=
    letI := hᵣ.nonempty_catPullbackSquare.some
    letI := h'.nonempty_catPullbackSquare.some
    ⟨⟨CatPullbackSquare.ofHComp T₁ T₂ V₁ V₂ V₃ B₁ B₂ h⟩⟩
  mpr h' :=
    letI := hᵣ.nonempty_catPullbackSquare.some
    letI := h'.nonempty_catPullbackSquare.some
    ⟨⟨CatPullbackSquare.hComp T₁ T₂ V₁ V₂ V₃ B₁ B₂ h⟩⟩

lemma isCatPullbackSquare_vComp_iff
    (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃)
    (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆)
    [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃]
    [CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃]
    (h : CatCommSq.iso H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ =
      (CatCommSq.vComp L₁ L₂ H₁ H₂ H₃ R₁ R₂).iso)
    [hᵣ : IsCatPullbackSquare H₂ L₂ R₂ H₃] :
    IsCatPullbackSquare H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ ↔
      IsCatPullbackSquare H₁ L₁ R₁ H₂ where
  mp h' :=
    letI := hᵣ.nonempty_catPullbackSquare.some
    letI := h'.nonempty_catPullbackSquare.some
    ⟨⟨CatPullbackSquare.ofVComp L₁ L₂ H₁ H₂ H₃ R₁ R₂ h⟩⟩
  mpr h' :=
    letI := hᵣ.nonempty_catPullbackSquare.some
    letI := h'.nonempty_catPullbackSquare.some
    ⟨⟨CatPullbackSquare.vComp L₁ L₂ H₁ H₂ H₃ R₁ R₂ h⟩⟩

end IsCatPullbackSquare

namespace CategoricalPullback

@[simps!]
def hCompEquiv (R : C₁ ⥤ C₂) (B₁ : C₄ ⥤ C₃) (B₂ : C₃ ⥤ C₂) :
    R ⊡ (B₁ ⋙ B₂) ≌ (π₂ R B₂) ⊡ B₁ :=
  letI : CatCommSq (π₁ (π₂ R B₂) B₁ ⋙ π₁ R B₂) (π₂ (π₂ R B₂) B₁) R (B₁ ⋙ B₂) :=
    CatCommSq.hComp _ _ _ (π₂ R B₂) _ _ _
  letI :
      CatPullbackSquare
        (π₁ (π₂ R B₂) B₁ ⋙ π₁ R B₂) (π₂ (π₂ R B₂) B₁) R (B₁ ⋙ B₂) :=
    CatPullbackSquare.hComp _ _ _ _ _ _ _ rfl
  CatPullbackSquare.equivalence
    (π₁ (π₂ R B₂) B₁ ⋙ π₁ R B₂) (π₂ (π₂ R B₂) B₁) R (B₁ ⋙ B₂)|>.symm

@[simps!]
def vCompEquiv (R₁ : C₁ ⥤ C₂) (R₂ : C₂ ⥤ C₃) (B : C₄ ⥤ C₃) :
    (R₁ ⋙ R₂) ⊡ B ≌ R₁ ⊡ (π₁ R₂ B) :=
  letI : CatCommSq (π₁ R₁ (π₁ R₂ B)) (π₂ R₁ (π₁ R₂ B) ⋙ π₂ R₂ B) (R₁ ⋙ R₂) B :=
    CatCommSq.vComp _ _ _ (π₁ R₂ B) _ _ _
  letI :
      CatPullbackSquare
        (π₁ R₁ (π₁ R₂ B)) (π₂ R₁ (π₁ R₂ B) ⋙ π₂ R₂ B) (R₁ ⋙ R₂) B :=
    CatPullbackSquare.vComp _ _ _ _ _ _ _ rfl
  CatPullbackSquare.equivalence
    (π₁ R₁ (π₁ R₂ B)) (π₂ R₁ (π₁ R₂ B) ⋙ π₂ R₂ B) (R₁ ⋙ R₂) B|>.symm

end CategoricalPullback

end CategoryTheory.Limits
