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

### TODOs
- Vertical composition
- Give good (d)simp lemmas when both squares as the default ones, *i.e*
give good lemmas for the equivalence `V₃ ⊡ (B₁ ⋙ B₂) ≌ (π₁ T₂ V₂) ⊡ B₁`.
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

section

variable [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂]
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
def hComp :
    CatPullbackSquare (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) :=
  { inverse := hCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂
    unitIso := hCompUnitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
    counitIso := hCompCounitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
    functorEquiv_inverse_obj_unitIso_comp x := by
      ext <;> dsimp [hCompUnitIso, hCompCounitIso]
      · simp [← Functor.map_comp_assoc]
      · simp }

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
def ofHComp :
    CatPullbackSquare T₁ V₁ V₂ B₁ :=
  { inverse := ofHCompInverse T₁ T₂ V₁ V₂ V₃ B₁ B₂
    unitIso := ofHCompUnitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
    counitIso := ofHCompCounitIso T₁ T₂ V₁ V₂ V₃ B₁ B₂ h
    functorEquiv_inverse_obj_unitIso_comp x := by
      ext <;> dsimp [ofHCompUnitIso, ofHCompCounitIso]
      · apply IsCatPullbackSquare.hom_ext T₂ V₂ V₃ B₂
        · simp [← Functor.comp_map]
        · simp [← Functor.map_comp_assoc]
      · simp }

end

end

end hComp

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

end IsCatPullbackSquare

end CategoryTheory.Limits
