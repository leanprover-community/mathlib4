/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.FreeMonoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Tensor product of quasicoherent sheaves

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat)]
  [(W R).IsMonoidal]

variable {M₁ M₂ : SheafOfModules.{w} ((sheafCompose J (forget₂ _ RingCat)).obj R)}
  (P₁ : M₁.Presentation) (P₂ : M₂.Presentation)

namespace Presentation

/-- Auxiliary definition for `Presentation.tensor`. -/
noncomputable def tensorRelationsIso :
    free (R := (sheafCompose J (forget₂ _ RingCat)).obj R) P₁.relations.I ⊗
      free P₂.generators.I ⨿ free P₁.generators.I ⊗ free P₂.relations.I ≅
    free (P₁.relations.I × P₂.generators.I ⊕ P₁.generators.I × P₂.relations.I) :=
  (coprod.mapIso (freeProdIso (R := R) P₁.relations.I P₂.generators.I).symm
    (freeProdIso P₁.generators.I P₂.relations.I).symm ≪≫ freeSumIso _ _)

/-- Auxiliary definition for `Presentation.tensor`. -/
noncomputable def tensorMap :
    free (R := (sheafCompose J (forget₂ _ RingCat)).obj R)
      (P₁.relations.I × P₂.generators.I ⊕ P₁.generators.I × P₂.relations.I) ⟶
    free (P₁.generators.I × P₂.generators.I) :=
  (tensorRelationsIso P₁ P₂).inv ≫
      coprod.desc (((freeHomEquiv _).symm P₁.relations.s ≫ kernel.ι _) ▷ _)
        (_ ◁ ((freeHomEquiv _).symm P₂.relations.s ≫ kernel.ι _)) ≫ (freeProdIso _ _).inv

/-- Auxiliary definition for `Presentation.tensor`. -/
noncomputable abbrev cokernelCoforkTensor :
    CokernelCofork (tensorMap P₁ P₂) :=
  CokernelCofork.ofπ ((freeProdIso _ _).hom ≫ (P₁.generators.π ⊗ₘ P₂.generators.π)) (by
    dsimp [tensorMap]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      Preadditive.IsIso.comp_left_eq_zero]
    ext : 1
    · rw [coprod.inl_desc_assoc, tensorHom_def, ← MonoidalCategory.comp_whiskerRight_assoc]
      simp
    · rw [coprod.inr_desc_assoc, tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc]
      simp)

/-- Auxiliary definition for `Presentation.tensor`. -/
noncomputable def isColimitCokernelCoforkTensor :
    IsColimit (cokernelCoforkTensor P₁ P₂) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeInvEquiv
      (parallelPair.ext (tensorRelationsIso P₁ P₂) (freeProdIso _ _).symm
        (by simp [tensorMap])) _).2
      (CokernelCofork.isColimitTensor P₁.isColimit P₂.isColimit))
      (Cofork.ext (Iso.refl _) (by simp [Cofork.π]))

/-- If `P₁` is a presentation of a sheaf of modules `M₁` and
`P₂` is a presentation of a sheaf of modules `M₂`, then this is a
presentation of `P₁ ⊗ P₂`. -/
noncomputable def tensor : (M₁ ⊗ M₂).Presentation :=
  presentationOfIsCokernelFree _ _ (cokernelCoforkTensor P₁ P₂).condition
    (isColimitCokernelCoforkTensor P₁ P₂)

end Presentation

variable [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat)]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
  [∀ (X : C), (J.over X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat)]
  [(W R).IsMonoidal] [∀ (X : C), (W ((R.over X))).IsMonoidal]

namespace QuasicoherentData

variable (R) in
noncomputable abbrev overFunctorOfCommRing (X : C) :
    SheafOfModules.{w} (((sheafCompose J (forget₂ _ RingCat)).obj R)) ⥤
      SheafOfModules.{w} (((sheafCompose (J.over X) (forget₂ _ RingCat)).obj (R.over X))) :=
  overFunctor _ X

variable (R) in
noncomputable abbrev overPullbackOfCommRing {X Y : C} (f : X ⟶ Y) :
    SheafOfModules.{w} (((sheafCompose (J.over Y) (forget₂ _ RingCat)).obj (R.over Y))) ⥤
      SheafOfModules.{w} (((sheafCompose (J.over X) (forget₂ _ RingCat)).obj (R.over X))) :=
  pushforward (F := Over.map f) (𝟙 _)

instance {X Y : C} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{w, w} (overPullbackOfCommRing R f) := sorry

-- to be moved
instance {X Y : C} (f : X ⟶ Y) :
    (Over.map f ⋙ Over.forget Y).IsContinuous (J.over X) J := by
  rw [Over.mapForget_eq]
  infer_instance

variable (R) in
noncomputable def overFunctorOfCommRingCompOverPullbackOfCommRing {X Y : C} (f : X ⟶ Y) :
    overFunctorOfCommRing R Y ⋙ overPullbackOfCommRing R f ≅ overFunctorOfCommRing R X :=
  pushforwardComp _ _

instance (X : C) : (overFunctorOfCommRing.{w} R X).Monoidal := sorry

instance {X Y : C} (f : X ⟶ Y) : (overPullbackOfCommRing.{w} R f).Monoidal := sorry

noncomputable def tensor (d₁ : M₁.QuasicoherentData) (d₂ : M₂.QuasicoherentData) :
    (M₁ ⊗ M₂).QuasicoherentData where
  I := _
  X := _
  coversTop := d₁.coversTop.prod d₂.coversTop
  presentation := fun ⟨A, i, i', p, p'⟩ ↦
    Presentation.ofIsIso
      (Functor.Monoidal.μIso (overFunctorOfCommRing.{w} R A) M₁ M₂).hom (by
        apply Presentation.tensor
        · exact Presentation.ofIsIso
            ((overFunctorOfCommRingCompOverPullbackOfCommRing.{w} R p).hom.app M₁)
              (Presentation.map (by exact (d₁.presentation i))
                  (overPullbackOfCommRing R p)
                    (Functor.Monoidal.εIso _).symm)
        · exact Presentation.ofIsIso
            ((overFunctorOfCommRingCompOverPullbackOfCommRing.{w} R p').hom.app M₂)
              (Presentation.map (by exact (d₂.presentation i'))
                  (overPullbackOfCommRing R p')
                    (Functor.Monoidal.εIso _).symm))

end QuasicoherentData

instance [M₁.IsQuasicoherent] [M₂.IsQuasicoherent] : (M₁ ⊗ M₂).IsQuasicoherent :=
  QuasicoherentData.isQuasicoherent
    (M₁.quasicoherentData.tensor M₂.quasicoherentData)

instance isMonoidal_isQuasicoherent :
    (isQuasicoherent ((sheafCompose J (forget₂ _ RingCat)).obj R)).IsMonoidal where
  prop_unit := sorry
  prop_tensor M₁ M₂ _ _ := by infer_instance

end

end SheafOfModules
