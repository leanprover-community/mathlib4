/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.FreeMonoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels

/-!
# Tensor product of quasicoherent sheaves

-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

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

end SheafOfModules
