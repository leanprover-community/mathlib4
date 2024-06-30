/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Yoneda

/-!

# Ind- and pro- (co)yoneda lemmas

We define limit versions of the yoneda and coyoneda lemmas.

## Main results

Notation: categories `C`, `I` and functors `D : Iᵒᵖ ⥤ C`, `F : C ⥤ Type`.

- `colimitCoyonedaHomIsoLimit`: pro-coyoneda lemma: homorphisms from colimit of coyoneda of
  diagram `D` to `F` is limit of `F` evaluated at `D`.
- `colimitCoyonedaHomIsoLimit'`: a variant of `colimitCoyonedaHomIsoLimit` for a covariant
  diagram.

## TODO:

- define the ind-yoneda versions (for contravariant `F`)

-/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Limits

open Opposite

variable {C : Type u₁} [Category.{u₂} C] {I : Type v₁} [Category.{v₂} I]

section LimitOpColimit

instance (F : I ⥤ C) [HasColimit F] : HasLimit F.op := hasLimit_op_of_hasColimit F

/-- The limit of `F.op` is the opposite of `colimit F`. -/
noncomputable def limitOpIsoOpColimit (F : I ⥤ C) [HasColimit F] :
    limit F.op ≅ op <| colimit F :=
  limit.isoLimitCone ⟨(colimit.cocone F).op, (colimit.isColimit F).op⟩

@[reassoc (attr := simp)]
lemma limitOpIsoOpColimit_inv_comp_π (F : I ⥤ C) [HasColimit F] (i : I) :
    (limitOpIsoOpColimit F).inv ≫ limit.π F.op ⟨i⟩ = (colimit.ι F i).op := by
  simp [limitOpIsoOpColimit]

@[reassoc (attr := simp)]
lemma limitOpIsoOpColimit_hom_comp_ι (F : I ⥤ C) [HasColimit F] (i : I) :
    (limitOpIsoOpColimit F).hom ≫ (colimit.ι F i).op = limit.π F.op ⟨i⟩ := by
  rw [← limitOpIsoOpColimit_inv_comp_π, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

instance (F : Iᵒᵖ ⥤ C) [HasColimit F] : HasLimit F.rightOp where
  exists_limit := ⟨⟨coneRightOpOfCocone (colimit.cocone F),
    isLimitConeRightOpOfCocone F (colimit.isColimit F)⟩⟩

/-- `limitOpIsoOpColimit` for contravariant functor. -/
noncomputable def limitRightOpIsoOpColimit (F : Iᵒᵖ ⥤ C) [HasColimit F] :
    limit F.rightOp ≅ op <| colimit F :=
  limit.isoLimitCone ⟨coneRightOpOfCocone (colimit.cocone F),
    isLimitConeRightOpOfCocone F (colimit.isColimit F)⟩

@[reassoc (attr := simp)]
lemma limitRightOpIsoOpColimit_inv_comp_π (F : Iᵒᵖ ⥤ C) [HasColimit F] (i : I) :
    (limitRightOpIsoOpColimit F).inv ≫ limit.π F.rightOp i = (colimit.ι F ⟨i⟩).op := by
  simp [limitRightOpIsoOpColimit]

@[reassoc (attr := simp)]
lemma limitRightOpIsoOpColimit_hom_comp_ι (F : Iᵒᵖ ⥤ C) [HasColimit F] (i : I) :
    (limitRightOpIsoOpColimit F).hom ≫ (colimit.ι F ⟨i⟩).op = limit.π F.rightOp i := by
  rw [← limitRightOpIsoOpColimit_inv_comp_π, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end LimitOpColimit

section HomCocontinuousCovariant

variable (F : I ⥤ C) [HasColimit F]

/-- Hom is functorially cocontinuous: coyoneda of a colimit is the limit
over coyoneda of the diagram. -/
noncomputable def coyonedaOpColimitIsoLimitCoyoneda :
    coyoneda.obj (op <| colimit F) ≅ limit (F.op ⋙ coyoneda) :=
  coyoneda.mapIso (limitOpIsoOpColimit F).symm ≪≫ (preservesLimitIso coyoneda F.op)

@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda_hom_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda F).hom ≫ limit.π (F.op.comp coyoneda) ⟨i⟩
      = coyoneda.map (colimit.ι F i).op := by
  simp only [coyonedaOpColimitIsoLimitCoyoneda, Functor.mapIso_symm,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc, preservesLimitsIso_hom_π,
    ← Functor.map_comp, limitOpIsoOpColimit_inv_comp_π]

@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda_inv_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda F).inv ≫ coyoneda.map (colimit.ι F i).op
      = limit.π (F.op.comp coyoneda) ⟨i⟩ := by
  rw [← coyonedaOpColimitIsoLimitCoyoneda_hom_comp_π, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Hom is cocontinuous: homomorphisms from a colimit is the limit over yoneda of the diagram. -/
noncomputable def colimitHomIsoLimitYoneda
    [HasLimitsOfShape Iᵒᵖ (Type u₂)] (A : C) :
    (colimit F ⟶ A) ≅ limit (F.op ⋙ yoneda.obj A) :=
  (coyonedaOpColimitIsoLimitCoyoneda F).app A ≪≫ limitObjIsoLimitCompEvaluation _ _

@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda_hom_comp_π [HasLimitsOfShape Iᵒᵖ (Type u₂)] (A : C) (i : I) :
    (colimitHomIsoLimitYoneda F A).hom ≫ limit.π (F.op ⋙ yoneda.obj A) ⟨i⟩
      = (coyoneda.map (colimit.ι F i).op).app A := by
  simp only [colimitHomIsoLimitYoneda, Iso.trans_hom, Iso.app_hom, Category.assoc]
  erw [limitObjIsoLimitCompEvaluation_hom_π]
  change ((coyonedaOpColimitIsoLimitCoyoneda F).hom ≫ _).app A = _
  rw [coyonedaOpColimitIsoLimitCoyoneda_hom_comp_π]

@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda_inv_comp_π [HasLimitsOfShape Iᵒᵖ (Type u₂)] (A : C) (i : I) :
    (colimitHomIsoLimitYoneda F A).inv ≫ (coyoneda.map (colimit.ι F i).op).app A
      = limit.π (F.op ⋙ yoneda.obj A) ⟨i⟩ := by
  rw [← colimitHomIsoLimitYoneda_hom_comp_π, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end HomCocontinuousCovariant

section HomCocontinuousContravariant

variable (F : Iᵒᵖ ⥤ C) [HasColimit F]

/-- Variant of `coyonedaOoColimitIsoLimitCoyoneda` for contravariant `F`. -/
noncomputable def coyonedaOpColimitIsoLimitCoyoneda' :
    coyoneda.obj (op <| colimit F) ≅ limit (F.rightOp ⋙ coyoneda) :=
  coyoneda.mapIso (limitRightOpIsoOpColimit F).symm ≪≫ preservesLimitIso coyoneda F.rightOp

@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda'_hom_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda' F).hom ≫ limit.π (F.rightOp ⋙ coyoneda) i
      = coyoneda.map (colimit.ι F ⟨i⟩).op := by
  simp only [coyonedaOpColimitIsoLimitCoyoneda', Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc, preservesLimitsIso_hom_π, ← Functor.map_comp,
    limitRightOpIsoOpColimit_inv_comp_π]

@[reassoc (attr := simp)]
lemma coyonedaOpColimitIsoLimitCoyoneda'_inv_comp_π (i : I) :
    (coyonedaOpColimitIsoLimitCoyoneda' F).inv ≫ coyoneda.map (colimit.ι F ⟨i⟩).op
      = limit.π (F.rightOp ⋙ coyoneda) i := by
  rw [← coyonedaOpColimitIsoLimitCoyoneda'_hom_comp_π, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Variant of `colimitHomIsoLimitYoneda` for contravariant `F`. -/
noncomputable def colimitHomIsoLimitYoneda' [HasLimitsOfShape I (Type u₂)] (A : C) :
    (colimit F ⟶ A) ≅ limit (F.rightOp ⋙ yoneda.obj A) :=
  (coyonedaOpColimitIsoLimitCoyoneda' F).app A ≪≫ limitObjIsoLimitCompEvaluation _ _

@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda'_hom_comp_π [HasLimitsOfShape I (Type u₂)] (A : C) (i : I) :
    (colimitHomIsoLimitYoneda' F A).hom ≫ limit.π (F.rightOp ⋙ yoneda.obj A) i
      = (coyoneda.map (colimit.ι F ⟨i⟩).op).app A := by
  simp only [yoneda_obj_obj, colimitHomIsoLimitYoneda', Iso.trans_hom,
    Iso.app_hom, Category.assoc]
  erw [limitObjIsoLimitCompEvaluation_hom_π]
  change ((coyonedaOpColimitIsoLimitCoyoneda' F).hom ≫ _).app A = _
  rw [coyonedaOpColimitIsoLimitCoyoneda'_hom_comp_π]

@[reassoc (attr := simp)]
lemma colimitHomIsoLimitYoneda'_inv_comp_π [HasLimitsOfShape I (Type u₂)] (A : C) (i : I) :
    (colimitHomIsoLimitYoneda' F A).inv ≫ (coyoneda.map (colimit.ι F ⟨i⟩).op).app A
      = limit.π (F.rightOp ⋙ yoneda.obj A) i := by
  rw [← colimitHomIsoLimitYoneda'_hom_comp_π, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end HomCocontinuousContravariant

section ProCoyonedaContravariant

variable (D : Iᵒᵖ ⥤ C) (F : C ⥤ Type u₂)
variable [HasColimit (D.rightOp ⋙ coyoneda)] [HasLimitsOfShape Iᵒᵖ (Type (max u₁ u₂))]

/-- Pro-Coyoneda lemma: homorphisms from colimit of coyoneda of diagram `D` to `F` is limit
of `F` evaluated at `D`. -/
noncomputable def colimitCoyonedaHomIsoLimit :
    (colimit (D.rightOp ⋙ coyoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  colimitHomIsoLimitYoneda _ F ≪≫
    HasLimit.isoOfNatIso (isoWhiskerLeft (D ⋙ Prod.sectl C F) (coyonedaLemma C))

@[simp]
lemma colimitCoyonedaHomIsoLimit_π_apply (f : colimit (D.rightOp ⋙ coyoneda) ⟶ F) (i : I) :
    limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) (op i) ((colimitCoyonedaHomIsoLimit D F).hom f)
      = ⟨f.app (D.obj (op i)) ((colimit.ι (D.rightOp ⋙ coyoneda) i).app (D.obj (op i))
          (𝟙 (D.obj (op i))))⟩ := by
  change ((colimitCoyonedaHomIsoLimit D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) (op i))) f = _
  simp only [colimitCoyonedaHomIsoLimit, Iso.trans_hom, Category.assoc,
    HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, colimitHomIsoLimitYoneda_hom_comp_π]
  dsimp [coyonedaLemma, types_comp_apply]
  erw [coyonedaEquiv_comp, coyonedaEquiv_apply]
  rfl

end ProCoyonedaContravariant

section ProCoyonedaCovariant

variable (D : I ⥤ C) (F : C ⥤ Type u₂)
variable [HasColimit (D.op ⋙ coyoneda)] [HasLimitsOfShape I (Type (max u₁ u₂))]

/-- A variant of `colimitCoyonedaHomIsoLimit` for a contravariant diagram. -/
noncomputable def colimitCoyonedaHomIsoLimit' :
    (colimit (D.op ⋙ coyoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  colimitHomIsoLimitYoneda' _ F ≪≫
    HasLimit.isoOfNatIso (isoWhiskerLeft (D ⋙ Prod.sectl C F) (coyonedaLemma C))

@[simp]
lemma colimitCoyonedaHomIsoLimit'_π_apply (f : colimit (D.op ⋙ coyoneda) ⟶ F) (i : I) :
    limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i ((colimitCoyonedaHomIsoLimit' D F).hom f)
      = ⟨f.app (D.obj i) ((colimit.ι (D.op ⋙ coyoneda) ⟨i⟩).app (D.obj i) (𝟙 (D.obj i)))⟩ := by
  change ((colimitCoyonedaHomIsoLimit' D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) i)) f = _
  simp only [colimitCoyonedaHomIsoLimit', Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, colimitHomIsoLimitYoneda'_hom_comp_π]
  dsimp [coyonedaLemma]
  erw [coyonedaEquiv_comp, coyonedaEquiv_apply]
  rfl

end ProCoyonedaCovariant

end Limits

end CategoryTheory
