import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Indization.IndObject
import Mathlib.CategoryTheory.Limits.Opposites

section

variable (G M : Type*) [Group G] [Monoid M] (f : G ≃* M) (g : M ≃* G)

lemma isUnit_of_equiv (x : M) : IsUnit x := by
  rw [isUnit_iff_exists]
  refine ⟨f (f.symm x)⁻¹, ?_, ?_⟩
  all_goals
  apply EquivLike.injective f.symm
  simp

end

open CategoryTheory Limits Opposite

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{u₂} C] {I : Type v₁} [Category.{v₂} I] (F : I ⥤ C)
variable [HasColimit F] [HasLimit (F.op ⋙ coyoneda)]

instance : HasLimit F.op := hasLimit_op_of_hasColimit F

noncomputable def limitOfOpIsoOpColimit : limit F.op ≅ op <| colimit F :=
  let c : Cocone F := colimit.cocone F
  let hc : IsColimit c := colimit.isColimit F
  limit.isoLimitCone ⟨c.op, IsColimit.op hc⟩

@[simp]
theorem limitOfOpIsoOpColimit_inv_comp_π (i : I) :
    (limitOfOpIsoOpColimit F).inv ≫ limit.π F.op ⟨i⟩ = (colimit.ι F i).op := by
  simp [limitOfOpIsoOpColimit]

noncomputable def homCocont : coyoneda.obj (limit F.op) ≅ limit (F.op ⋙ coyoneda) :=
  preservesLimitIso coyoneda F.op

noncomputable def homCocont' : coyoneda.obj (op <| colimit F) ≅ limit (F.op ⋙ coyoneda) :=
  coyoneda.mapIso (limitOfOpIsoOpColimit F).symm ≪≫ homCocont F

noncomputable def homCocont'App [HasLimitsOfShape Iᵒᵖ (Type u₂)] (A : C) :
    (colimit F ⟶ A) ≅ limit (F.op ⋙ yoneda.obj A) :=
  ((homCocont' F).app A).trans <| limitObjIsoLimitCompEvaluation _ _

@[simp]
theorem homCocont'_comp_π (i : I) :
    (homCocont' F).hom ≫ (limit.π (F.op.comp coyoneda) ⟨i⟩)
      = (coyoneda.map (colimit.ι F i).op) := by
  simp [homCocont', homCocont]
  rw [← Functor.map_comp]
  simp

@[simp]
theorem homCocont'App_comp_π [HasLimitsOfShape Iᵒᵖ (Type u₂)] (A : C) (i : I) :
    (homCocont'App F A).hom ≫ limit.π (F.op ⋙ yoneda.obj A) ⟨i⟩
      = (coyoneda.map (colimit.ι F i).op).app A := by
  simp [homCocont'App]
  erw [limitObjIsoLimitCompEvaluation_hom_π]
  change ((homCocont' F).hom ≫ _).app A = _
  rw [homCocont'_comp_π]

end

variable {C : Type u₁} [Category.{u₂} C] {J : Type v₁} [Category.{v₂} J] (D : Jᵒᵖ ⥤ C)
variable (F : C ⥤ Type u₂)

variable [HasColimit (D.rightOp ⋙ coyoneda)] [HasLimitsOfShape Jᵒᵖ (Type (max u₁ u₂))]

noncomputable def procoyonedaIso :
    (colimit (D.rightOp ⋙ coyoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  (homCocont'App _ F).trans
    (HasLimit.isoOfNatIso (isoWhiskerLeft (D ⋙ Prod.sectl C F) (coyonedaLemma C)))

attribute [-simp] types_comp_apply

@[simp]
theorem procoyonedaIso_π (f : colimit (D.rightOp ⋙ coyoneda) ⟶ F) (i : J) :
    (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) (op i)) ((procoyonedaIso D F).hom f)
      = ⟨(f.app (D.obj (op i)) ((colimit.ι (D.rightOp ⋙ coyoneda) i).app (D.obj (op i)) (𝟙 (D.obj (op i)))))⟩ := by
  change ((procoyonedaIso D F).hom ≫ (limit.π (D ⋙ F ⋙ uliftFunctor.{u₁}) (op i))) f = _
  simp [procoyonedaIso]
  rw [← Category.assoc]
  rw [homCocont'App_comp_π]
  simp [coyonedaLemma, types_comp_apply]
  erw [coyonedaEquiv_comp]
  rw [coyonedaEquiv_apply]
  rfl
