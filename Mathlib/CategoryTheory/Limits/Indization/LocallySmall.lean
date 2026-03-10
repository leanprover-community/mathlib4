/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# There are only `v`-many natural transformations between Ind-objects

We provide the instance `LocallySmall.{v} (FullSubcategory (IsIndObject (C := C)))`, which will
serve as the basis for our definition of the category of Ind-objects.

## Future work

The equivalence established here serves as the basis for a well-known calculation of hom-sets of
ind-objects as a limit of a colimit.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u u₁ u₂

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I TypeCat.{v}]
  [HasLimitsOfShape Iᵒᵖ TypeCat.{v}]
variable {J : Type u₂} [Category.{v₂} J]
  [HasLimitsOfShape Iᵒᵖ TypeCat.{max u v}]
variable (F : I ⥤ C) (G : Cᵒᵖ ⥤ TypeCat.{v})

/-- Variant of `colimitYonedaHomIsoLimitOp`: natural transformations with domain
`colimit (F ⋙ yoneda)` are equivalent to a limit in a lower universe. -/
noncomputable def colimitYonedaHomEquiv :
    (colimit (F ⋙ yoneda) ⟶ G) ≃ (limit (F.op ⋙ G) : TypeCat) :=
  Equiv.symm <| Equiv.ulift.symm.trans <| Equiv.symm <| Iso.toEquiv <| calc
  TypeCat.of (colimit (F ⋙ yoneda) ⟶ G) ≅ limit (F.op ⋙ G ⋙ uliftFunctor.{u}) :=
        colimitYonedaHomIsoLimitOp _ _
  _ ≅ limit ((F.op ⋙ G) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u}.obj (limit (F.op ⋙ G)) :=
        (preservesLimitIso _ _).symm

attribute [elementwise] HasLimit.isoOfNatIso_hom_π

@[simp]
theorem colimitYonedaHomEquiv_π_apply (η : colimit (F ⋙ yoneda) ⟶ G) (i : Iᵒᵖ) :
    limit.π (F.op ⋙ G) i (colimitYonedaHomEquiv F G η) =
      η.app (op (F.obj i.unop)) ((colimit.ι (F ⋙ yoneda) i.unop).app _ (𝟙 _)) := by
  simp only [Functor.comp_obj, Functor.op_obj, colimitYonedaHomEquiv, Iso.toEquiv, uliftFunctor_obj,
    Iso.trans_def, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_mk, comp_apply,
    Equiv.ulift_apply, yoneda_obj_obj]
  have (a : (limit ((F.op ⋙ G) ⋙ uliftFunctor.{u, v}) : TypeCat)) := congrArg ULift.down
    (ConcreteCategory.congr_hom (preservesLimitIso_inv_π uliftFunctor.{u, v} (F.op ⋙ G) i) a)
  refine Eq.trans (by convert this _) ?_
  erw [HasLimit.isoOfNatIso_hom_π_apply]
  dsimp
  erw [colimitYonedaHomIsoLimitOp_π_apply]
  simp

instance : Small.{v} (colimit (F ⋙ yoneda) ⟶ G) where
  equiv_small := ⟨_, ⟨colimitYonedaHomEquiv F G⟩⟩

end

instance : LocallySmall.{v} (ObjectProperty.FullSubcategory (IsIndObject (C := C))) where
  hom_small X Y := by
    obtain ⟨⟨P⟩⟩ := X.2
    obtain ⟨⟨Q⟩⟩ := Y.2
    let e₁ := IsColimit.coconePointUniqueUpToIso (P.isColimit) (colimit.isColimit _)
    let e₂ := IsColimit.coconePointUniqueUpToIso (Q.isColimit) (colimit.isColimit _)
    let e₃ := Iso.homCongr e₁ e₂
    dsimp only [colimit.cocone_x] at e₃
    exact small_map (InducedCategory.homEquiv.trans e₃)

end CategoryTheory
