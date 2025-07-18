/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# There are only `v`-many natural transformations between Ind-objects

We provide the instance `LocallySmall.{v} (FullSubcategory (IsIndObject (C := C)))`, which will
serve as the basis for our definition of the category of Ind-objects.

## Future work

The equivalence established here serves as the basis for a well-known calculation of hom-sets of
ind-objects as a limit of a colimit.
-/

open CategoryTheory Limits Opposite

universe v v₁ v₂ u u₁ u₂

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I (Type v)]
  [HasLimitsOfShape Iᵒᵖ (Type v)]
variable {J : Type u₂} [Category.{v₂} J]
  [HasLimitsOfShape Iᵒᵖ (Type (max u v))]
variable (F : I ⥤ C) (G : Cᵒᵖ ⥤ Type v)

/-- Variant of `colimitYonedaHomIsoLimitOp`: natural transformations with domain
`colimit (F ⋙ yoneda)` are equivalent to a limit in a lower universe. -/
noncomputable def colimitYonedaHomEquiv : (colimit (F ⋙ yoneda) ⟶ G) ≃ limit (F.op ⋙ G) :=
  Equiv.symm <| Equiv.ulift.symm.trans <| Equiv.symm <| Iso.toEquiv <| calc
  (colimit (F ⋙ yoneda) ⟶ G) ≅ limit (F.op ⋙ G ⋙ uliftFunctor.{u}) :=
        colimitYonedaHomIsoLimitOp _ _
  _ ≅ limit ((F.op ⋙ G) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u}.obj (limit (F.op ⋙ G)) :=
        (preservesLimitIso _ _).symm

@[simp]
theorem colimitYonedaHomEquiv_π_apply (η : colimit (F ⋙ yoneda) ⟶ G) (i : Iᵒᵖ) :
    limit.π (F.op ⋙ G) i (colimitYonedaHomEquiv F G η) =
      η.app (op (F.obj i.unop)) ((colimit.ι (F ⋙ yoneda) i.unop).app _ (𝟙 _)) := by
  simp only [Functor.comp_obj, Functor.op_obj, colimitYonedaHomEquiv, uliftFunctor_obj,
    Iso.trans_def, Iso.trans_assoc, Iso.toEquiv_comp, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.trans_apply, Iso.toEquiv_fun, Iso.symm_hom, Equiv.ulift_apply]
  have (a : _) := congrArg ULift.down
    (congrFun (preservesLimitIso_inv_π uliftFunctor.{u, v} (F.op ⋙ G) i) a)
  dsimp at this
  rw [this, ← types_comp_apply (HasLimit.isoOfNatIso _).hom (limit.π _ _),
    HasLimit.isoOfNatIso_hom_π]
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
    exact small_map e₃

end CategoryTheory
