/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Fintype.Card
import Mathlib.CategoryTheory.FinCategory.Basic

#align_import category_theory.fin_category from "leanprover-community/mathlib"@"2efd2423f8d25fa57cf7a179f5d8652ab4d0df44"

/-!
# Finite categories are equivalent to category in `Type 0`.
-/


universe w v u

open scoped Classical

noncomputable section

namespace CategoryTheory

namespace FinCategory

variable (α : Type*) [Fintype α] [SmallCategory α] [FinCategory α]

/-- A FinCategory `α` is equivalent to a category with objects in `Type`. -/
--@[nolint unused_arguments]
abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm
#align category_theory.fin_category.obj_as_type CategoryTheory.FinCategory.ObjAsType

instance {i j : ObjAsType α} : Fintype (i ⟶ j) :=
  FinCategory.fintypeHom ((Fintype.equivFin α).symm i) _

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence
#align category_theory.fin_category.obj_as_type_equiv CategoryTheory.FinCategory.objAsTypeEquiv

/-- A FinCategory `α` is equivalent to a fin_category with in `Type`. -/
--@[nolint unused_arguments]
abbrev AsType : Type :=
  Fin (Fintype.card α)
#align category_theory.fin_category.as_type CategoryTheory.FinCategory.AsType

@[simps (config := .lemmasOnly) id comp]
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  Hom i j := Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id i := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)
#align category_theory.fin_category.category_as_type CategoryTheory.FinCategory.categoryAsType

attribute [local simp] categoryAsType_id categoryAsType_comp

/-- The "identity" functor from `AsType α` to `ObjAsType α`. -/
@[simps]
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map {X Y} := (Fintype.equivFin _).symm
#align category_theory.fin_category.as_type_to_obj_as_type CategoryTheory.FinCategory.asTypeToObjAsType

/-- The "identity" functor from `ObjAsType α` to `AsType α`. -/
@[simps]
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map {X Y} := Fintype.equivFin _
#align category_theory.fin_category.obj_as_type_to_as_type CategoryTheory.FinCategory.objAsTypeToAsType

/-- The constructed category (`AsType α`) is equivalent to `ObjAsType α`. -/
noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α :=
  Equivalence.mk (asTypeToObjAsType α) (objAsTypeToAsType α)
    (NatIso.ofComponents Iso.refl)
    (NatIso.ofComponents Iso.refl)
#align category_theory.fin_category.as_type_equiv_obj_as_type CategoryTheory.FinCategory.asTypeEquivObjAsType

noncomputable instance asTypeFinCategory : FinCategory (AsType α) where
  fintypeHom := fun _ _ => show Fintype (Fin _) from inferInstance
#align category_theory.fin_category.as_type_fin_category CategoryTheory.FinCategory.asTypeFinCategory

/-- The constructed category (`ObjAsType α`) is indeed equivalent to `α`. -/
noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)
#align category_theory.fin_category.equiv_as_type CategoryTheory.FinCategory.equivAsType

end FinCategory

end CategoryTheory
