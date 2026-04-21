/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Finite categories are equivalent to categories in `Type 0`.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true


universe w v u

noncomputable section

namespace CategoryTheory

namespace FinCategory

variable (α : Type*) [Fintype α] [SmallCategory α] [FinCategory α]

/-- A FinCategory `α` is equivalent to a category with objects in `Type`. -/
--@[nolint unused_arguments]
abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm

instance {i j : ObjAsType α} : Fintype (i ⟶ j) :=
  Fintype.ofEquiv _ InducedCategory.homEquiv.symm

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

/-- A FinCategory `α` is equivalent to a FinCategory in `Type`. -/
--@[nolint unused_arguments]
abbrev AsType : Type :=
  Fin (Fintype.card α)

@[simps -isSimp id comp]
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  Hom i j := Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id _ := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

attribute [local simp] categoryAsType_id categoryAsType_comp

/-- The "identity" functor from `AsType α` to `ObjAsType α`. -/
@[simps]
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map {_ _} := (Fintype.equivFin _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The "identity" functor from `ObjAsType α` to `AsType α`. -/
@[simps]
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map {_ _} := Fintype.equivFin _

set_option backward.isDefEq.respectTransparency false in
/-- The constructed category (`AsType α`) is equivalent to `ObjAsType α`. -/
noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α where
  functor := asTypeToObjAsType α
  inverse := objAsTypeToAsType α
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl

noncomputable instance asTypeFinCategory : FinCategory (AsType α) where
  fintypeHom := fun _ _ => show Fintype (Fin _) from inferInstance

/-- The constructed category (`ObjAsType α`) is indeed equivalent to `α`. -/
noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

end FinCategory

end CategoryTheory
