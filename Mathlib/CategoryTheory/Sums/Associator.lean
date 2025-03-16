/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
import Mathlib.CategoryTheory.Sums.Basic

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open Sum

namespace CategoryTheory.sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (E : Type u₃) [Category.{v₃} E]

/-- The associator functor `(C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E)` for sums of categories.
-/
def associator : (C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E) :=
  (inl_ _ _ |>.sum' <| inl_ _ _ ⋙ inr_ _ _).sum' <| inr_ _ _ ⋙ inr_ _ _

@[simp]
theorem associator_obj_inl_inl (X) : (associator C D E).obj (inl (inl X)) = inl X :=
  rfl

@[simp]
theorem associator_obj_inl_inr (X) : (associator C D E).obj (inl (inr X)) = inr (inl X) :=
  rfl

@[simp]
theorem associator_obj_inr (X) : (associator C D E).obj (inr X) = inr (inr X) :=
  rfl

@[simp]
theorem associator_map_inl_inl {X Y : C} (f : inl (inl X) ⟶ inl (inl Y)) :
    (associator C D E).map f = (inl_ _ _).map f.down.down :=
  rfl

@[simp]
theorem associator_map_inl_inr {X Y : D} (f : inl (inr X) ⟶ inl (inr Y)) :
    (associator C D E).map f = (inr_ _ _).map ((inl_ _ _).map f.down.down) :=
  rfl

@[simp]
theorem associator_map_inr {X Y : E} (f : inr X ⟶ inr Y) :
    (associator C D E).map f = (inr_ _ _).map ((inr_ _ _).map f.down) :=
  rfl

@[simps!]
def inlCompAssociator : (inl_ _ _) ⋙ associator C D E ≅ inl_ _ _ |>.sum' <| inl_ _ _ ⋙ inr_ _ _ :=
  (Functor.inlCompSum' _ _)

@[simps!]
def inrCompAssociator : (inr_ _ _) ⋙ associator C D E ≅ inr_ _ _ ⋙ inr_ _ _ :=
  (Functor.inrCompSum' _ _)

@[simps!]
def inlCompInlCompAssociator : (inl_ _ _) ⋙ (inl_ _ _) ⋙ associator C D E ≅ inl_ _ _ :=
  isoWhiskerLeft (inl_ _ _) (inlCompAssociator C D E) ≪≫ (Functor.inlCompSum' _ _)

@[simps!]
def inrCompInlCompAssociator : (inr_ _ _) ⋙ (inl_ _ _) ⋙ associator C D E ≅ inl_ _ _ ⋙ inr_ _ _ :=
  isoWhiskerLeft (inr_ _ _) (inlCompAssociator C D E) ≪≫ (Functor.inrCompSum' _ _)

/-- The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
def inverseAssociator : C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E :=
  inl_ _ _ ⋙ inl_ _ _ |>.sum' <| (inr_ _ _ ⋙ inl_ _ _).sum' <| inr_ _ _

@[simp]
theorem inverseAssociator_obj_inl (X) : (inverseAssociator C D E).obj (inl X) = inl (inl X) :=
  rfl

@[simp]
theorem inverseAssociator_obj_inr_inl (X) :
    (inverseAssociator C D E).obj (inr (inl X)) = inl (inr X) :=
  rfl

@[simp]
theorem inverseAssociator_obj_inr_inr (X) : (inverseAssociator C D E).obj (inr (inr X)) = inr X :=
  rfl

@[simp]
theorem inverseAssociator_map_inl {X Y : C} (f : inl X ⟶ inl Y) :
    (inverseAssociator C D E).map f = (inl_ _ _).map ((inl_ _ _).map f.down) :=
  rfl

@[simp]
theorem inverseAssociator_map_inr_inl {X Y : D} (f : inr (inl X) ⟶ inr (inl Y)) :
    (inverseAssociator C D E).map f = (inl_ _ _).map ((inr_ _ _).map f.down.down) :=
  rfl

@[simp]
theorem inverseAssociator_map_inr_inr {X Y : E} (f : inr (inr X) ⟶ inr (inr Y)) :
    (inverseAssociator C D E).map f = (inr_ _ _).map f.down.down :=
  rfl

@[simps!]
def inlCompInverseAssociator : (inl_ _ _) ⋙ inverseAssociator C D E ≅ inl_ _ _ ⋙ inl_ _ _ :=
  Functor.inlCompSum' _ _

@[simps!]
def inrCompInverseAssociator :
    (inr_ _ _) ⋙ inverseAssociator C D E ≅ (inr_ _ _ ⋙ inl_ _ _).sum' <| inr_ _ _ :=
  Functor.inrCompSum' _ _

@[simps!]
def inlCompInrCompInverseAssociator :
    (inl_ _ _) ⋙ (inr_ _ _) ⋙ inverseAssociator C D E ≅ inr_ _ _ ⋙ inl_ _ _ :=
  isoWhiskerLeft (inl_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inlCompSum' _ _

@[simps!]
def inrCompInrCompInverseAssociator :
    (inr_ _ _) ⋙ (inr_ _ _) ⋙ inverseAssociator C D E ≅ inr_ _ _ :=
  isoWhiskerLeft (inr_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inrCompSum' _ _

/-- The equivalence of categories expressing associativity of sums of categories.
-/
@[simps functor inverse]
def associativity : (C ⊕ D) ⊕ E ≌ C ⊕ (D ⊕ E) where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := Functor.sumIsoExt
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inlCompInlCompAssociator _ _ _) (inverseAssociator _ _ _) ≪≫
          inlCompInverseAssociator _ _ _).symm ≪≫ Functor.associator _ _ _)
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inrCompInlCompAssociator _ _ _) (inverseAssociator _ _ _) ≪≫
          inlCompInrCompInverseAssociator _ _ _).symm ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _)))
    (Functor.rightUnitor _ ≪≫
      (isoWhiskerRight (inrCompAssociator _ _ _) (inverseAssociator _ _ _) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInrCompInverseAssociator _ _ _).symm ≪≫
      Functor.associator _ _ _)
  counitIso := Functor.sumIsoExt
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (inlCompInverseAssociator _ _ _) (associator _ _ _) ≪≫
      Functor.associator _ _ _ ≪≫ inlCompInlCompAssociator _ _ _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inlCompInrCompInverseAssociator C D E) (associator _ _ _) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInlCompAssociator _ _ _ ≪≫ (Functor.rightUnitor _).symm)
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inrCompInrCompInverseAssociator _ _ _) (associator _ _ _) ≪≫
        inrCompAssociator _ _ _ ≪≫ isoWhiskerLeft _ ((Functor.rightUnitor _).symm)))
  functor_unitIso_comp x := match x with
    | inl (inl c) => by simp [inlCompInlCompAssociator]
    | inl (inr d) => by simp [inrCompInlCompAssociator]
    | inr e => by simp [inrCompAssociator]

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum
