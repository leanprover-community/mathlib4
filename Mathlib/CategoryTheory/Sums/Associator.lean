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
  (inl_ C (D ⊕ E) |>.sum' <| inl_ D E ⋙ inr_ C (D ⊕ E)).sum' <| inr_ D E ⋙ inr_ C (D ⊕ E)

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
theorem associator_map_inl_inl {X Y : C} (f : X ⟶ Y) :
    (associator C D E).map ((inl_ _ _).map ((inl_ _ _).map f)) = (inl_ _ _).map f :=
  rfl

@[simp]
theorem associator_map_inl_inr {X Y : D} (f : X ⟶ Y) :
    (associator C D E).map ((inl_ _ _).map ((inr_ _ _).map f)) =
    (inr_ _ _).map ((inl_ _ _).map f) :=
  rfl

@[simp]
theorem associator_map_inr {X Y : E} (f : X ⟶ Y) :
    (associator C D E).map ((inr_ _ _).map f) = (inr_ _ _).map ((inr_ _ _).map f) :=
  rfl

/-- Characterizing the composition of the associator and the left inclusion. -/
@[simps!]
def inlCompAssociator :
    inl_ (C ⊕ D) E ⋙ associator C D E ≅ inl_ C (D ⊕ E) |>.sum' <| inl_ D E ⋙ inr_ C (D ⊕ E) :=
  (Functor.inlCompSum' _ _)

/-- Characterizing the composition of the associator and the right inclusion. -/
@[simps!]
def inrCompAssociator : inr_ (C ⊕ D) E ⋙ associator C D E ≅ inr_ D E ⋙ inr_ C (D ⊕ E) :=
  (Functor.inrCompSum' _ _)

/-- Further characterizing the composition of the associator and the left inclusion. -/
@[simps!]
def inlCompInlCompAssociator : inl_ C D ⋙ inl_ (C ⊕ D) E ⋙ associator C D E ≅ inl_ C (D ⊕ E) :=
  isoWhiskerLeft (inl_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inlCompSum' _ _

/-- Further characterizing the composition of the associator and the left inclusion. -/
@[simps!]
def inrCompInlCompAssociator :
    inr_ C D ⋙ inl_ (C ⊕ D) E ⋙ associator C D E ≅ inl_ D E ⋙ inr_ C (D ⊕ E) :=
  isoWhiskerLeft (inr_ _ _) (inlCompAssociator C D E) ≪≫ Functor.inrCompSum' _ _

/-- The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
def inverseAssociator : C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E :=
  inl_ C D ⋙ inl_ (C ⊕ D) E |>.sum' <| (inr_ C D ⋙ inl_ (C ⊕ D) E).sum' <| inr_ (C ⊕ D) E

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
theorem inverseAssociator_map_inl {X Y : C} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inl_ _ _).map f) = (inl_ _ _).map ((inl_ _ _).map f) :=
  rfl

@[simp]
theorem inverseAssociator_map_inr_inl {X Y : D} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inr_ _ _).map ((inl_ _ _).map f)) =
    (inl_ _ _).map ((inr_ _ _).map f) :=
  rfl

@[simp]
theorem inverseAssociator_map_inr_inr {X Y : E} (f : X ⟶ Y) :
    (inverseAssociator C D E).map ((inr_ _ _).map ((inr_ _ _).map f)) =
    (inr_ _ _).map f :=
  rfl

/-- Characterizing the composition of the inverse of the associator and the left inclusion. -/
@[simps!]
def inlCompInverseAssociator :
    inl_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ inl_ C D ⋙ inl_ (C ⊕ D) E :=
  Functor.inlCompSum' _ _

/-- Characterizing the composition of the inverse of the associator and the right inclusion. -/
@[simps!]
def inrCompInverseAssociator :
    inr_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ (inr_ C D ⋙ inl_ (C ⊕ D) E).sum' <| inr_ (C ⊕ D) E :=
  Functor.inrCompSum' _ _

/-- Further characterizing the composition of the inverse of the associator and the right
inclusion. -/
@[simps!]
def inlCompInrCompInverseAssociator :
    inl_ D E ⋙ inr_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ inr_ C D ⋙ inl_ (C ⊕ D) E :=
  isoWhiskerLeft (inl_ _ _) (inrCompInverseAssociator C D E) ≪≫ Functor.inlCompSum' _ _

/-- Further characterizing the composition of the inverse of the associator and the right
inclusion. -/
@[simps!]
def inrCompInrCompInverseAssociator :
    inr_ D E ⋙ inr_ C (D ⊕ E) ⋙ inverseAssociator C D E ≅ inr_ (C ⊕ D) E :=
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
        (isoWhiskerRight (inlCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          inlCompInverseAssociator C D E).symm ≪≫ Functor.associator _ _ _)
      ((Functor.associator _ _ _).symm ≪≫ Functor.rightUnitor _ ≪≫
        (isoWhiskerRight (inrCompInlCompAssociator C D E) (inverseAssociator C D E) ≪≫
          inlCompInrCompInverseAssociator C D E).symm ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _)))
    (Functor.rightUnitor _ ≪≫
      (isoWhiskerRight (inrCompAssociator C D E) (inverseAssociator C D E) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInrCompInverseAssociator C D E).symm ≪≫
      Functor.associator _ _ _)
  counitIso := Functor.sumIsoExt
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (inlCompInverseAssociator C D E) (associator C D E) ≪≫
      Functor.associator _ _ _ ≪≫ inlCompInlCompAssociator C D E ≪≫ (Functor.rightUnitor _).symm)
    (Functor.sumIsoExt
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inlCompInrCompInverseAssociator C D E) (associator C D E) ≪≫
        Functor.associator _ _ _ ≪≫ inrCompInlCompAssociator C D E ≪≫ (Functor.rightUnitor _).symm)
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.associator _ _ _ ≪≫
          inrCompInrCompInverseAssociator C D E) (associator C D E) ≪≫
        inrCompAssociator C D E ≪≫ isoWhiskerLeft _ (Functor.rightUnitor _).symm))
  functor_unitIso_comp x := match x with
    | inl (inl c) => by simp [inlCompInlCompAssociator, inlCompInverseAssociator]
    | inl (inr d) => by simp [inrCompInlCompAssociator, inlCompInrCompInverseAssociator]
    | inr e => by simp [inrCompAssociator, inrCompInrCompInverseAssociator]

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.sum
