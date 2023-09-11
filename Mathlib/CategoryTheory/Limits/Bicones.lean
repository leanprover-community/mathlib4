/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.limits.bicones
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.FinCategory

/-!
# Bicones

Given a category `J`, a walking `Bicone J` is a category whose objects are the objects of `J` and
two extra vertices `Bicone.left` and `Bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `⬝ ⟶ j` and `⬝ ⟶ k` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C` via
`biconeMk`.

This is used in `CategoryTheory.Functor.Flat`.
-/


universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

open Classical

namespace CategoryTheory

section Bicone

/-- Given a category `J`, construct a walking `Bicone J` by adjoining two elements. -/
inductive Bicone (J : Type u₁)
  | left : Bicone J
  | right : Bicone J
  | diagram (val : J) : Bicone J
  deriving DecidableEq
#align category_theory.bicone CategoryTheory.Bicone

variable (J : Type u₁)

instance : Inhabited (Bicone J) :=
  ⟨Bicone.left⟩

instance finBicone [Fintype J] : Fintype (Bicone J)
    where
  elems := [Bicone.left, Bicone.right].toFinset ∪ Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp
    apply Fintype.complete
#align category_theory.fin_bicone CategoryTheory.finBicone

variable [Category.{v₁} J]

/-- The homs for a walking `Bicone J`. -/
inductive BiconeHom : Bicone J → Bicone J → Type max u₁ v₁
  | left_id : BiconeHom Bicone.left Bicone.left
  | right_id : BiconeHom Bicone.right Bicone.right
  | left (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
  | right (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)
#align category_theory.bicone_hom CategoryTheory.BiconeHom

instance : Inhabited (BiconeHom J Bicone.left Bicone.left) :=
  ⟨BiconeHom.left_id⟩

instance BiconeHom.decidableEq {j k : Bicone J} : DecidableEq (BiconeHom J j k) := fun f g => by
  cases f <;> cases g <;> simp <;> infer_instance
#align category_theory.bicone_hom.decidable_eq CategoryTheory.BiconeHom.decidableEq

@[simps]
instance biconeCategoryStruct : CategoryStruct (Bicone J)
    where
  Hom := BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    . exact g
    . exact g
    . cases g
      apply BiconeHom.left
    . cases g
      apply BiconeHom.right
    . rcases g with (_|_|_|_|g)
      exact BiconeHom.diagram (f ≫ g)
#align category_theory.bicone_category_struct CategoryTheory.biconeCategoryStruct

instance biconeCategory : Category (Bicone J)
    where
  id_comp f := by cases f <;> simp
  comp_id f := by cases f <;> simp
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp
#align category_theory.bicone_category CategoryTheory.biconeCategory

end Bicone

section SmallCategory

variable (J : Type v₁) [SmallCategory J]

/-- Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C`.
-/
@[simps]
def biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bicone J ⥤ C
    where
  obj X := Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_|_|_|_|f)
    . exact 𝟙 _
    . exact 𝟙 _
    . exact c₁.π.app _
    . exact c₂.π.app _
    . exact F.map f
  map_id X := by cases X <;> simp
  map_comp f g := by
    rcases f with (_|_|_|_|_)
    . exact (Category.id_comp _).symm
    . exact (Category.id_comp _).symm
    . cases g
      exact (Category.id_comp _).symm.trans (c₁.π.naturality _)
    . cases g
      exact (Category.id_comp _).symm.trans (c₂.π.naturality _)
    . cases g
      apply F.map_comp
#align category_theory.bicone_mk CategoryTheory.biconeMk

instance finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  . exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  . exact
    { elems := ∅
      complete := fun f => by cases f }
  . exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  . exact
    { elems := ∅
      complete := fun f => by cases f }
  . exact
      { elems := {BiconeHom.right_id}
        complete := fun f => by cases f; simp }
  . exact
    { elems := {BiconeHom.right _}
      complete := fun f => by cases f; simp }
  . exact
    { elems := ∅
      complete := fun f => by cases f }
  . exact
    { elems := ∅
      complete := fun f => by cases f }
  . exact
    { elems := Finset.image BiconeHom.diagram Fintype.elems
      complete := fun f => by
        rcases f with (_|_|_|_|f)
        simp only [Finset.mem_image]
        use f
        simpa using Fintype.complete _ }
#align category_theory.fin_bicone_hom CategoryTheory.finBiconeHom

instance biconeSmallCategory : SmallCategory (Bicone J) :=
  CategoryTheory.biconeCategory J
#align category_theory.bicone_small_category CategoryTheory.biconeSmallCategory

instance biconeFinCategory [FinCategory J] : FinCategory (Bicone J) where
#align category_theory.bicone_fin_category CategoryTheory.biconeFinCategory

end SmallCategory

end CategoryTheory
