/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow

/-!
# Kan extensions

The basic definitions for Kan extensions of functors is introduced in this file. Part of API
is parallel to the definitions for bicategories (see `CategoryTheory.Bicategory.Kan.IsKan`).
(The bicategory API cannot be used directly here because it would not allow the universe
polymorphism which is necessary for some applications.)

Given a natural transformation `α : L ⋙ F' ⟶ F`, we define the property
`F'.IsRightKanExtension α` which expresses that `(F', α)` is a right Kan
extension of `F` along `L`, i.e. that it is a terminal object in a
category `RightExtension L F` of costructured arrows. The condition
`F'.IsLeftKanExtension α` for `α : F ⟶ L ⋙ F'` is defined similarly.

## TODO (@joelriou)

* define a property `HasRightKanExtension L F` and related API
* define a condition expressing that a functor is a pointwise Kan extension
* refactor the file `CategoryTheory.Limits.KanExtension` using this new general API
* define left/right derived functors as particular cases of Kan extensions

## References
https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]

/-- Given two functors `L : C ⥤ H` and `F : C ⥤ D`, this is the category of functors
`F' : H ⥤ D` equipped with a natural transformation `L ⋙ F' ⟶ F`. -/
abbrev RightExtension (L : C ⥤ H) (F : C ⥤ D) :=
  CostructuredArrow ((whiskeringLeft C H D).obj L) F

/-- Given two functors `L : C ⥤ H` and `F : C ⥤ D`, this is the category of functors
`F' : H ⥤ D` equipped with a natural transformation `F ⟶ L ⋙ F'`. -/
abbrev LeftExtension (L : C ⥤ H) (F : C ⥤ D) :=
  StructuredArrow F ((whiskeringLeft C H D).obj L)

/-- Constructor for objects of the category `Functor.RightExtension L F`. -/
@[simps!]
def RightExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) :
    RightExtension L F :=
  CostructuredArrow.mk α

/-- Constructor for objects of the category `Functor.LeftExtension L F`. -/
@[simps!]
def LeftExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') :
    LeftExtension L F :=
  StructuredArrow.mk α

section

variable (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F)

/-- Given `α : L ⋙ F' ⟶ F`, the property `F'.IsRightKanExtension α` asserts that
`(F', α)` is a terminal object in the category `RightExtension L F`, i.e. that `(F', α)`
is a right Kan extension of `F` along `L`. -/
class IsRightKanExtension : Prop where
  nonempty_isUniversal : Nonempty (RightExtension.mk F' α).IsUniversal

variable [F'.IsRightKanExtension α]

/-- If `(F', α)` is a right Kan extension of `F` along `L`, then `(F', α)` is a terminal object
in the category `RightExtension L F`. -/
noncomputable def isUniversalOfIsRightKanExtension : (RightExtension.mk F' α).IsUniversal :=
  IsRightKanExtension.nonempty_isUniversal.some

/-- If `(F', α)` is a right Kan extension of `F` along `L` and `β : L ⋙ G ⟶ F` is
a natural transformation, this is the induced morphism `G ⟶ F'`. -/
noncomputable def liftOfIsRightKanExtension (G : H ⥤ D) (β : L ⋙ G ⟶ F) : G ⟶ F' :=
  (F'.isUniversalOfIsRightKanExtension α).lift (RightExtension.mk G β)

lemma liftOfIsRightKanExtension_fac (G : H ⥤ D) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]
lemma liftOfIsRightKanExtension_fac_app (G : H ⥤ D) (β : L ⋙ G ⟶ F) (X : C) :
    (F'.liftOfIsRightKanExtension α G β).app (L.obj X) ≫ α.app X = β.app X :=
  NatTrans.congr_app (F'.liftOfIsRightKanExtension_fac α G β) X

lemma hom_ext_of_isRightKanExtension {G : H ⥤ D} (γ₁ γ₂ : G ⟶ F')
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsRightKanExtension α).hom_ext hγ

lemma isRightKanExtension_of_iso {F' F'' : H ⥤ D} (e : F' ≅ F'') {L : C ⥤ H} {F : C ⥤ D}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α)
    [F'.IsRightKanExtension α] : F''.IsRightKanExtension α' where
  nonempty_isUniversal := ⟨IsTerminal.ofIso (F'.isUniversalOfIsRightKanExtension α)
    (CostructuredArrow.isoMk e comm)⟩

lemma isRightKanExtension_iff_of_iso {F' F'' : H ⥤ D} (e : F' ≅ F'') {L : C ⥤ H} {F : C ⥤ D}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α) :
    F'.IsRightKanExtension α ↔ F''.IsRightKanExtension α' := by
  constructor
  · intro
    exact isRightKanExtension_of_iso e α α' comm
  · intro
    refine isRightKanExtension_of_iso e.symm α' α ?_
    rw [← comm, ← whiskerLeft_comp_assoc, Iso.symm_hom, e.inv_hom_id, whiskerLeft_id', id_comp]

end

section

variable (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F')

/-- Given `α : F ⟶ L ⋙ F'`, the property `F'.IsLeftKanExtension α` asserts that
`(F', α)` is an initial object in the category `LeftExtension L F`, i.e. that `(F', α)`
is a left Kan extension of `F` along `L`. -/
class IsLeftKanExtension : Prop where
  nonempty_isUniversal : Nonempty (LeftExtension.mk F' α).IsUniversal

variable [F'.IsLeftKanExtension α]

/-- If `(F', α)` is a left Kan extension of `F` along `L`, then `(F', α)` is an initial object
in the category `LeftExtension L F`. -/
noncomputable def isUniversalOfIsLeftKanExtension : (LeftExtension.mk F' α).IsUniversal :=
    IsLeftKanExtension.nonempty_isUniversal.some

/-- If `(F', α)` is a left Kan extension of `F` along `L` and `β : F ⟶ L ⋙ G` is
a natural transformation, this is the induced morphisms `F' ⟶ G`. -/
noncomputable def descOfIsLeftKanExtension (G : H ⥤ D) (β : F ⟶ L ⋙ G) : F' ⟶ G :=
  (F'.isUniversalOfIsLeftKanExtension α).desc (LeftExtension.mk G β)

lemma descOfIsLeftKanExtension_fac (G : H ⥤ D) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (F'.descOfIsLeftKanExtension α G β) = β :=
  (F'.isUniversalOfIsLeftKanExtension α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]
lemma descOfIsLeftKanExtension_fac_app (G : H ⥤ D) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (F'.descOfIsLeftKanExtension α G β).app (L.obj X) = β.app X :=
  NatTrans.congr_app (F'.descOfIsLeftKanExtension_fac α G β) X

lemma hom_ext_of_isLeftKanExtension {G : H ⥤ D} (γ₁ γ₂ : F' ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsLeftKanExtension α).hom_ext hγ

lemma isLeftKanExtension_of_iso {F' : H ⥤ D} {F'' : H ⥤ D} (e : F' ≅ F'')
    {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' where
  nonempty_isUniversal := ⟨IsInitial.ofIso (F'.isUniversalOfIsLeftKanExtension α)
    (StructuredArrow.isoMk e comm)⟩

lemma isLeftKanExtension_iff_of_iso {F' : H ⥤ D} {F'' : H ⥤ D} (e : F' ≅ F'')
    {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') :
    F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α' := by
  constructor
  · intro
    exact isLeftKanExtension_of_iso e α α' comm
  · intro
    refine isLeftKanExtension_of_iso e.symm α' α ?_
    rw [← comm, assoc, ← whiskerLeft_comp, Iso.symm_hom, e.hom_inv_id, whiskerLeft_id', comp_id]

end

end Functor

end CategoryTheory
