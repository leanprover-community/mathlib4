/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

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

We also introduce typeclasses `HasRightKanExtension L F` and `HasLeftKanExtension L F`
which assert the existence of a right or left Kan extension, and chosen Kan extensions
are obtained as `leftKanExtension L F` and `rightKanExtension L F`.

## TODO (@joelriou)

* define left/right derived functors as particular cases of Kan extensions

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C H D D' : Type*} [Category C] [Category H] [Category D] [Category D']

/-- Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : H ⥤ D` equipped with a natural transformation `L ⋙ F' ⟶ F`. -/
abbrev RightExtension (L : C ⥤ D) (F : C ⥤ H) :=
  CostructuredArrow ((whiskeringLeft C D H).obj L) F

/-- Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : H ⥤ D` equipped with a natural transformation `F ⟶ L ⋙ F'`. -/
abbrev LeftExtension (L : C ⥤ D) (F : C ⥤ H) :=
  StructuredArrow F ((whiskeringLeft C D H).obj L)

/-- Constructor for objects of the category `Functor.RightExtension L F`. -/
@[simps!]
def RightExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) :
    RightExtension L F :=
  CostructuredArrow.mk α

/-- Constructor for objects of the category `Functor.LeftExtension L F`. -/
@[simps!]
def LeftExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') :
    LeftExtension L F :=
  StructuredArrow.mk α

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)

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
noncomputable def liftOfIsRightKanExtension (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ F' :=
  (F'.isUniversalOfIsRightKanExtension α).lift (RightExtension.mk G β)

lemma liftOfIsRightKanExtension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]
lemma liftOfIsRightKanExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) :
    (F'.liftOfIsRightKanExtension α G β).app (L.obj X) ≫ α.app X = β.app X :=
  NatTrans.congr_app (F'.liftOfIsRightKanExtension_fac α G β) X

lemma hom_ext_of_isRightKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F')
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsRightKanExtension α).hom_ext hγ

lemma isRightKanExtension_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α)
    [F'.IsRightKanExtension α] : F''.IsRightKanExtension α' where
  nonempty_isUniversal := ⟨IsTerminal.ofIso (F'.isUniversalOfIsRightKanExtension α)
    (CostructuredArrow.isoMk e comm)⟩

lemma isRightKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
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

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')

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
a natural transformation, this is the induced morphism `F' ⟶ G`. -/
noncomputable def descOfIsLeftKanExtension (G : D ⥤ H) (β : F ⟶ L ⋙ G) : F' ⟶ G :=
  (F'.isUniversalOfIsLeftKanExtension α).desc (LeftExtension.mk G β)

@[reassoc (attr := simp)]
lemma descOfIsLeftKanExtension_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (F'.descOfIsLeftKanExtension α G β) = β :=
  (F'.isUniversalOfIsLeftKanExtension α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]
lemma descOfIsLeftKanExtension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (F'.descOfIsLeftKanExtension α G β).app (L.obj X) = β.app X :=
  NatTrans.congr_app (F'.descOfIsLeftKanExtension_fac α G β) X

lemma hom_ext_of_isLeftKanExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsLeftKanExtension α).hom_ext hγ

/-- If `(F', α)` is a left Kan extension of `F` along `L`, then this
is the induced bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)` for all `G`. -/
@[pp_dot]
noncomputable def homEquivOfIsLeftKanExtension (G : D ⥤ H) :
    (F' ⟶ G) ≃ (F ⟶ L ⋙ G) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by aesop_cat)
  right_inv := by aesop_cat

lemma isLeftKanExtension_of_iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' where
  nonempty_isUniversal := ⟨IsInitial.ofIso (F'.isUniversalOfIsLeftKanExtension α)
    (StructuredArrow.isoMk e comm)⟩

lemma isLeftKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') :
    F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α' := by
  constructor
  · intro
    exact isLeftKanExtension_of_iso e α α' comm
  · intro
    refine isLeftKanExtension_of_iso e.symm α' α ?_
    rw [← comm, assoc, ← whiskerLeft_comp, Iso.symm_hom, e.hom_inv_id, whiskerLeft_id', comp_id]

/-- Two left Kan extensions are (canonically) isomorphic. -/
@[simps]
noncomputable def leftKanExtensionUnique
    (F'' : D ⥤ H) (α' : F ⟶ L ⋙ F'') [F''.IsLeftKanExtension α'] : F' ≅ F'' where
  hom := F'.descOfIsLeftKanExtension α F'' α'
  inv := F''.descOfIsLeftKanExtension α' F' α
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := F''.hom_ext_of_isLeftKanExtension α' _ _ (by simp)

lemma isLeftKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L φ = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' ↔ IsIso φ := by
  constructor
  · intro
    rw [F'.hom_ext_of_isLeftKanExtension α φ (leftKanExtensionUnique _ α _ α').hom
      (by simp [comm])]
    infer_instance
  · intro
    exact isLeftKanExtension_of_iso (asIso φ) α α' comm

end

/-- This property `HasRightKanExtension L F` holds when the functor `F` has a right
Kan extension along `L`. -/
abbrev HasRightKanExtension (L : C ⥤ D) (F : C ⥤ H) := HasTerminal (RightExtension L F)

lemma HasRightKanExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F :=
  (F'.isUniversalOfIsRightKanExtension α).hasTerminal

/-- This property `HasLeftKanExtension L F` holds when the functor `F` has a left
Kan extension along `L`. -/
abbrev HasLeftKanExtension (L : C ⥤ D) (F : C ⥤ H) := HasInitial (LeftExtension L F)

lemma HasLeftKanExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] : HasLeftKanExtension L F :=
  (F'.isUniversalOfIsLeftKanExtension α).hasInitial

section

variable (L : C ⥤ D) (F : C ⥤ H) [HasRightKanExtension L F]

/-- A chosen right Kan extension when `[HasRightKanExtension L F]` holds. -/
noncomputable def rightKanExtension : D ⥤ H := (⊤_ _ : RightExtension L F).left

/-- The counit of the chosen right Kan extension `rightKanExtension L F`. -/
noncomputable def rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F :=
  (⊤_ _ : RightExtension L F).hom

instance : (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F) where
  nonempty_isUniversal := ⟨terminalIsTerminal⟩

@[ext]
lemma rightKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : G ⟶ rightKanExtension L F)
    (hγ : whiskerLeft L γ₁ ≫ rightKanExtensionCounit L F =
      whiskerLeft L γ₂ ≫ rightKanExtensionCounit L F) :
    γ₁ = γ₂ :=
  hom_ext_of_isRightKanExtension _ _ _ _ hγ

end

section

variable (L : C ⥤ D) (F : C ⥤ H) [HasLeftKanExtension L F]

/-- A chosen left Kan extension when `[HasLeftKanExtension L F]` holds. -/
noncomputable def leftKanExtension : D ⥤ H := (⊥_ _ : LeftExtension L F).right

/-- The unit of the chosen left Kan extension `leftKanExtension L F`. -/
noncomputable def leftKanExtensionUnit : F ⟶ L ⋙ leftKanExtension L F :=
  (⊥_ _ : LeftExtension L F).hom

instance : (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) where
  nonempty_isUniversal := ⟨initialIsInitial⟩

@[ext]
lemma leftKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : leftKanExtension L F ⟶ G)
    (hγ : leftKanExtensionUnit L F ≫ whiskerLeft L γ₁ =
      leftKanExtensionUnit L F ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  hom_ext_of_isLeftKanExtension _ _ _ _ hγ

end

section

variable (L L' : C ⥤ D) (iso₁ : L ≅ L') (F F' : C ⥤ H) (e : D ≌ D') (iso₂ : F ≅ F')

/-- The equivalence of categories `RightExtension (L ⋙ e.functor) F ≌ RightExtension L F`
when `e` is an equivalence. -/
noncomputable def rightExtensionEquivalenceOfPostcomp₁ :
    RightExtension (L ⋙ e.functor) F ≌ RightExtension L F := by
  have := CostructuredArrow.isEquivalencePre ((whiskeringLeft D D' H).obj e.functor)
    ((whiskeringLeft C D H).obj L) F
  exact Functor.asEquivalence (CostructuredArrow.pre ((whiskeringLeft D D' H).obj e.functor)
    ((whiskeringLeft C D H).obj L) F)

lemma hasRightExtension_iff_postcomp₁ :
    HasRightKanExtension L F ↔ HasRightKanExtension (L ⋙ e.functor) F :=
  (rightExtensionEquivalenceOfPostcomp₁ L F e).symm.hasTerminal_iff

/-- The equivalence of categories `LeftExtension (L ⋙ e.functor) F ≌ LeftExtension L F`
when `e` is an equivalence. -/
noncomputable def leftExtensionEquivalenceOfPostcomp₁ :
    LeftExtension (L ⋙ e.functor) F ≌ LeftExtension L F := by
  have := StructuredArrow.isEquivalencePre F ((whiskeringLeft D D' H).obj e.functor)
    ((whiskeringLeft C D H).obj L)
  exact Functor.asEquivalence (StructuredArrow.pre F ((whiskeringLeft D D' H).obj e.functor)
    ((whiskeringLeft C D H).obj L))

lemma hasLeftExtension_iff_postcomp₁ :
    HasLeftKanExtension L F ↔ HasLeftKanExtension (L ⋙ e.functor) F :=
  (leftExtensionEquivalenceOfPostcomp₁ L F e).symm.hasInitial_iff

variable {L L'}

/-- The equivalence `RightExtension L F ≌ RightExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
def rightExtensionEquivalenceOfIso₁ : RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

lemma hasRightExtension_iff_of_iso₁ : HasRightKanExtension L F ↔ HasRightKanExtension L' F :=
  (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

/-- The equivalence `LeftExtension L F ≌ LeftExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
def leftExtensionEquivalenceOfIso₁ : LeftExtension L F ≌ LeftExtension L' F :=
  StructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

lemma hasLeftExtension_iff_of_iso₁ : HasLeftKanExtension L F ↔ HasLeftKanExtension L' F :=
  (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff

variable (L) {F F'}

/-- The equivalence `RightExtension L F ≌ RightExtension L F'` induced by
a natural isomorphism `F ≅ F'`. -/
def rightExtensionEquivalenceOfIso₂ : RightExtension L F ≌ RightExtension L F' :=
  CostructuredArrow.mapIso iso₂

lemma hasRightExtension_iff_of_iso₂ : HasRightKanExtension L F ↔ HasRightKanExtension L F' :=
  (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff

/-- The equivalence `LeftExtension L F ≌ LeftExtension L F'` induced by
a natural isomorphism `F ≅ F'`. -/
def leftExtensionEquivalenceOfIso₂ : LeftExtension L F ≌ LeftExtension L F' :=
  StructuredArrow.mapIso iso₂

lemma hasLeftExtension_iff_of_iso₂ : HasLeftKanExtension L F ↔ HasLeftKanExtension L F' :=
  (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff

end

end Functor

end CategoryTheory
