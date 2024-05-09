/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.Extra
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

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

def Limits.IsInitial.equivOfIso {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) :
    IsInitial X ≃ IsInitial Y where
  toFun h := IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def Limits.IsTerminal.equivOfIso {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) :
    IsTerminal X ≃ IsTerminal Y where
  toFun h := IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

namespace Functor

variable {C C' D D' H H' : Type*} [Category C] [Category D] [Category H] [Category H']
  [Category D'] [Category C']

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
a natural transformation, this is the induced morphism `F' ⟶ G`. -/
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

/-- This property `HasRightKanExtension L F` holds when the functor `F` has a right
Kan extension along `L`. -/
abbrev HasRightKanExtension (L : C ⥤ H) (F : C ⥤ D) := HasTerminal (RightExtension L F)

lemma HasRightKanExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F :=
  (F'.isUniversalOfIsRightKanExtension α).hasTerminal

/-- This property `HasLeftKanExtension L F` holds when the functor `F` has a left
Kan extension along `L`. -/
abbrev HasLeftKanExtension (L : C ⥤ H) (F : C ⥤ D) := HasInitial (LeftExtension L F)

lemma HasLeftKanExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] : HasLeftKanExtension L F :=
  (F'.isUniversalOfIsLeftKanExtension α).hasInitial

section

variable (L : C ⥤ H) (F : C ⥤ D) [HasRightKanExtension L F]

/-- A chosen right Kan extension when `[HasRightKanExtension L F]` holds. -/
noncomputable def rightKanExtension : H ⥤ D := (⊤_ _ : RightExtension L F).left

/-- The counit of the chosen right Kan extension `rightKanExtension L F`. -/
noncomputable def rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F :=
  (⊤_ _ : RightExtension L F).hom

instance : (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F) where
  nonempty_isUniversal := ⟨terminalIsTerminal⟩

@[ext]
lemma rightKanExtension_hom_ext {G : H ⥤ D} (γ₁ γ₂ : G ⟶ rightKanExtension L F)
    (hγ : whiskerLeft L γ₁ ≫ rightKanExtensionCounit L F =
      whiskerLeft L γ₂ ≫ rightKanExtensionCounit L F) :
    γ₁ = γ₂ :=
  hom_ext_of_isRightKanExtension _ _ _ _ hγ

end

section

variable (L : C ⥤ H) (F : C ⥤ D) [HasLeftKanExtension L F]

/-- A chosen left Kan extension when `[HasLeftKanExtension L F]` holds. -/
noncomputable def leftKanExtension : H ⥤ D := (⊥_ _ : LeftExtension L F).right

/-- The unit of the chosen left Kan extension `leftKanExtension L F`. -/
noncomputable def leftKanExtensionUnit : F ⟶ L ⋙ leftKanExtension L F :=
  (⊥_ _ : LeftExtension L F).hom

instance : (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) where
  nonempty_isUniversal := ⟨initialIsInitial⟩

@[ext]
lemma leftKanExtension_hom_ext {G : H ⥤ D} (γ₁ γ₂ : leftKanExtension L F ⟶ G)
    (hγ : leftKanExtensionUnit L F ≫ whiskerLeft L γ₁ =
      leftKanExtensionUnit L F ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  hom_ext_of_isLeftKanExtension _ _ _ _ hγ

end

section

variable (L : C ⥤ H) (F : C ⥤ D) (e : H ≌ H')

/-- The equivalence of categories `RightExtension (L ⋙ e.functor) F ≌ RightExtension L F`
when `e` is an equivalence. -/
noncomputable def rightExtensionEquivalenceOfPostcomp₁ :
    RightExtension (L ⋙ e.functor) F ≌ RightExtension L F := by
  have := CostructuredArrow.isEquivalencePre ((whiskeringLeft H H' D).obj e.functor)
    ((whiskeringLeft C H D).obj L) F
  exact Functor.asEquivalence (CostructuredArrow.pre ((whiskeringLeft H H' D).obj e.functor)
    ((whiskeringLeft C H D).obj L) F)

lemma hasRightExtension_iff_postcomp₁ :
    HasRightKanExtension L F ↔ HasRightKanExtension (L ⋙ e.functor) F :=
  (rightExtensionEquivalenceOfPostcomp₁ L F e).symm.hasTerminal_iff

--/-- The equivalence of categories `LeftExtension (L ⋙ e.functor) F ≌ LeftExtension L F`
--when `e` is an equivalence. -/
--noncomputable def leftExtensionEquivalenceOfPostcomp₁ :
--    LeftExtension (L ⋙ e.functor) F ≌ LeftExtension L F := by
--  have := StructuredArrow.isEquivalencePre F ((whiskeringLeft H H' D).obj e.functor)
--    ((whiskeringLeft C H D).obj L)
--  exact Functor.asEquivalence (StructuredArrow.pre F ((whiskeringLeft H H' D).obj e.functor)
--    ((whiskeringLeft C H D).obj L))
--
--lemma hasLeftExtension_iff_postcomp₁ :
--    HasLeftKanExtension L F ↔ HasLeftKanExtension (L ⋙ e.functor) F :=
--  (leftExtensionEquivalenceOfPostcomp₁ L F e).symm.hasInitial_iff

end

section

variable (L L' : C ⥤ H) (iso₁ : L ≅ L') (F F' : C ⥤ D) (iso₂ : F ≅ F')
variable {L L'}

/-- The equivalence `RightExtension L F ≌ RightExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
def rightExtensionEquivalenceOfIso₁ : RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C H D).mapIso iso₁)

lemma hasRightExtension_iff_of_iso₁ : HasRightKanExtension L F ↔ HasRightKanExtension L' F :=
  (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

/-- The equivalence `LeftExtension L F ≌ LeftExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
def leftExtensionEquivalenceOfIso₁ : LeftExtension L F ≌ LeftExtension L' F :=
  StructuredArrow.mapNatIso ((whiskeringLeft C H D).mapIso iso₁)

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

section

variable {L : C ⥤ H} {L' : C ⥤ H'}
  (G : H ⥤ H') [IsEquivalence G] (e : L ⋙ G ≅ L')
  (F : C ⥤ D) (F' : H' ⥤ D) (α : F ⟶ L' ⋙ F')

@[simps!]
def LeftExtension.postcomp₁ : LeftExtension L' F ⥤ LeftExtension L F :=
  StructuredArrow.map₂ (F := (whiskeringLeft H H' D).obj G) (G := 𝟭 _) (𝟙 _)
    ((whiskeringLeft C H' D).map e.inv)

noncomputable instance : IsEquivalence (LeftExtension.postcomp₁ G e F) := by
  have : EssSurj ((whiskeringLeft H H' D).obj G) := Equivalence.essSurj_of_equivalence _
  apply StructuredArrow.isEquivalenceMap₂

variable {G} in
lemma hasLeftExtension_iff_postcomp₁ :
    HasLeftKanExtension L' F ↔ HasLeftKanExtension L F :=
  (LeftExtension.postcomp₁ G e F).asEquivalence.hasInitial_iff

lemma LeftExtension.isUniversalPostcomp₁Equiv (ex : LeftExtension L' F) :
    ex.IsUniversal ≃ ((LeftExtension.postcomp₁ G e F).obj ex).IsUniversal := by
  apply Limits.IsInitial.isInitialIffObj (LeftExtension.postcomp₁ G e F)

variable {F F'}

lemma isLeftKanExtension_iff_postcomp₁ :
    F'.IsLeftKanExtension α ↔
      (G ⋙ F').IsLeftKanExtension (α ≫ whiskerRight e.inv _ ≫ (Functor.associator _ _ _).hom) := by
  let ex := LeftExtension.mk _ α
  let ex' := LeftExtension.mk _ (α ≫ whiskerRight e.inv _ ≫ (Functor.associator _ _ _).hom)
  have : ex.IsUniversal ≃ ex'.IsUniversal :=
    (LeftExtension.isUniversalPostcomp₁Equiv G e F ex).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · intro
    exact ⟨⟨this (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · intro
    exact ⟨⟨this.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

end

section

variable (L : C ⥤ H) (F : C ⥤ D)
  (F' : H ⥤ D) (α : F ⟶ L ⋙ F')
  (G : D ⥤ D') [IsEquivalence G]

@[simps!]
def LeftExtension.postcomp₂ : LeftExtension L F ⥤ LeftExtension L (F ⋙ G) :=
  StructuredArrow.map₂ (F := (whiskeringRight H D D').obj G)
    (G := (whiskeringRight C D D').obj G) (𝟙 _) (𝟙 _)

noncomputable instance : IsEquivalence (LeftExtension.postcomp₂ L F G) := by
  have : EssSurj ((whiskeringRight H D D').obj G) := Equivalence.essSurj_of_equivalence _
  apply StructuredArrow.isEquivalenceMap₂

lemma LeftExtension.isUniversalPostcompEquiv (e : LeftExtension L F) :
    e.IsUniversal ≃ ((LeftExtension.postcomp₂ L F G).obj e).IsUniversal := by
  apply Limits.IsInitial.isInitialIffObj (LeftExtension.postcomp₂ L F G)

variable {L F}

lemma isLeftKanExtension_iff_postcomp₂ :
    F'.IsLeftKanExtension α ↔
      (F' ⋙ G).IsLeftKanExtension (whiskerRight α G ≫ (Functor.associator _ _ _).hom) := by
  let e := LeftExtension.mk _ α
  let e' := LeftExtension.mk _ (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
  have : e.IsUniversal ≃ e'.IsUniversal :=
    (LeftExtension.isUniversalPostcompEquiv L F G e).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · intro
    exact ⟨⟨this (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · intro
    exact ⟨⟨this.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

end

section

variable (L : C ⥤ H) (F : C ⥤ D)
  (F' : H ⥤ D) (α : F ⟶ L ⋙ F')
  (G : C' ⥤ C) [IsEquivalence G]


@[simps!]
def LeftExtension.precomp : LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F) :=
  StructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C D).obj G) (𝟙 _) (𝟙 _)

noncomputable instance : IsEquivalence (LeftExtension.precomp L F G) := by
  apply StructuredArrow.isEquivalenceMap₂

lemma LeftExtension.isUniversalPrecompEquiv (e : LeftExtension L F) :
    e.IsUniversal ≃ ((LeftExtension.precomp L F G).obj e).IsUniversal := by
  apply Limits.IsInitial.isInitialIffObj (LeftExtension.precomp L F G)

variable {F L}

lemma isLeftKanExtension_iff_precomp :
    F'.IsLeftKanExtension α ↔ F'.IsLeftKanExtension
          (whiskerLeft G α ≫ (Functor.associator _ _ _).inv) := by
  let e := LeftExtension.mk _ α
  let e' := LeftExtension.mk _ (whiskerLeft G α ≫ (Functor.associator _ _ _).inv)
  have : e.IsUniversal ≃ e'.IsUniversal :=
    (LeftExtension.isUniversalPrecompEquiv L F G e).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · intro
    exact ⟨⟨this (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · intro
    exact ⟨⟨this.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

end

section

variable {L : C ⥤ H} {F₁ F₂ : C ⥤ D}

/-- When two left extensions `α₁ : LeftExtension L F₁` and `α₂ : LeftExtension L F₂`
are essentially the same via an isomorphism of functors `F₁ ≅ F₂`,
then `α₁` is universal iff `α₂` is. -/
noncomputable def LeftExtension.isUniversalEquivOfIso₂
    (α₁ : LeftExtension L F₁) (α₂ : LeftExtension L F₂) (e : F₁ ≅ F₂)
    (e' : α₁.right ≅ α₂.right)
    (h : α₁.hom ≫ whiskerLeft L e'.hom = e.hom ≫ α₂.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal :=
  (IsInitial.isInitialIffObj (leftExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk e'
      (by simp [leftExtensionEquivalenceOfIso₂, h])))

lemma isLeftKanExtension_iff_of_iso₂ {F₁' F₂' : H ⥤ D} (α₁ : F₁ ⟶ L ⋙ F₁') (α₂ : F₂ ⟶ L ⋙ F₂')
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : α₁ ≫ whiskerLeft L e'.hom = e.hom ≫ α₂) :
    F₁'.IsLeftKanExtension α₁ ↔ F₂'.IsLeftKanExtension α₂ := by
  let eq := LeftExtension.isUniversalEquivOfIso₂ (LeftExtension.mk _ α₁)
    (LeftExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsLeftKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsLeftKanExtension F₂' α₂)⟩⟩

/-- When two right extensions `α₁ : RightExtension L F₁` and `α₂ : RightExtension L F₂`
are essentially the same via an isomorphism of functors `F₁ ≅ F₂`,
then `α₁` is universal iff `α₂` is. -/
noncomputable def RightExtension.isUniversalEquivOfIso₂
    (α₁ : RightExtension L F₁) (α₂ : RightExtension L F₂) (e : F₁ ≅ F₂)
    (e' : α₁.left ≅ α₂.left)
    (h : whiskerLeft L e'.hom ≫ α₂.hom = α₁.hom ≫ e.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal :=
  (IsTerminal.isTerminalIffObj (rightExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk e'
      (by simp [rightExtensionEquivalenceOfIso₂, h])))

lemma isRightKanExtension_iff_of_iso₂ {F₁' F₂' : H ⥤ D} (α₁ : L ⋙ F₁' ⟶ F₁) (α₂ : L ⋙ F₂' ⟶ F₂)
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : whiskerLeft L e'.hom ≫ α₂ = α₁ ≫ e.hom) :
    F₁'.IsRightKanExtension α₁ ↔ F₂'.IsRightKanExtension α₂ := by
  let eq := RightExtension.isUniversalEquivOfIso₂ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

end

section

variable {L₁ L₂ : C ⥤ H} {F₁ F₂ : C ⥤ D}

/-- When two left extensions `α₁ : RightExtension L₁ F₁` and `α₂ : RightExtension L₂ F₂`
are essentially the same via isomorphism of functors `F₁ ≅ F₂` and `L₁ ≅ L₂`,
then `α₁` is universal iff `α₂` is. -/
noncomputable def LeftExtension.isUniversalEquivOfIso₃
    (α₁ : LeftExtension L₁ F₁) (α₂ : LeftExtension L₂ F₂)
    (e : F₁ ≅ F₂) (e' : α₁.right ≅ α₂.right) (e'' : L₁ ≅ L₂)
    (h : α₁.hom ≫ whiskerLeft L₁ e'.hom = e.hom ≫ α₂.hom ≫ whiskerRight e''.inv _) :
    α₁.IsUniversal ≃ α₂.IsUniversal := by
  apply (LeftExtension.isUniversalEquivOfIso₂ α₁
    (LeftExtension.mk _ (e.inv ≫ α₁.hom ≫ whiskerLeft L₁ e'.hom)) e e' (by aesop_cat)).trans
  apply (IsInitial.isInitialIffObj (leftExtensionEquivalenceOfIso₁ e'' F₂).functor _).trans
  refine' IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _) ?_)
  dsimp [leftExtensionEquivalenceOfIso₁]
  simp only [h, Iso.inv_hom_id_assoc, assoc, comp_id]
  ext X
  dsimp
  rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma isLeftKanExtension_iff_of_iso₃
    {F₁' F₂' : H ⥤ D} (α₁ : F₁ ⟶ L₁ ⋙ F₁') (α₂ : F₂ ⟶ L₂ ⋙ F₂')
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (e'' : L₁ ≅ L₂)
    (h : α₁ ≫ whiskerLeft L₁ e'.hom = e.hom ≫ α₂ ≫ whiskerRight e''.inv _) :
    F₁'.IsLeftKanExtension α₁ ↔ F₂'.IsLeftKanExtension α₂ := by
  let eq := LeftExtension.isUniversalEquivOfIso₃ (LeftExtension.mk _ α₁)
    (LeftExtension.mk _ α₂) e e' e'' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsLeftKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsLeftKanExtension F₂' α₂)⟩⟩

/-- When two right extensions `α₁ : RightExtension L₁ F₁` and `α₂ : RightExtension L₂ F₂`
are essentially the same via isomorphism of functors `F₁ ≅ F₂` and `L₁ ≅ L₂`,
then `α₁` is universal iff `α₂` is. -/
noncomputable def RightExtension.isUniversalEquivOfIso₃
    (α₁ : RightExtension L₁ F₁) (α₂ : RightExtension L₂ F₂)
    (e : F₁ ≅ F₂) (e' : α₁.left ≅ α₂.left) (e'' : L₁ ≅ L₂)
    (h : whiskerLeft L₂ e'.hom ≫ α₂.hom = whiskerRight e''.inv _ ≫ α₁.hom ≫ e.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal := by
  apply (RightExtension.isUniversalEquivOfIso₂ α₁
    (RightExtension.mk _ (whiskerLeft L₁ e'.inv ≫ α₁.hom ≫ e.hom)) e e' (by aesop_cat)).trans
  apply (IsTerminal.isTerminalIffObj (rightExtensionEquivalenceOfIso₁ e'' F₂).functor _).trans
  refine' IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _) ?_)
  dsimp [rightExtensionEquivalenceOfIso₁]
  rw [id_comp, ← cancel_epi (whiskerLeft L₂ e'.hom), h]
  ext X
  dsimp
  rw [NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]

lemma isRightKanExtension_iff_of_iso₃
    {F₁' F₂' : H ⥤ D} (α₁ : L₁ ⋙ F₁' ⟶ F₁) (α₂ : L₂ ⋙ F₂' ⟶ F₂)
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (e'' : L₁ ≅ L₂)
    (h : whiskerLeft L₂ e'.hom ≫ α₂ = whiskerRight e''.inv _ ≫ α₁ ≫ e.hom) :
    F₁'.IsRightKanExtension α₁ ↔ F₂'.IsRightKanExtension α₂ := by
  let eq := RightExtension.isUniversalEquivOfIso₃ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' e'' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

end

end Functor

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] (e : C ≌ D)

def whiskeringLeft (E : Type _) [Category E] : (D ⥤ E) ≌ (C ⥤ E) where
  functor := (CategoryTheory.whiskeringLeft C D E).obj e.functor
  inverse := (CategoryTheory.whiskeringLeft D C E).obj e.inverse
  unitIso := (CategoryTheory.whiskeringLeft D D E).mapIso e.counitIso.symm
  counitIso := (CategoryTheory.whiskeringLeft C C E).mapIso e.unitIso.symm
  functor_unitIso_comp F := by
    ext Y
    dsimp
    rw [← F.map_id, ← F.map_comp, counitInv_functor_comp]

end Equivalence

end CategoryTheory
