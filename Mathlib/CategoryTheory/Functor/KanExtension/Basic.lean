/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
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

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits Functor

namespace Functor

variable {C C' H D D' : Type*} [Category C] [Category C'] [Category H] [Category D] [Category D']

/-- Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : D ⥤ H` equipped with a natural transformation `L ⋙ F' ⟶ F`. -/
abbrev RightExtension (L : C ⥤ D) (F : C ⥤ H) :=
  CostructuredArrow ((whiskeringLeft C D H).obj L) F

/-- Given two functors `L : C ⥤ D` and `F : C ⥤ H`, this is the category of functors
`F' : D ⥤ H` equipped with a natural transformation `F ⟶ L ⋙ F'`. -/
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

@[reassoc (attr := simp)]
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

/-- If `(F', α)` is a right Kan extension of `F` along `L`, then this
is the induced bijection `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` for all `G`. -/
noncomputable def homEquivOfIsRightKanExtension (G : D ⥤ H) :
    (G ⟶ F') ≃ (L ⋙ G ⟶ F) where
  toFun β := whiskerLeft _ β ≫ α
  invFun β := liftOfIsRightKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isRightKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

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

/-- Right Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
noncomputable def rightKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : L ⋙ G' ⟶ G) [G'.IsRightKanExtension β] : F' ≅ G' where
  hom := liftOfIsRightKanExtension _ β F' (α ≫ i.hom)
  inv := liftOfIsRightKanExtension _ α G' (β ≫ i.inv)
  hom_inv_id := F'.hom_ext_of_isRightKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isRightKanExtension β _ _ (by simp)

/-- Two right Kan extensions are (canonically) isomorphic. -/
@[simps!]
noncomputable def rightKanExtensionUnique
    (F'' : D ⥤ H) (α' : L ⋙ F'' ⟶ F) [F''.IsRightKanExtension α'] : F' ≅ F'' :=
  rightKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'


lemma isRightKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F')
    {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F)
    (comm : whiskerLeft L φ ≫ α = α') [F'.IsRightKanExtension α] :
    F''.IsRightKanExtension α' ↔ IsIso φ := by
  constructor
  · intro
    rw [F'.hom_ext_of_isRightKanExtension α φ (rightKanExtensionUnique _ α' _ α).hom
      (by simp [comm])]
    infer_instance
  · intro
    rw [isRightKanExtension_iff_of_iso (asIso φ) α' α comm]
    infer_instance
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
@[simps!]
noncomputable def homEquivOfIsLeftKanExtension (G : D ⥤ H) :
    (F' ⟶ G) ≃ (F ⟶ L ⋙ G) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

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

/-- Left Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
noncomputable def leftKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : G ⟶ L ⋙ G') [G'.IsLeftKanExtension β] : F' ≅ G' where
  hom := descOfIsLeftKanExtension _ α G' (i.hom ≫ β)
  inv := descOfIsLeftKanExtension _ β F' (i.inv ≫ α)
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isLeftKanExtension β _ _ (by simp)

/-- Two left Kan extensions are (canonically) isomorphic. -/
@[simps!]
noncomputable def leftKanExtensionUnique
    (F'' : D ⥤ H) (α' : F ⟶ L ⋙ F'') [F''.IsLeftKanExtension α'] : F' ≅ F'' :=
  leftKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'

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

variable {L : C ⥤ D} {L' : C ⥤ D'} (G : D ⥤ D')

/-- The functor `LeftExtension L' F ⥤ LeftExtension L F`
induced by a natural transformation `L' ⟶ L ⋙ G'`. -/
@[simps!]
def LeftExtension.postcomp₁ (f : L' ⟶ L ⋙ G) (F : C ⥤ H) :
    LeftExtension L' F ⥤ LeftExtension L F :=
  StructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _) (𝟙 _)
    ((whiskeringLeft C D' H).map f)

/-- The functor `RightExtension L' F ⥤ RightExtension L F`
induced by a natural transformation `L ⋙ G ⟶ L'`. -/
@[simps!]
def RightExtension.postcomp₁ (f : L ⋙ G ⟶ L') (F : C ⥤ H) :
    RightExtension L' F ⥤ RightExtension L F :=
  CostructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _)
    ((whiskeringLeft C D' H).map f) (𝟙 _)

variable [IsEquivalence G]

noncomputable instance (f : L' ⟶ L ⋙ G) [IsIso f] (F : C ⥤ H) :
    IsEquivalence (LeftExtension.postcomp₁ G f F) := by
  apply StructuredArrow.isEquivalenceMap₂

noncomputable instance (f : L ⋙ G ⟶ L') [IsIso f] (F : C ⥤ H) :
    IsEquivalence (RightExtension.postcomp₁ G f F) := by
  apply CostructuredArrow.isEquivalenceMap₂

variable {G} in
lemma hasLeftExtension_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) :
    HasLeftKanExtension L' F ↔ HasLeftKanExtension L F :=
  (LeftExtension.postcomp₁ G e.inv F).asEquivalence.hasInitial_iff

variable {G} in
lemma hasRightExtension_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) :
    HasRightKanExtension L' F ↔ HasRightKanExtension L F :=
  (RightExtension.postcomp₁ G e.hom F).asEquivalence.hasTerminal_iff

variable (e : L ⋙ G ≅ L') (F : C ⥤ H)

/-- Given an isomorphism `e : L ⋙ G ≅ L'`, a left extension of `F` along `L'` is universal
iff the corresponding left extension of `L` along `L` is. -/
noncomputable def LeftExtension.isUniversalPostcomp₁Equiv (ex : LeftExtension L' F) :
    ex.IsUniversal ≃ ((LeftExtension.postcomp₁ G e.inv F).obj ex).IsUniversal := by
  apply IsInitial.isInitialIffObj (LeftExtension.postcomp₁ G e.inv F)

/-- Given an isomorphism `e : L ⋙ G ≅ L'`, a right extension of `F` along `L'` is universal
iff the corresponding right extension of `L` along `L` is. -/
noncomputable def RightExtension.isUniversalPostcomp₁Equiv (ex : RightExtension L' F) :
    ex.IsUniversal ≃ ((RightExtension.postcomp₁ G e.hom F).obj ex).IsUniversal := by
  apply IsTerminal.isTerminalIffObj (RightExtension.postcomp₁ G e.hom F)

variable {F F'}

lemma isLeftKanExtension_iff_postcomp₁ (α : F ⟶ L' ⋙ F') :
    F'.IsLeftKanExtension α ↔ (G ⋙ F').IsLeftKanExtension
      (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom) := by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃
      (LeftExtension.mk _
        (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom)).IsUniversal :=
    (LeftExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

lemma isRightKanExtension_iff_postcomp₁ (α : L' ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔ (G ⋙ F').IsRightKanExtension
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α) := by
  let eq : (RightExtension.mk _ α).IsUniversal ≃
    (RightExtension.mk _
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α)).IsUniversal :=
  (RightExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension _ _)⟩⟩

end

section

variable (L : C ⥤ D) (F : C ⥤ H) (G : H ⥤ D')

/-- Given a left extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering by `G`
on the right. -/
@[simps!]
def LeftExtension.postcompose₂ : LeftExtension L F ⥤ LeftExtension L (F ⋙ G) :=
  StructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) ({app _ := (associator _ _ _).hom})

/-- Given a right extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering by `G`
on the right. -/
@[simps!]
def RightExtension.postcompose₂ : RightExtension L F ⥤ RightExtension L (F ⋙ G) :=
  CostructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    ({app _ := associator _ _ _|>.inv}) (𝟙 _)

variable {L F} {F' : D ⥤ H}
/-- An isomorphism to describe the action of `LeftExtension.postcompose₂` on terms of the form
`LeftExtension.mk _ α`. -/
@[simps!]
def LeftExtension.postcompose₂ObjMkIso (α : F ⟶ L ⋙ F') :
    (LeftExtension.postcompose₂ L F G).obj (.mk F' α) ≅
    .mk (F' ⋙ G) <| whiskerRight α G ≫ (associator _ _ _).hom :=
  StructuredArrow.isoMk (.refl _)

/-- An isomorphism to describe the action of `RightExtension.postcompose₂` on terms of the form
`RightExtension.mk _ α`. -/
@[simps!]
def RightExtension.postcompose₂ObjMkIso (α : L ⋙ F' ⟶ F) :
    (RightExtension.postcompose₂ L F G).obj (.mk F' α) ≅
    .mk (F' ⋙ G) <| (associator _ _ _).inv ≫ whiskerRight α G :=
  CostructuredArrow.isoMk (.refl _)

end

section

variable (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (G : C' ⥤ C)

/-- The functor `LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition. -/
@[simps!]
def LeftExtension.precomp : LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F) :=
  StructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

/-- The functor `RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition. -/
@[simps!]
def RightExtension.precomp : RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F) :=
  CostructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

variable [IsEquivalence G]

noncomputable instance : IsEquivalence (LeftExtension.precomp L F G) := by
  apply StructuredArrow.isEquivalenceMap₂

noncomputable instance : IsEquivalence (RightExtension.precomp L F G) := by
  apply CostructuredArrow.isEquivalenceMap₂

/-- If `G` is an equivalence, then a left extension of `F` along `L` is universal iff
the corresponding left extension of `G ⋙ F` along `G ⋙ L` is. -/
noncomputable def LeftExtension.isUniversalPrecompEquiv (e : LeftExtension L F) :
    e.IsUniversal ≃ ((LeftExtension.precomp L F G).obj e).IsUniversal := by
  apply IsInitial.isInitialIffObj (LeftExtension.precomp L F G)

/-- If `G` is an equivalence, then a right extension of `F` along `L` is universal iff
the corresponding left extension of `G ⋙ F` along `G ⋙ L` is. -/
noncomputable def RightExtension.isUniversalPrecompEquiv (e : RightExtension L F) :
    e.IsUniversal ≃ ((RightExtension.precomp L F G).obj e).IsUniversal := by
  apply IsTerminal.isTerminalIffObj (RightExtension.precomp L F G)

variable {F L}

lemma isLeftKanExtension_iff_precomp (α : F ⟶ L ⋙ F') :
    F'.IsLeftKanExtension α ↔ F'.IsLeftKanExtension
      (whiskerLeft G α ≫ (associator _ _ _).inv) := by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃ (LeftExtension.mk _
      (whiskerLeft G α ≫ (associator _ _ _).inv)).IsUniversal :=
    (LeftExtension.isUniversalPrecompEquiv L F G _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

lemma isRightKanExtension_iff_precomp (α : L ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔
      F'.IsRightKanExtension ((associator _ _ _).hom ≫ whiskerLeft G α) := by
  let eq : (RightExtension.mk _ α).IsUniversal ≃ (RightExtension.mk _
      ((associator _ _ _).hom ≫ whiskerLeft G α)).IsUniversal :=
    (RightExtension.isUniversalPrecompEquiv L F G _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension _ _)⟩⟩

end

section

variable {L L' : C ⥤ D} (iso₁ : L ≅ L') (F : C ⥤ H)

/-- The equivalence `RightExtension L F ≌ RightExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
def rightExtensionEquivalenceOfIso₁ : RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in
lemma hasRightExtension_iff_of_iso₁ : HasRightKanExtension L F ↔ HasRightKanExtension L' F :=
  (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

/-- The equivalence `LeftExtension L F ≌ LeftExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
@[simps!]
def leftExtensionEquivalenceOfIso₁ : LeftExtension L F ≌ LeftExtension L' F :=
  StructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in
lemma hasLeftExtension_iff_of_iso₁ : HasLeftKanExtension L F ↔ HasLeftKanExtension L' F :=
  (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff

end

section

variable (L : C ⥤ D) {F F' : C ⥤ H} (iso₂ : F ≅ F')

/-- The equivalence `RightExtension L F ≌ RightExtension L F'` induced by
a natural isomorphism `F ≅ F'`. -/
def rightExtensionEquivalenceOfIso₂ : RightExtension L F ≌ RightExtension L F' :=
  CostructuredArrow.mapIso iso₂

include iso₂ in
lemma hasRightExtension_iff_of_iso₂ : HasRightKanExtension L F ↔ HasRightKanExtension L F' :=
  (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff

/-- The equivalence `LeftExtension L F ≌ LeftExtension L F'` induced by
a natural isomorphism `F ≅ F'`. -/
def leftExtensionEquivalenceOfIso₂ : LeftExtension L F ≌ LeftExtension L F' :=
  StructuredArrow.mapIso iso₂

include iso₂ in
lemma hasLeftExtension_iff_of_iso₂ : HasLeftKanExtension L F ↔ HasLeftKanExtension L F' :=
  (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff

end

section

variable {L : C ⥤ D} {F₁ F₂ : C ⥤ H}

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

lemma isLeftKanExtension_iff_of_iso₂ {F₁' F₂' : D ⥤ H} (α₁ : F₁ ⟶ L ⋙ F₁') (α₂ : F₂ ⟶ L ⋙ F₂')
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

lemma isRightKanExtension_iff_of_iso₂ {F₁' F₂' : D ⥤ H} (α₁ : L ⋙ F₁' ⟶ F₁) (α₂ : L ⋙ F₂' ⟶ F₂)
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : whiskerLeft L e'.hom ≫ α₂ = α₁ ≫ e.hom) :
    F₁'.IsRightKanExtension α₁ ↔ F₂'.IsRightKanExtension α₂ := by
  let eq := RightExtension.isUniversalEquivOfIso₂ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

end

section transitivity

/-- A variant of `LeftExtension.precomp` where we precompose, and then
"whisker" the diagram by a given natural transformation `(α : F₀ ⟶ L ⋙ F₁)` -/
@[simps!]
def LeftExtension.precomp₂
    {F₀ : C ⥤ H} {L : C ⥤ D} {F₁ : D ⥤ H} (L' : D ⥤ D') (α : F₀ ⟶ L ⋙ F₁) :
    L'.LeftExtension F₁ ⥤ (L ⋙ L').LeftExtension F₀ :=
  LeftExtension.precomp L' F₁ L ⋙ StructuredArrow.map α

variable
    {L : C ⥤ D} {L' : D ⥤ D'}
    {F₀ : C ⥤ H} {F₁ : D ⥤ H} {F₂ : D' ⥤ H}
    (α : F₀ ⟶ L ⋙ F₁)

/-- If the right extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, if an extension
`b : L'.LeftExtension F₁` is universal, so is the "pasted" extension
`(LeftExtension.precomp₂ L' α).obj b`. -/
def LeftExtension.isUniversalPrecomp₂
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    {b : L'.LeftExtension F₁} (hb : b.IsUniversal) :
    ((LeftExtension.precomp₂ L' α).obj b).IsUniversal := by
  letI (y : (L ⋙ L').LeftExtension F₀) :
      Unique ((precomp₂ L' α).obj b ⟶ y) := by
    let u : L'.LeftExtension F₁ :=
      mk y.right <|
        hα.desc <| LeftExtension.mk _ <|
          y.hom ≫ (L.associator L' y.right).hom
    refine
      ⟨⟨StructuredArrow.homMk (hb.desc u) <| by
          ext x
          haveI hb_fac_app := congr_app (hb.fac u) (L.obj x)
          haveI hα_fac_app :=
            congr_app (hα.fac <| LeftExtension.mk _ <|
              y.hom ≫ (L.associator L' y.right).hom) x
          dsimp at hα_fac_app hb_fac_app
          simp [hb_fac_app, u, hα_fac_app]⟩, fun a => ?_⟩
    dsimp
    ext1
    apply hb.hom_ext
    apply hα.hom_ext
    ext t
    dsimp
    have a_w_t := congr_app a.w t
    have hb_fac_app := congr_app (hb.fac u) (L.obj t)
    have hα_fac_app :=
      congr_app
        (hα.fac <| LeftExtension.mk _ <|
          y.hom ≫ (L.associator L' y.right).hom) t
    dsimp at hb_fac_app hα_fac_app
    simp only [precomp₂_obj_left, const_obj_obj, whiskeringLeft_obj_obj,
      comp_obj, StructuredArrow.left_eq_id, const_obj_map, id_comp,
      precomp₂_obj_right, whiskeringLeft_obj_map, NatTrans.comp_app,
      precomp₂_obj_hom_app, whiskerLeft_app, assoc] at a_w_t
    simp [← a_w_t, hb_fac_app, u, hα_fac_app]
  apply IsInitial.ofUnique

/-- If the left extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, if an extension
`b : L'.LeftExtension F₁` is such that the "pasted" extension
`(LeftExtension.precomp₂ L' α).obj b` is universal, then `b` is itself
universal. -/
def LeftExtension.isUniversalOfPrecomp₂
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    {b : L'.LeftExtension F₁}
    (hb : ((LeftExtension.precomp₂ L' α).obj b).IsUniversal) :
    b.IsUniversal := by
  letI (y : L'.LeftExtension F₁) : Unique (b ⟶ y) := by
    let u : (LeftExtension.precomp₂ L' α).obj b ⟶
      (LeftExtension.precomp₂ L' α).obj y := hb.to _
    haveI := u.w
    simp only [precomp₂_obj_left, const_obj_obj, precomp₂_obj_right,
      whiskeringLeft_obj_obj, StructuredArrow.left_eq_id, const_obj_map, id_comp,
      whiskeringLeft_obj_map] at this
    refine
      ⟨⟨StructuredArrow.homMk u.right <| by
          apply hα.hom_ext
          ext t
          have := congr_app u.w t
          simp only [precomp₂_obj_left, const_obj_obj, precomp₂_obj_right,
            whiskeringLeft_obj_obj, comp_obj, StructuredArrow.left_eq_id,
            const_obj_map, id_comp, precomp₂_obj_hom_app, whiskeringLeft_obj_map,
            NatTrans.comp_app, whiskerLeft_app, assoc] at this
          simp [this]⟩, fun a => ?_⟩
    dsimp
    ext1
    apply hb.hom_ext
    ext t
    have := congr_app u.w t
    have a_w := a.w
    simp only [precomp₂_obj_left, const_obj_obj, precomp₂_obj_right,
      whiskeringLeft_obj_obj, comp_obj, StructuredArrow.left_eq_id,
      const_obj_map, id_comp, precomp₂_obj_hom_app, whiskeringLeft_obj_map,
      NatTrans.comp_app, whiskerLeft_app, assoc] at this a_w
    simp [← this, a_w]
  apply IsInitial.ofUnique

/-- If the left extension defined by `α : F₀ ⟶ L ⋙ F₁` is universal,
then for every `L' : D ⥤ D'`, `F₁ : D ⥤ H`, an extension
`b : L'.LeftExtension F₁` is universal if and only if
`(LeftExtension.precomp₂ L' α).obj b` is universal. -/
def LeftExtension.isUniversalPrecomp₂Equiv
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    (b : L'.LeftExtension F₁) :
    b.IsUniversal ≃ ((LeftExtension.precomp₂ L' α).obj b).IsUniversal where
  toFun h := LeftExtension.isUniversalPrecomp₂ α hα h
  invFun h := LeftExtension.isUniversalOfPrecomp₂ α hα h
  left_inv x := by subsingleton
  right_inv x := by subsingleton


theorem isLeftKanExtension_iff_postcompose [F₁.IsLeftKanExtension α]
    {F₂ : D' ⥤ H} (L'' : C ⥤ D') (e : L ⋙ L' ≅ L'') (β : F₁ ⟶ L' ⋙ F₂)
    (γ : F₀ ⟶ L'' ⋙ F₂)
    (hγ :
      α ≫ whiskerLeft _ β ≫
        (Functor.associator _ _ _).inv ≫ whiskerRight e.hom F₂ =
      γ := by aesop_cat) :
    F₂.IsLeftKanExtension β ↔ F₂.IsLeftKanExtension γ := by
  let Ψ := leftExtensionEquivalenceOfIso₁ e F₀
  obtain ⟨⟨hα⟩⟩ := (inferInstance : F₁.IsLeftKanExtension α)
  refine ⟨fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩, fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩⟩
  · apply IsInitial.isInitialIffObj Ψ.inverse _|>.invFun
    haveI := LeftExtension.isUniversalPrecomp₂ α hα h
    let i :
        (LeftExtension.precomp₂ L' α).obj (LeftExtension.mk F₂ β) ≅
        Ψ.inverse.obj (LeftExtension.mk F₂ γ) :=
      StructuredArrow.isoMk (NatIso.ofComponents fun _ ↦ .refl _) <| by
        ext x
        simp [Ψ, ← congr_app hγ x, ← Functor.map_comp]
    exact IsInitial.ofIso this i
  · apply LeftExtension.isUniversalOfPrecomp₂ α hα
    apply IsInitial.isInitialIffObj Ψ.functor _|>.invFun
    let i :
        (LeftExtension.mk F₂ γ) ≅
        Ψ.functor.obj <| (LeftExtension.precomp₂ L' α).obj <|
          LeftExtension.mk F₂ β :=
      StructuredArrow.isoMk (NatIso.ofComponents fun _ ↦ .refl _)
    exact IsInitial.ofIso h i

end transitivity

section Colimit

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') [F'.IsLeftKanExtension α]

/-- Construct a cocone for a left Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a functor
`L : C ⥤ D` given a cocone for `F`. -/
@[simps]
noncomputable def coconeOfIsLeftKanExtension (c : Cocone F) : Cocone F' where
  pt := c.pt
  ι := F'.descOfIsLeftKanExtension α _ c.ι

/-- If `c` is a colimit cocone for a functor `F : C ⥤ H` and `α : F ⟶ L ⋙ F'` is the unit of any
left Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coconeOfIsLeftKanExtension α c` is
a colimit cocone, too. -/
@[simps]
noncomputable def isColimitCoconeOfIsLeftKanExtension {c : Cocone F} (hc : IsColimit c) :
    IsColimit (F'.coconeOfIsLeftKanExtension α c) where
  desc s := hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))
  fac s := by
    have : F'.descOfIsLeftKanExtension α ((const D).obj c.pt) c.ι ≫
        (Functor.const _).map (hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))) = s.ι :=
      F'.hom_ext_of_isLeftKanExtension α _ _ (by cat_disch)
    exact congr_app this
  uniq s m hm := hc.hom_ext (fun j ↦ by
    have := hm (L.obj j)
    nth_rw 1 [← F'.descOfIsLeftKanExtension_fac_app α ((const D).obj c.pt)]
    dsimp at this ⊢
    rw [assoc, this, IsColimit.fac, NatTrans.comp_app, whiskerLeft_app])

variable [HasColimit F] [HasColimit F']

/-- If `F' : D ⥤ H` is a left Kan extension of `F : C ⥤ H` along `L : C ⥤ D`, the colimit over `F'`
is isomorphic to the colimit over `F`. -/
noncomputable def colimitIsoOfIsLeftKanExtension : colimit F' ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit F')
    (F'.isColimitCoconeOfIsLeftKanExtension α (colimit.isColimit F))

@[reassoc (attr := simp)]
lemma ι_colimitIsoOfIsLeftKanExtension_hom (i : C) :
    α.app i ≫ colimit.ι F' (L.obj i) ≫ (F'.colimitIsoOfIsLeftKanExtension α).hom =
      colimit.ι F i := by
  simp [colimitIsoOfIsLeftKanExtension]

@[reassoc (attr := simp)]
lemma ι_colimitIsoOfIsLeftKanExtension_inv (i : C) :
    colimit.ι F i ≫ (F'.colimitIsoOfIsLeftKanExtension α).inv =
    α.app i ≫ colimit.ι F' (L.obj i) := by
  rw [Iso.comp_inv_eq, assoc, ι_colimitIsoOfIsLeftKanExtension_hom]

end Colimit

section Limit

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α]

/-- Construct a cone for a right Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a functor
`L : C ⥤ D` given a cone for `F`. -/
@[simps]
noncomputable def coneOfIsRightKanExtension (c : Cone F) : Cone F' where
  pt := c.pt
  π := F'.liftOfIsRightKanExtension α _ c.π

/-- If `c` is a limit cone for a functor `F : C ⥤ H` and `α : L ⋙ F' ⟶ F` is the counit of any
right Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coneOfIsRightKanExtension α c` is
a limit cone, too. -/
@[simps]
noncomputable def isLimitConeOfIsRightKanExtension {c : Cone F} (hc : IsLimit c) :
    IsLimit (F'.coneOfIsRightKanExtension α c) where
  lift s := hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))
  fac s := by
    have : (Functor.const _).map (hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))) ≫
        F'.liftOfIsRightKanExtension α ((const D).obj c.pt) c.π = s.π :=
      F'.hom_ext_of_isRightKanExtension α _ _ (by cat_disch)
    exact congr_app this
  uniq s m hm := hc.hom_ext (fun j ↦ by
    have := hm (L.obj j)
    nth_rw 1 [← F'.liftOfIsRightKanExtension_fac_app α ((const D).obj c.pt)]
    dsimp at this ⊢
    rw [← assoc, this, IsLimit.fac, NatTrans.comp_app, whiskerLeft_app])

variable [HasLimit F] [HasLimit F']

/-- If `F' : D ⥤ H` is a right Kan extension of `F : C ⥤ H` along `L : C ⥤ D`, the limit over `F'`
is isomorphic to the limit over `F`. -/
noncomputable def limitIsoOfIsRightKanExtension : limit F' ≅ limit F :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F')
    (F'.isLimitConeOfIsRightKanExtension α (limit.isLimit F))

@[reassoc (attr := simp)]
lemma limitIsoOfIsRightKanExtension_inv_π (i : C) :
    (F'.limitIsoOfIsRightKanExtension α).inv ≫ limit.π F' (L.obj i) ≫ α.app i = limit.π F i := by
  simp [limitIsoOfIsRightKanExtension]

@[reassoc (attr := simp)]
lemma limitIsoOfIsRightKanExtension_hom_π (i : C) :
    (F'.limitIsoOfIsRightKanExtension α).hom ≫ limit.π F i = limit.π F' (L.obj i) ≫ α.app i := by
  rw [← Iso.eq_inv_comp, limitIsoOfIsRightKanExtension_inv_π]

end Limit

section

variable {L : C ≌ D} {F₀ : C ⥤ H} {F₁ : D ⥤ H}

variable (F₀) in
instance isLeftKanExtensionId : F₀.IsLeftKanExtension F₀.leftUnitor.inv where
  nonempty_isUniversal := ⟨StructuredArrow.mkIdInitial⟩

variable (F₀) in
instance isRightKanExtensionId : F₀.IsRightKanExtension F₀.leftUnitor.hom where
  nonempty_isUniversal := ⟨CostructuredArrow.mkIdTerminal⟩

instance isLeftKanExtensionAlongEquivalence (α : F₀ ≅ L.functor ⋙ F₁) :
    F₁.IsLeftKanExtension α.hom := by
  refine ⟨⟨?_⟩⟩
  apply LeftExtension.isUniversalPostcomp₁Equiv
    (G := L.functor) L.functor.leftUnitor F₀ _|>.invFun
  refine IsInitial.ofUniqueHom
    (fun y ↦ StructuredArrow.homMk <| α.inv ≫ y.hom ≫ y.right.leftUnitor.hom) ?_
  intro y m
  ext x
  simpa using α.inv.app x ≫= congr_app m.w.symm x

instance isLeftKanExtensionAlongEquivalence' (L : C ⥤ D) (α : F₀ ⟶ L ⋙ F₁)
    [IsEquivalence L] [IsIso α] :
    F₁.IsLeftKanExtension α :=
  inferInstanceAs <|
    F₁.IsLeftKanExtension (asIso α : F₀ ≅ (asEquivalence L).functor ⋙ F₁).hom

instance isRightKanExtensionAlongEquivalence (α : L.functor ⋙ F₁ ≅ F₀) :
    F₁.IsRightKanExtension α.hom := by
  refine ⟨⟨?_⟩⟩
  apply RightExtension.isUniversalPostcomp₁Equiv
    (G := L.functor) L.functor.leftUnitor F₀ _|>.invFun
  refine IsTerminal.ofUniqueHom
    (fun y ↦ CostructuredArrow.homMk <| y.left.leftUnitor.inv ≫ y.hom ≫ α.inv) ?_
  intro y m
  ext x
  simpa using congr_app m.w x =≫ α.inv.app x

instance isRightKanExtensionAlongEquivalence' (L : C ⥤ D) (α : L ⋙ F₁ ⟶ F₀)
    [IsEquivalence L] [IsIso α] :
    F₁.IsRightKanExtension α :=
  inferInstanceAs <|
    F₁.IsRightKanExtension (asIso α : (asEquivalence L).functor ⋙ F₁ ≅ F₀).hom

end

end Functor

end CategoryTheory
