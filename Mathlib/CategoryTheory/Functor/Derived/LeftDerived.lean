/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Left derived functors

In this file, given a functor `F : C ⥤ H`, and `L : C ⥤ D` that is a
localization functor for `W : MorphismProperty C`, we define
`F.totalLeftDerived L W : D ⥤ H` as the right Kan extension of `F`
along `L`: it is defined if the type class `F.HasLeftDerivedFunctor W`
asserting the existence of a right Kan extension is satisfied.
(The name `totalLeftDerived` is to avoid name-collision with
`Functor.leftDerived` which are the left derived functors in
the context of abelian categories.)

Given `LF : D ⥤ H` and `α : L ⋙ LF ⟶ F`, we also introduce a type class
`LF.IsLeftDerivedFunctor α W` saying that `α` is a right Kan extension of `F`
along the localization functor `L`.

(This file was obtained by dualizing the results in the file
`Mathlib.CategoryTheory.Functor.Derived.RightDerived`.)

## References

* https://ncatlab.org/nlab/show/derived+functor

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C C' D D' H H' : Type _} [Category* C] [Category* C']
  [Category* D] [Category* D'] [Category* H] [Category* H']
  (LF'' LF' LF : D ⥤ H) {F F' F'' : C ⥤ H} (e : F ≅ F') {L : C ⥤ D}
  (α'' : L ⋙ LF'' ⟶ F'') (α' : L ⋙ LF' ⟶ F') (α : L ⋙ LF ⟶ F) (α'₂ : L ⋙ LF' ⟶ F)
  (W : MorphismProperty C)

/-- A functor `LF : D ⥤ H` is a left derived functor of `F : C ⥤ H`
if it is equipped with a natural transformation `α : L ⋙ LF ⟶ F`
which makes it a right Kan extension of `F` along `L`,
where `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`. -/
class IsLeftDerivedFunctor (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
    (W : MorphismProperty C) [L.IsLocalization W] : Prop where
  isRightKanExtension (LF α) : LF.IsRightKanExtension α

lemma isLeftDerivedFunctor_iff_isRightKanExtension [L.IsLocalization W] :
    LF.IsLeftDerivedFunctor α W ↔ LF.IsRightKanExtension α := by
  constructor
  · exact fun _ => IsLeftDerivedFunctor.isRightKanExtension LF α W
  · exact fun h => ⟨h⟩

variable {RF RF'} in
lemma isLeftDerivedFunctor_iff_of_iso (α' : L ⋙ LF' ⟶ F) (W : MorphismProperty C)
    [L.IsLocalization W] (e : LF ≅ LF') (comm : whiskerLeft L e.hom ≫ α' = α) :
    LF.IsLeftDerivedFunctor α W ↔ LF'.IsLeftDerivedFunctor α' W := by
  simp only [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_iff_of_iso e _ _ comm

section

variable [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]

/-- Constructor for natural transformations to a left derived functor. -/
noncomputable def leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension α G β

@[reassoc (attr := simp)]
lemma leftDerived_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (LF.leftDerivedLift α W G β) ≫ α = β :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac α G β

@[reassoc (attr := simp)]
lemma leftDerived_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) :
    (LF.leftDerivedLift α W G β).app (L.obj X) ≫ α.app X = β.app X :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.liftOfIsRightKanExtension_fac_app α G β X

include W in
lemma leftDerived_ext (G : D ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  LF.hom_ext_of_isRightKanExtension α γ₁ γ₂ hγ

/-- The natural transformation `LF' ⟶ LF` on left derived functors that is
induced by a natural transformation `F' ⟶ F`. -/
noncomputable def leftDerivedNatTrans (τ : F' ⟶ F) : LF' ⟶ LF :=
  LF.leftDerivedLift α W LF' (α' ≫ τ)

@[reassoc (attr := simp)]
lemma leftDerivedNatTrans_fac (τ : F' ⟶ F) :
    whiskerLeft L (leftDerivedNatTrans LF' LF α' α W τ) ≫ α = α' ≫ τ := by
  dsimp only [leftDerivedNatTrans]
  simp

@[reassoc (attr := simp)]
lemma leftDerivedNatTrans_app (τ : F' ⟶ F) (X : C) :
    (leftDerivedNatTrans LF' LF α' α W τ).app (L.obj X) ≫ α.app X =
    α'.app X ≫ τ.app X := by
  dsimp only [leftDerivedNatTrans]
  simp

@[simp]
lemma leftDerivedNatTrans_id :
    leftDerivedNatTrans LF LF α α W (𝟙 F) = 𝟙 LF :=
  leftDerived_ext LF α W _ _ _ (by simp)

variable [LF'.IsLeftDerivedFunctor α' W]

@[reassoc (attr := simp)]
lemma leftDerivedNatTrans_comp (τ' : F'' ⟶ F') (τ : F' ⟶ F) :
    leftDerivedNatTrans LF'' LF' α'' α' W τ' ≫ leftDerivedNatTrans LF' LF α' α W τ =
    leftDerivedNatTrans LF'' LF α'' α W (τ' ≫ τ) :=
  leftDerived_ext LF α W _ _ _ (by simp)

/-- The natural isomorphism `LF' ≅ LF` on left derived functors that is
induced by a natural isomorphism `F' ≅ F`. -/
@[simps]
noncomputable def leftDerivedNatIso (τ : F' ≅ F) :
    LF' ≅ LF where
  hom := leftDerivedNatTrans LF' LF α' α W τ.hom
  inv := leftDerivedNatTrans LF LF' α α' W τ.inv

/-- Uniqueness (up to a natural isomorphism) of the left derived functor. -/
noncomputable abbrev leftDerivedUnique [LF'.IsLeftDerivedFunctor α'₂ W] : LF ≅ LF' :=
  leftDerivedNatIso LF LF' α α'₂ W (Iso.refl F)

lemma isLeftDerivedFunctor_iff_isIso_leftDerivedLift (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    G.IsLeftDerivedFunctor β W ↔ IsIso (LF.leftDerivedLift α W G β) := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  have := IsLeftDerivedFunctor.isRightKanExtension _ α W
  exact isRightKanExtension_iff_isIso _ α _ (by simp)

end

variable (F)

/-- A functor `F : C ⥤ H` has a left derived functor with respect to
`W : MorphismProperty C` if it has a right Kan extension along
`W.Q : C ⥤ W.Localization` (or any localization functor `L : C ⥤ D`
for `W`, see `hasLeftDerivedFunctor_iff`). -/
class HasLeftDerivedFunctor : Prop where
  hasRightKanExtension' : HasRightKanExtension W.Q F

variable (L)
variable [L.IsLocalization W]

lemma hasLeftDerivedFunctor_iff :
    F.HasLeftDerivedFunctor W ↔ HasRightKanExtension L F := by
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasRightExtension_iff_postcomp₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

include e in
lemma hasLeftDerivedFunctor_iff_of_iso :
    HasLeftDerivedFunctor F W ↔ HasLeftDerivedFunctor F' W := by
  rw [hasLeftDerivedFunctor_iff F W.Q W, hasLeftDerivedFunctor_iff F' W.Q W,
    hasRightExtension_iff_of_iso₂ W.Q e]

variable (F)

lemma HasLeftDerivedFunctor.hasRightKanExtension [HasLeftDerivedFunctor F W] :
    HasRightKanExtension L F := by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

variable {F L W}

lemma HasLeftDerivedFunctor.mk' [LF.IsLeftDerivedFunctor α W] :
    HasLeftDerivedFunctor F W := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk LF α

section

variable (F) [F.HasLeftDerivedFunctor W] (L W)

/-- Given a functor `F : C ⥤ H`, and a localization functor `L : C ⥤ D` for `W`,
this is the left derived functor `D ⥤ H` of `F`, i.e. the right Kan extension
of `F` along `L`. -/
noncomputable def totalLeftDerived : D ⥤ H :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

/-- The canonical natural transformation `L ⋙ F.totalLeftDerived L W ⟶ F`. -/
noncomputable def totalLeftDerivedCounit : L ⋙ F.totalLeftDerived L W ⟶ F :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

instance : (F.totalLeftDerived L W).IsLeftDerivedFunctor
    (F.totalLeftDerivedCounit L W) W where
  isRightKanExtension := by
    dsimp [totalLeftDerived, totalLeftDerivedCounit]
    infer_instance

end

end Functor

end CategoryTheory
