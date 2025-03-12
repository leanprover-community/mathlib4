/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Whiskering

/-!
# Joins of category

Given categories `C, D`, this file constructs a category `C ⋆ D`.... -- TODO
-/

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory


/-- Elements of `Join C D` are either elements of `C` or elements of `D`. -/
-- Impl. : We are not defining it as a type alias for `C ⊕ D` so that we can have
-- aesop to call cases on `Join C D`
inductive Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type (max u₁ u₂)
  | left : C → Join C D
  | right : D → Join C D

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Join

@[inherit_doc] infixr:30 " ⋆ " => Join

namespace Join

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

variable {C D}

/-- Morphisms in `C ⋆ D` are those of `C` and `D`, plus an unique
morphism `(left c ⟶ right d)` for every `c : C` and `d : D`. -/
@[simp]
def Hom : C ⋆ D → C ⋆ D → Type (max v₁ v₂)
  | .left x, .left y => ULift (x ⟶ y)
  | .right x, .right y => ULift (x ⟶ y)
  | .left _, .right _ => PUnit
  | .right _, .left _ => PEmpty
attribute [nolint simpNF] Hom.eq_3

/-- Identity morphisms in `C ⋆ D` are inherited from those in `C` and `D`. -/
@[simp]
def id : ∀ (X : C ⋆ D), Hom X X
  | .left x => ULift.up (𝟙 x)
  | .right x => ULift.up (𝟙 x)

/-- Composition in `C ⋆ D` is inherited from the compositions in `C` and `D`. -/
@[simp]
def comp : ∀ {x y z : C ⋆ D}, Hom x y → Hom y z → Hom x z
  | .left _x, .left _y, .left _z => fun f g ↦ ULift.up (ULift.down f ≫ ULift.down g)
  | .left _x, .left _y, .right _z => fun _ _ ↦ PUnit.unit
  | .left _x, .right _y, .left _z => fun _ g ↦ PEmpty.elim g
  | .left _x, .right _y, .right _z => fun _ _ ↦ PUnit.unit
  | .right _x, .left _y, .left _z => fun f _ ↦ PEmpty.elim f
  | .right _x, .left _y, .right _z => fun f _ ↦ PEmpty.elim f
  | .right _x, .right _y, .left _z => fun _ g ↦ PEmpty.elim g
  | .right _x, .right _y, .right _z => fun f g ↦ ULift.up (ULift.down f ≫ ULift.down g)

instance : Category.{max v₁ v₂} (C ⋆ D) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, id, comp, Category.assoc] <;>
    tauto

@[aesop safe destruct (rule_sets := [CategoryTheory])]
lemma false_of_right_to_left {X : D} {Y : C} (f : right X ⟶ left Y) : False := (f : PEmpty).elim

instance {X : C} {Y : D} : Unique (left X ⟶ right Y) := inferInstanceAs (Unique PUnit)

namespace Hom

/-- Get back a morphism `X ⟶ Y` in C from a morphism `left X ⟶ left Y` in `C ⋆ D`. -/
def downl {X Y : C} (f : (left X : C ⋆ D) ⟶ left Y) : X ⟶ Y := ULift.down f

/-- Get back a morphism `X ⟶ Y` in `D` from a morphism `right X ⟶ right Y` in `C ⋆ D`. -/
def downr {X Y : D} (f : (right X : C ⋆ D) ⟶ right Y) : X ⟶ Y := ULift.down f

/-- Construct a morphism `left X ⟶ left Y` in `C ⋆ D` from a morphism `X ⟶ Y` in C. -/
def upl {X Y : C} (f : X ⟶ Y) : (left X : C ⋆ D) ⟶ left Y := ULift.up f

/-- Construct a morphism `right X ⟶ right Y` in `C ⋆ D` from a morphism `X ⟶ Y` in D. -/
def upr {X Y : D} (f : X ⟶ Y) : (right X : C ⋆ D) ⟶ right Y := ULift.up f

@[simp]
lemma downl_upl {X Y : C} (f : X ⟶ Y) : downl (upl f : (_ : C ⋆ D) ⟶ _) = f := rfl

@[simp]
lemma downr_upr {X Y : D} (f : X ⟶ Y) : downr (upr f : (_ : C ⋆ D) ⟶ _) = f := rfl

@[simp]
lemma upl_downl {X Y : C} (f : (left X : C ⋆ D) ⟶ left Y) : upl (downl f) = f := rfl

@[simp]
lemma upr_downr {X Y : D} (f : (right X : C ⋆ D) ⟶ right Y) : upr (downr f) = f := rfl

@[simp]
lemma downl_comp {X Y Z : C} (f : (left X : C ⋆ D) ⟶ left Y) (g : (left Y : C ⋆ D) ⟶ left Z) :
    downl (f ≫ g) = downl f ≫ downl g :=
  rfl

@[simp]
lemma downr_comp {X Y Z : D} (f : (right X : C ⋆ D) ⟶ right Y) (g : (right Y : C ⋆ D) ⟶ right Z) :
    downr (f ≫ g) = downr f ≫ downr g :=
  rfl

@[simp]
lemma upl_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upl (f ≫ g) : (_ : C ⋆ D) ⟶ _) = upl f ≫ upl g :=
  rfl

@[simp]
lemma upr_comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upr (f ≫ g) : (_ : C ⋆ D) ⟶ _) = upr f ≫ upr g :=
  rfl

@[simp]
lemma upl_id {X : C} : (upl (𝟙 X) : (_ : C ⋆ D) ⟶ _) = 𝟙 (left X) := rfl

@[simp]
lemma upr_id {X : D} : (upr (𝟙 X) : (_ : C ⋆ D) ⟶ _) = 𝟙 (right X) := rfl

@[simp]
lemma downl_id {X : C} : downl (𝟙 (left X : C ⋆ D)) = 𝟙 X := rfl

@[simp]
lemma downr_id {X : D} : downr (𝟙 (right X : C ⋆ D)) = 𝟙 X := rfl

end Hom

/-- The canonical inclusion from C to `C ⋆ D`. -/
@[simps]
def inclLeft : C ⥤ C ⋆ D where
  obj := left
  map := Hom.upl

/-- The canonical inclusion from D to `C ⋆ D`. -/
@[simps]
def inclRight : D ⥤ C ⋆ D where
  obj := right
  map := Hom.upr

instance : (inclLeft : C ⥤ C ⋆ D).Full where
  map_surjective f := ⟨Hom.downl f, rfl⟩

instance : (inclRight : D ⥤ C ⋆ D).Full where
  map_surjective f := ⟨Hom.downr f, rfl⟩

instance : (inclLeft : C ⥤ C ⋆ D).Faithful where
  map_injective {_ _} _ _ h := congrArg (fun k ↦ Hom.downl k) h

instance : (inclRight : D ⥤ C ⋆ D).Faithful where
  map_injective {_ _} _ _ h := congrArg (fun k ↦ Hom.downr k) h

section Functoriality

variable {E : Type u₃} [Category.{v₃} E] (Fₗ : C ⥤ E)
  {E' : Type u₄} [Category.{v₄} E'] (Fᵣ : D ⥤ E')

/-- A functor (C ⥤ E) induces a functor (C ⋆ D ⥤ E ⋆ D). -/
@[simps!]
def mapLeft : (C ⋆ D) ⥤ (E ⋆ D) where
  obj X :=
    match X with
    | .left x => left (Fₗ.obj x)
    | .right x => right x
  map {X Y} f :=
    match X, Y, f with
    | .left x, .left y, f => Hom.upl <| Fₗ.map <| Hom.downl f
    | .right x, .right y, f => Hom.upr <| Hom.downr f
    | .left _, .right _, _ => PUnit.unit

/-- A functor (D ⥤ E') induces a functor (C ⋆ D ⥤ C ⋆ E'). -/
@[simps!]
def mapRight : (C ⋆ D) ⥤ (C ⋆ E') where
  obj X :=
    match X with
    | .left x => left x
    | .right x => right (Fᵣ.obj x)
  map {X Y} f :=
    match X, Y, f with
    | .left x, .left y, f => Hom.upl <| Hom.downl f
    | .right x, .right y, f => Hom.upr <| Fᵣ.map <| Hom.downr f
    | .left _, .right _, _ => PUnit.unit

/-- A pair of functors ((C ⥤ E), (D ⥤ E')) induces a functor (C ⋆ D ⥤ E ⋆ E'). -/
@[simps!]
def mapPair : (C ⋆ D) ⥤ (E ⋆ E') where
  obj X :=
    match X with
    | .left x => left (Fₗ.obj x)
    | .right x => right (Fᵣ.obj x)
  map {X Y} f :=
    match X, Y, f with
    | .left x, .left y, f => Hom.upl <| Fₗ.map <| Hom.downl f
    | .right x, .right y, f => Hom.upr <| Fᵣ.map <| Hom.downr f
    | .left _, .right _, _ => PUnit.unit

/-- We can decompose mapPair as first `mapLeft`, then `mapRight`. -/
@[simps!]
def mapPairIsoMapLeftCompMapRight : mapPair Fₗ Fᵣ ≅ mapLeft Fₗ ⋙ mapRight Fᵣ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- We can decompose `mapPair` as first mapRight, then `mapLeft`. -/
@[simps!]
def mapPairIsoMapRightCompMapLeft : mapPair Fₗ Fᵣ ≅ mapRight Fᵣ ⋙ mapLeft Fₗ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapLeft` respects the identity functors. -/
@[simps!]
def mapLeftId : mapLeft (𝟭 C) ≅ 𝟭 (C ⋆ D) :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapRight` respects the identity functors. -/
@[simps!]
def mapRightId : mapRight (𝟭 D) ≅ 𝟭 (C ⋆ D) :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapPair F (𝟭 D)` is naturally isomorphic to `mapLeft F`. -/
@[simps!]
def mapPairIdRight : mapPair Fₗ (𝟭 D) ≅ mapLeft Fₗ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapPair (𝟭 C) F` is naturally isomorphic to `mapLeft R`. -/
@[simps!]
def mapPairIdLeft : mapPair (𝟭 C) Fᵣ ≅ mapRight Fᵣ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapPair` respects identities. -/
@[simps!]
def mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D) :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- Coherence of the previous isomorphims. -/
@[simp]
lemma mapPairId_coherence_left :
    (mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)) = mapPairIdLeft (𝟭 D) ≪≫ mapLeftId := by
  aesop_cat

/-- Coherence of the previous isomorphims. -/
@[simp]
lemma mapPairId_coherence_right :
    (mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)) = mapPairIdRight (𝟭 C) ≪≫ mapRightId := by
  aesop_cat

@[simp]
lemma mapPairIsoMapLeftCompMapRight_coherence_id :
    mapPairIsoMapLeftCompMapRight (𝟭 C) (𝟭 D) ≪≫
      (isoWhiskerLeft (mapLeft _) mapRightId) ≪≫ (isoWhiskerRight mapLeftId _) ≪≫
      (Functor.leftUnitor _) =
    (mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)) := by
  aesop_cat

@[simp]
lemma mapPairIsoMapRightCompMapLeft_coherence_id :
    mapPairIsoMapRightCompMapLeft (𝟭 C) (𝟭 D) ≪≫
      (isoWhiskerLeft (mapRight _) mapLeftId) ≪≫ (isoWhiskerRight mapLeftId _) ≪≫
      (Functor.leftUnitor _) =
    (mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)) := by
  aesop_cat

variable {J : Type u₅} [Category.{v₅} J] (Gₗ : E ⥤ J)
  {J' : Type u₆} [Category.{v₆} J'] (Gᵣ : E' ⥤ J')

/-- `mapLeft` respects functor composition. -/
@[simps!]
def mapLeftComp : (mapLeft (Fₗ ⋙ Gₗ) : C ⋆ D ⥤ J ⋆ D) ≅ mapLeft Fₗ ⋙ mapLeft Gₗ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapRight` respects functor composition. -/
@[simps!]
def mapRightComp : (mapRight (Fᵣ ⋙ Gᵣ) : C ⋆ D ⥤ C ⋆ J') ≅ mapRight Fᵣ ⋙ mapRight Gᵣ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

/-- `mapRight` respects functor composition. -/
@[simps!]
def mapPairComp : (mapPair (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) : C ⋆ D ⥤ J ⋆ J') ≅ mapPair Fₗ Fᵣ ⋙ mapPair Gₗ Gᵣ :=
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

@[simps!]
def mapPairComp_coherence_left :
    mapPairComp Fₗ Fᵣ Gₗ Gᵣ = mapPairIsoMapLeftCompMapRight (Fₗ ≫ Gₗ) (Fᵣ ≫ Gᵣ) ≪≫ 
      (isoWhiskerLeft (mapRight _) (mapLeftComp _ _)) ≪≫ (isoWhiskerRight mapLeftId _) := by
  NatIso.ofComponents (fun X ↦ match X with
    | left _ => Iso.refl _
    | right _ => Iso.refl _)

end Functoriality

end Join


end CategoryTheory
