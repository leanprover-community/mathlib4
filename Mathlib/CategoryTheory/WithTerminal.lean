/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.with_terminal
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!

# `with_initial` and `with_terminal`

Given a category `C`, this file constructs two objects:
1. `with_terminal C`, the category built from `C` by formally adjoining a terminal object.
2. `with_initial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `with_terminal.star` resp. `with_initial.star`, and
the proofs that these are terminal resp. initial are in `with_terminal.star_terminal`
and `with_initial.star_initial`.

The inclusion from `C` intro `with_terminal C` resp. `with_initial C` is denoted
`with_terminal.incl` resp. `with_initial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `with_terminal C` resp. `with_initial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `incl_lift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `lift_unique` provides the uniqueness property of `lift`.

In addition to this, we provide `with_terminal.map` and `with_initinal.map` providing the
functoriality of these constructions with respect to functors on the base categories.

-/


namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
inductive WithTerminal : Type u
  | of : C → with_terminal
  | star : with_terminal
  deriving Inhabited
#align category_theory.with_terminal CategoryTheory.WithTerminal

/-- Formally adjoin an initial object to a category. -/
inductive WithInitial : Type u
  | of : C → with_initial
  | star : with_initial
  deriving Inhabited
#align category_theory.with_initial CategoryTheory.WithInitial

namespace WithTerminal

attribute [local tidy] tactic.case_bash

variable {C}

/- warning: category_theory.with_terminal.hom -> CategoryTheory.WithTerminal.Hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], (CategoryTheory.WithTerminal.{u1, u2} C _inst_1) -> (CategoryTheory.WithTerminal.{u1, u2} C _inst_1) -> Type.{u1}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], (CategoryTheory.WithTerminal.{u2, u1} C _inst_1) -> (CategoryTheory.WithTerminal.{u2, u1} C _inst_1) -> Type.{u2}
Case conversion may be inaccurate. Consider using '#align category_theory.with_terminal.hom CategoryTheory.WithTerminal.Homₓ'. -/
/-- Morphisms for `with_terminal C`. -/
@[simp, nolint has_nonempty_instance]
def Hom : WithTerminal C → WithTerminal C → Type v
  | of X, of Y => X ⟶ Y
  | star, of X => PEmpty
  | _, star => PUnit
#align category_theory.with_terminal.hom CategoryTheory.WithTerminal.Hom

/- warning: category_theory.with_terminal.id -> CategoryTheory.WithTerminal.id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.WithTerminal.{u1, u2} C _inst_1), CategoryTheory.WithTerminal.Hom.{u1, u2} C _inst_1 X X
but is expected to have type
  PUnit.{max (succ (succ u1)) (succ (succ u2))}
Case conversion may be inaccurate. Consider using '#align category_theory.with_terminal.id CategoryTheory.WithTerminal.idₓ'. -/
/-- Identity morphisms for `with_terminal C`. -/
@[simp]
def id : ∀ X : WithTerminal C, Hom X X
  | of X => 𝟙 _
  | star => PUnit.unit
#align category_theory.with_terminal.id CategoryTheory.WithTerminal.id

/- warning: category_theory.with_terminal.comp -> CategoryTheory.WithTerminal.comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : CategoryTheory.WithTerminal.{u1, u2} C _inst_1} {Y : CategoryTheory.WithTerminal.{u1, u2} C _inst_1} {Z : CategoryTheory.WithTerminal.{u1, u2} C _inst_1}, (CategoryTheory.WithTerminal.Hom.{u1, u2} C _inst_1 X Y) -> (CategoryTheory.WithTerminal.Hom.{u1, u2} C _inst_1 Y Z) -> (CategoryTheory.WithTerminal.Hom.{u1, u2} C _inst_1 X Z)
but is expected to have type
  PUnit.{max (succ (succ u1)) (succ (succ u2))}
Case conversion may be inaccurate. Consider using '#align category_theory.with_terminal.comp CategoryTheory.WithTerminal.compₓ'. -/
/-- Composition of morphisms for `with_terminal C`. -/
@[simp]
def comp : ∀ {X Y Z : WithTerminal C}, Hom X Y → Hom Y Z → Hom X Z
  | of X, of Y, of Z => fun f g => f ≫ g
  | of X, _, star => fun f g => PUnit.unit
  | star, of X, _ => fun f g => PEmpty.elim f
  | _, star, of Y => fun f g => PEmpty.elim g
  | star, star, star => fun _ _ => PUnit.unit
#align category_theory.with_terminal.comp CategoryTheory.WithTerminal.comp

instance : Category.{v} (WithTerminal C)
    where
  Hom X Y := Hom X Y
  id X := id _
  comp X Y Z f g := comp f g

/-- The inclusion from `C` into `with_terminal C`. -/
def incl : C ⥤ WithTerminal C where
  obj := of
  map X Y f := f
#align category_theory.with_terminal.incl CategoryTheory.WithTerminal.incl

instance : Full (incl : C ⥤ _) where preimage X Y f := f

instance : Faithful (incl : C ⥤ _) where

/-- Map `with_terminal` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type _} [Category D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal D
    where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map X Y f :=
    match X, Y, f with
    | of x, of y, f => F.map f
    | of x, star, PUnit.unit => PUnit.unit
    | star, star, PUnit.unit => PUnit.unit
#align category_theory.with_terminal.map CategoryTheory.WithTerminal.map

instance {X : WithTerminal C} : Unique (X ⟶ star)
    where
  default :=
    match X with
    | of x => PUnit.unit
    | star => PUnit.unit
  uniq := by tidy

/-- `with_terminal.star` is terminal. -/
def starTerminal : Limits.IsTerminal (star : WithTerminal C) :=
  Limits.IsTerminal.ofUnique _
#align category_theory.with_terminal.star_terminal CategoryTheory.WithTerminal.starTerminal

/-- Lift a functor `F : C ⥤ D` to `with_term C ⥤ D`. -/
@[simps]
def lift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal C ⥤ D
    where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map X Y f :=
    match X, Y, f with
    | of x, of y, f => F.map f
    | of x, star, PUnit.unit => M x
    | star, star, PUnit.unit => 𝟙 Z
#align category_theory.with_terminal.lift CategoryTheory.WithTerminal.lift

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def inclLift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F
    where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.with_terminal.incl_lift CategoryTheory.WithTerminal.inclLift

/-- The isomorphism between `(lift F _ _).obj with_terminal.star` with `Z`. -/
@[simps]
def liftStar {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl
#align category_theory.with_terminal.lift_star CategoryTheory.WithTerminal.liftStar

theorem lift_map_liftStar {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).Hom =
      (inclLift F M hM).Hom.app x ≫ M x :=
  by
  erw [category.id_comp, category.comp_id]
  rfl
#align category_theory.with_terminal.lift_map_lift_star CategoryTheory.WithTerminal.lift_map_liftStar

/-- The uniqueness of `lift`. -/
@[simp]
def liftUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.Hom = h.Hom.app x ≫ M x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
      · cases f
        exact hh _
      · cases f
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)
#align category_theory.with_terminal.lift_unique CategoryTheory.WithTerminal.liftUnique

/-- A variant of `lift` with `Z` a terminal object. -/
@[simps]
def liftToTerminal {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    WithTerminal C ⥤ D :=
  lift F (fun x => hZ.from _) fun x y f => hZ.hom_ext _ _
#align category_theory.with_terminal.lift_to_terminal CategoryTheory.WithTerminal.liftToTerminal

/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps]
def inclLiftToTerminal {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    incl ⋙ liftToTerminal F hZ ≅ F :=
  inclLift _ _ _
#align category_theory.with_terminal.incl_lift_to_terminal CategoryTheory.WithTerminal.inclLiftToTerminal

/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps]
def liftToTerminalUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToTerminal F hZ :=
  liftUnique F (fun z => hZ.from _) (fun x y f => hZ.hom_ext _ _) G h hG fun x => hZ.hom_ext _ _
#align category_theory.with_terminal.lift_to_terminal_unique CategoryTheory.WithTerminal.liftToTerminalUnique

/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
def homFrom (X : C) : incl.obj X ⟶ star :=
  starTerminal.from _
#align category_theory.with_terminal.hom_from CategoryTheory.WithTerminal.homFrom

instance isIso_of_from_star {X : WithTerminal C} (f : star ⟶ X) : IsIso f := by tidy
#align category_theory.with_terminal.is_iso_of_from_star CategoryTheory.WithTerminal.isIso_of_from_star

end WithTerminal

namespace WithInitial

attribute [local tidy] tactic.case_bash

variable {C}

/- warning: category_theory.with_initial.hom -> CategoryTheory.WithInitial.Hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C], (CategoryTheory.WithInitial.{u1, u2} C _inst_1) -> (CategoryTheory.WithInitial.{u1, u2} C _inst_1) -> Type.{u1}
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C], (CategoryTheory.WithInitial.{u2, u1} C _inst_1) -> (CategoryTheory.WithInitial.{u2, u1} C _inst_1) -> Type.{u2}
Case conversion may be inaccurate. Consider using '#align category_theory.with_initial.hom CategoryTheory.WithInitial.Homₓ'. -/
/-- Morphisms for `with_initial C`. -/
@[simp, nolint has_nonempty_instance]
def Hom : WithInitial C → WithInitial C → Type v
  | of X, of Y => X ⟶ Y
  | of X, _ => PEmpty
  | star, _ => PUnit
#align category_theory.with_initial.hom CategoryTheory.WithInitial.Hom

/- warning: category_theory.with_initial.id -> CategoryTheory.WithInitial.id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.WithInitial.{u1, u2} C _inst_1), CategoryTheory.WithInitial.Hom.{u1, u2} C _inst_1 X X
but is expected to have type
  PUnit.{max (succ (succ u1)) (succ (succ u2))}
Case conversion may be inaccurate. Consider using '#align category_theory.with_initial.id CategoryTheory.WithInitial.idₓ'. -/
/-- Identity morphisms for `with_initial C`. -/
@[simp]
def id : ∀ X : WithInitial C, Hom X X
  | of X => 𝟙 _
  | star => PUnit.unit
#align category_theory.with_initial.id CategoryTheory.WithInitial.id

/- warning: category_theory.with_initial.comp -> CategoryTheory.WithInitial.comp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : CategoryTheory.WithInitial.{u1, u2} C _inst_1} {Y : CategoryTheory.WithInitial.{u1, u2} C _inst_1} {Z : CategoryTheory.WithInitial.{u1, u2} C _inst_1}, (CategoryTheory.WithInitial.Hom.{u1, u2} C _inst_1 X Y) -> (CategoryTheory.WithInitial.Hom.{u1, u2} C _inst_1 Y Z) -> (CategoryTheory.WithInitial.Hom.{u1, u2} C _inst_1 X Z)
but is expected to have type
  PUnit.{max (succ (succ u1)) (succ (succ u2))}
Case conversion may be inaccurate. Consider using '#align category_theory.with_initial.comp CategoryTheory.WithInitial.compₓ'. -/
/-- Composition of morphisms for `with_initial C`. -/
@[simp]
def comp : ∀ {X Y Z : WithInitial C}, Hom X Y → Hom Y Z → Hom X Z
  | of X, of Y, of Z => fun f g => f ≫ g
  | star, _, of X => fun f g => PUnit.unit
  | _, of X, star => fun f g => PEmpty.elim g
  | of Y, star, _ => fun f g => PEmpty.elim f
  | star, star, star => fun _ _ => PUnit.unit
#align category_theory.with_initial.comp CategoryTheory.WithInitial.comp

instance : Category.{v} (WithInitial C)
    where
  Hom X Y := Hom X Y
  id X := id _
  comp X Y Z f g := comp f g

/-- The inclusion of `C` into `with_initial C`. -/
def incl : C ⥤ WithInitial C where
  obj := of
  map X Y f := f
#align category_theory.with_initial.incl CategoryTheory.WithInitial.incl

instance : Full (incl : C ⥤ _) where preimage X Y f := f

instance : Faithful (incl : C ⥤ _) where

/-- Map `with_initial` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type _} [Category D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D
    where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map X Y f :=
    match X, Y, f with
    | of x, of y, f => F.map f
    | star, of x, PUnit.unit => PUnit.unit
    | star, star, PUnit.unit => PUnit.unit
#align category_theory.with_initial.map CategoryTheory.WithInitial.map

instance {X : WithInitial C} : Unique (star ⟶ X)
    where
  default :=
    match X with
    | of x => PUnit.unit
    | star => PUnit.unit
  uniq := by tidy

/-- `with_initial.star` is initial. -/
def starInitial : Limits.IsInitial (star : WithInitial C) :=
  Limits.IsInitial.ofUnique _
#align category_theory.with_initial.star_initial CategoryTheory.WithInitial.starInitial

/-- Lift a functor `F : C ⥤ D` to `with_initial C ⥤ D`. -/
@[simps]
def lift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial C ⥤ D
    where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map X Y f :=
    match X, Y, f with
    | of x, of y, f => F.map f
    | star, of x, PUnit.unit => M _
    | star, star, PUnit.unit => 𝟙 _
#align category_theory.with_initial.lift CategoryTheory.WithInitial.lift

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def inclLift {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F
    where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.with_initial.incl_lift CategoryTheory.WithInitial.inclLift

/-- The isomorphism between `(lift F _ _).obj with_term.star` with `Z`. -/
@[simps]
def liftStar {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl
#align category_theory.with_initial.lift_star CategoryTheory.WithInitial.liftStar

theorem liftStar_lift_map {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
    (liftStar F M hM).Hom ≫ (lift F M hM).map (starInitial.to (incl.obj x)) =
      M x ≫ (inclLift F M hM).Hom.app x :=
  by
  erw [category.id_comp, category.comp_id]
  rfl
#align category_theory.with_initial.lift_star_lift_map CategoryTheory.WithInitial.liftStar_lift_map

/-- The uniqueness of `lift`. -/
@[simp]
def liftUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, hG.symm.Hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.Hom.app x) :
    G ≅ lift F M hM :=
  NatIso.ofComponents
    (fun X =>
      match X with
      | of x => h.app x
      | star => hG)
    (by
      rintro (X | X) (Y | Y) f
      · apply h.hom.naturality
      · cases f
      · cases f
        change G.map _ ≫ h.hom.app _ = hG.hom ≫ _
        symm
        erw [← iso.eq_inv_comp, ← category.assoc, hh]
        simpa
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)
#align category_theory.with_initial.lift_unique CategoryTheory.WithInitial.liftUnique

/-- A variant of `lift` with `Z` an initial object. -/
@[simps]
def liftToInitial {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    WithInitial C ⥤ D :=
  lift F (fun x => hZ.to _) fun x y f => hZ.hom_ext _ _
#align category_theory.with_initial.lift_to_initial CategoryTheory.WithInitial.liftToInitial

/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps]
def inclLiftToInitial {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    incl ⋙ liftToInitial F hZ ≅ F :=
  inclLift _ _ _
#align category_theory.with_initial.incl_lift_to_initial CategoryTheory.WithInitial.inclLiftToInitial

/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps]
def liftToInitialUnique {D : Type _} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToInitial F hZ :=
  liftUnique F (fun z => hZ.to _) (fun x y f => hZ.hom_ext _ _) G h hG fun x => hZ.hom_ext _ _
#align category_theory.with_initial.lift_to_initial_unique CategoryTheory.WithInitial.liftToInitialUnique

/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
def homTo (X : C) : star ⟶ incl.obj X :=
  starInitial.to _
#align category_theory.with_initial.hom_to CategoryTheory.WithInitial.homTo

instance isIso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f := by tidy
#align category_theory.with_initial.is_iso_of_to_star CategoryTheory.WithInitial.isIso_of_to_star

end WithInitial

end CategoryTheory

