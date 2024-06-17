/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
#align_import category_theory.with_terminal from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!

# `WithInitial` and `WithTerminal`

Given a category `C`, this file constructs two objects:
1. `WithTerminal C`, the category built from `C` by formally adjoining a terminal object.
2. `WithInitial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `WithTerminal.star` resp. `WithInitial.star`, and
the proofs that these are terminal resp. initial are in `WithTerminal.star_terminal`
and `WithInitial.star_initial`.

The inclusion from `C` into `WithTerminal C` resp. `WithInitial C` is denoted
`WithTerminal.incl` resp. `WithInitial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `WithTerminal C` resp. `WithInitial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `inclLift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `liftUnique` provides the uniqueness property of `lift`.

In addition to this, we provide `WithTerminal.map` and `WithInitial.map` providing the
functoriality of these constructions with respect to functors on the base categories.

We define corresponding pseudofunctors `WithTerminal.pseudofunctor` and `WithInitial.pseudofunctor`
from `Cat` to `Cat`.

-/


namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
inductive WithTerminal : Type u
  | of : C → WithTerminal
  | star : WithTerminal
  deriving Inhabited
#align category_theory.with_terminal CategoryTheory.WithTerminal

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithTerminal

/-- Formally adjoin an initial object to a category. -/
inductive WithInitial : Type u
  | of : C → WithInitial
  | star : WithInitial
  deriving Inhabited
#align category_theory.with_initial CategoryTheory.WithInitial

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithInitial

namespace WithTerminal

variable {C}

/-- Morphisms for `WithTerminal C`. -/
-- Porting note(#5171): removed `nolint has_nonempty_instance`
@[simp]
def Hom : WithTerminal C → WithTerminal C → Type v
  | of X, of Y => X ⟶ Y
  | star, of _ => PEmpty
  | _, star => PUnit
#align category_theory.with_terminal.hom CategoryTheory.WithTerminal.Hom

/-- Identity morphisms for `WithTerminal C`. -/
@[simp]
def id : ∀ X : WithTerminal C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit
#align category_theory.with_terminal.id CategoryTheory.WithTerminal.id

/-- Composition of morphisms for `WithTerminal C`. -/
@[simp]
def comp : ∀ {X Y Z : WithTerminal C}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | of _X, _, star => fun _f _g => PUnit.unit
  | star, of _X, _ => fun f _g => PEmpty.elim f
  | _, star, of _Y => fun _f g => PEmpty.elim g
  | star, star, star => fun _ _ => PUnit.unit
#align category_theory.with_terminal.comp CategoryTheory.WithTerminal.comp

instance : Category.{v} (WithTerminal C) where
  Hom X Y := Hom X Y
  id X := id _
  comp := comp
  assoc {a b c d} f g h := by
    -- Porting note: it would be nice to automate this away as well.
    -- I tried splitting this into separate `Quiver` and `Category` instances,
    -- so the `false_of_from_star` destruct rule below can be used here.
    -- That works, but causes mysterious failures of `aesop_cat` in `map`.
    cases a <;> cases b <;> cases c <;> cases d <;> try aesop_cat
    · exact (h : PEmpty).elim
    · exact (g : PEmpty).elim
    · exact (h : PEmpty).elim

/-- Helper function for typechecking. -/
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f

@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl

@[aesop safe destruct (rule_sets := [CategoryTheory])]
lemma false_of_from_star {X : C} (f : star ⟶ of X) : False := (f : PEmpty).elim

/-- The inclusion from `C` into `WithTerminal C`. -/
def incl : C ⥤ WithTerminal C where
  obj := of
  map f := f
#align category_theory.with_terminal.incl CategoryTheory.WithTerminal.incl

instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩

instance : (incl : C ⥤ _).Faithful where

/-- Map `WithTerminal` with respect to a functor `F : C ⥤ D`. -/
@[simps]
def map {D : Type*} [Category D] (F : C ⥤ D) : WithTerminal C ⥤ WithTerminal D where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of x, of y, f => F.map (down f)
    | of _, star, _ => PUnit.unit
    | star, star, _ => PUnit.unit
#align category_theory.with_terminal.map CategoryTheory.WithTerminal.map

/-- A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithTerminal C)`. -/
@[simps!]
def mapId (C : Type*) [Category C] : map (𝟭 C) ≅ 𝟭 (WithTerminal C) :=
  NatIso.ofComponents (fun X => match X with
    | of x => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)

/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
def mapComp {D E : Type*} [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of x => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)

/-- From a natural transformation of functors `C ⥤ D`, the induced natural transformation
of functors `WithTerminal C ⥤ WithTerminal D`. -/
@[simps]
def map₂ {D : Type*} [Category D] {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | of x, star, _ => rfl
    | star, star, _ => rfl

/-- The pseudofunctor from `Cat` to `Cat` defined with `WithTerminal`. -/
@[simps]
def pseudofunctor : Pseudofunctor Cat Cat where
  obj C := Cat.of (WithTerminal C)
  map := map
  map₂ := map₂
  mapId C := mapId C
  mapComp := mapComp
  map₂_id := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
  map₂_comp := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
  map₂_whisker_left := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, map₂, mapComp_hom_app, Iso.refl_hom,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_whisker_right := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, map₂, mapComp_hom_app, Iso.refl_hom,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_associator := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, map₂, Bicategory.Strict.associator_eqToIso,
        eqToIso_refl, Iso.refl_hom, mapComp_hom_app, mapComp_inv_app, Iso.refl_inv,
        Category.comp_id, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Bicategory.whiskerRight, whiskerRight_app, mapComp_hom_app,
        Iso.refl_hom, down_id, Functor.map_id, Bicategory.whiskerLeft, whiskerLeft_app,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id]
    · rfl
  map₂_left_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, Cat.id_map, map₂,
        Bicategory.Strict.leftUnitor_eqToIso, eqToIso_refl, Iso.refl_hom, mapComp_hom_app,
        Bicategory.whiskerRight, whiskerRight_app, mapId_hom_app, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
  map₂_right_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, Cat.id_map, map₂,
        Bicategory.Strict.rightUnitor_eqToIso, eqToIso_refl, Iso.refl_hom, mapComp_hom_app,
        Bicategory.whiskerLeft, whiskerLeft_app, mapId_hom_app, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl

instance {X : WithTerminal C} : Unique (X ⟶ star) where
  default :=
    match X with
    | of _ => PUnit.unit
    | star => PUnit.unit
  uniq := by aesop_cat

/-- `WithTerminal.star` is terminal. -/
def starTerminal : Limits.IsTerminal (star : WithTerminal C) :=
  Limits.IsTerminal.ofUnique _
#align category_theory.with_terminal.star_terminal CategoryTheory.WithTerminal.starTerminal

/-- Lift a functor `F : C ⥤ D` to `WithTerminal C ⥤ D`. -/
@[simps]
def lift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : WithTerminal C ⥤ D where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of x, of y, f => F.map (down f)
    | of x, star, _ => M x
    | star, star, _ => 𝟙 Z
#align category_theory.with_terminal.lift CategoryTheory.WithTerminal.lift

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps!]
def inclLift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.with_terminal.incl_lift CategoryTheory.WithTerminal.inclLift

/-- The isomorphism between `(lift F _ _).obj WithTerminal.star` with `Z`. -/
@[simps!]
def liftStar {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl
#align category_theory.with_terminal.lift_star CategoryTheory.WithTerminal.liftStar

theorem lift_map_liftStar {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
    (lift F M hM).map (starTerminal.from (incl.obj x)) ≫ (liftStar F M hM).hom =
      (inclLift F M hM).hom.app x ≫ M x := by
  erw [Category.id_comp, Category.comp_id]
  rfl
#align category_theory.with_terminal.lift_map_lift_star CategoryTheory.WithTerminal.lift_map_liftStar

/-- The uniqueness of `lift`. -/
@[simp]
def liftUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, F.obj x ⟶ Z)
    (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, G.map (starTerminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) :
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
@[simps!]
def liftToTerminal {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    WithTerminal C ⥤ D :=
  lift F (fun _x => hZ.from _) fun _x _y _f => hZ.hom_ext _ _
#align category_theory.with_terminal.lift_to_terminal CategoryTheory.WithTerminal.liftToTerminal

/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps!]
def inclLiftToTerminal {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z) :
    incl ⋙ liftToTerminal F hZ ≅ F :=
  inclLift _ _ _
#align category_theory.with_terminal.incl_lift_to_terminal CategoryTheory.WithTerminal.inclLiftToTerminal

/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps!]
def liftToTerminalUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsTerminal Z)
    (G : WithTerminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToTerminal F hZ :=
  liftUnique F (fun _z => hZ.from _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x =>
    hZ.hom_ext _ _
#align category_theory.with_terminal.lift_to_terminal_unique CategoryTheory.WithTerminal.liftToTerminalUnique

/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
def homFrom (X : C) : incl.obj X ⟶ star :=
  starTerminal.from _
#align category_theory.with_terminal.hom_from CategoryTheory.WithTerminal.homFrom

instance isIso_of_from_star {X : WithTerminal C} (f : star ⟶ X) : IsIso f :=
  match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩
#align category_theory.with_terminal.is_iso_of_from_star CategoryTheory.WithTerminal.isIso_of_from_star

end WithTerminal

namespace WithInitial

variable {C}

/-- Morphisms for `WithInitial C`. -/
-- Porting note(#5171): removed `nolint has_nonempty_instance`
@[simp]
def Hom : WithInitial C → WithInitial C → Type v
  | of X, of Y => X ⟶ Y
  | of _, _ => PEmpty
  | star, _ => PUnit
#align category_theory.with_initial.hom CategoryTheory.WithInitial.Hom

/-- Identity morphisms for `WithInitial C`. -/
@[simp]
def id : ∀ X : WithInitial C, Hom X X
  | of _ => 𝟙 _
  | star => PUnit.unit
#align category_theory.with_initial.id CategoryTheory.WithInitial.id

/-- Composition of morphisms for `WithInitial C`. -/
@[simp]
def comp : ∀ {X Y Z : WithInitial C}, Hom X Y → Hom Y Z → Hom X Z
  | of _X, of _Y, of _Z => fun f g => f ≫ g
  | star, _, of _X => fun _f _g => PUnit.unit
  | _, of _X, star => fun _f g => PEmpty.elim g
  | of _Y, star, _ => fun f _g => PEmpty.elim f
  | star, star, star => fun _ _ => PUnit.unit
#align category_theory.with_initial.comp CategoryTheory.WithInitial.comp

instance : Category.{v} (WithInitial C) where
  Hom X Y := Hom X Y
  id X := id X
  comp f g := comp f g
  assoc {a b c d} f g h := by
    -- Porting note: it would be nice to automate this away as well.
    -- See the note on `Category (WithTerminal C)`
    cases a <;> cases b <;> cases c <;> cases d <;> try aesop_cat
    · exact (g : PEmpty).elim
    · exact (f : PEmpty).elim
    · exact (f : PEmpty).elim

/-- Helper function for typechecking. -/
def down {X Y : C} (f : of X ⟶ of Y) : X ⟶ Y := f

@[simp] lemma down_id {X : C} : down (𝟙 (of X)) = 𝟙 X := rfl
@[simp] lemma down_comp {X Y Z : C} (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    down (f ≫ g) = down f ≫ down g :=
  rfl

@[aesop safe destruct (rule_sets := [CategoryTheory])]
lemma false_of_to_star {X : C} (f : of X ⟶ star) : False := (f : PEmpty).elim

/-- The inclusion of `C` into `WithInitial C`. -/
def incl : C ⥤ WithInitial C where
  obj := of
  map f := f
#align category_theory.with_initial.incl CategoryTheory.WithInitial.incl

instance : (incl : C ⥤ _).Full where
  map_surjective f := ⟨f, rfl⟩

instance : (incl : C ⥤ _).Faithful where

/-- Map `WithInitial` with respect to a functor `F : C ⥤ D`. -/
@[simps]
def map {D : Type*} [Category D] (F : C ⥤ D) : WithInitial C ⥤ WithInitial D where
  obj X :=
    match X with
    | of x => of <| F.obj x
    | star => star
  map {X Y} f :=
    match X, Y, f with
    | of x, of y, f => F.map (down f)
    | star, of _, _ => PUnit.unit
    | star, star, _ => PUnit.unit

#align category_theory.with_initial.map CategoryTheory.WithInitial.map

/-- A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithInitial C)`. -/
@[simps!]
def mapId (C : Type*) [Category C] : map (𝟭 C) ≅ 𝟭 (WithInitial C) :=
  NatIso.ofComponents (fun X => match X with
    | of x => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)

/-- A natural isomorphism between the functor `map (F ⋙ G) ` and `map F ⋙ map G `. -/
@[simps!]
def mapComp {D E : Type*} [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents (fun X => match X with
    | of x => Iso.refl _
    | star => Iso.refl _) (by aesop_cat)

/-- From a natrual transformation of functors `C ⥤ D`, the induced natural transformation
of functors `WithInitial C ⥤ WithInitial D`. -/
@[simps]
def map₂ {D : Type*} [Category D] {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := fun X => match X with
    | of x => η.app x
    | star => 𝟙 star
  naturality := by
    intro X Y f
    match X, Y, f with
    | of x, of y, f => exact η.naturality f
    | star, of x, _ => rfl
    | star, star, _ => rfl

/-- The pseudofunctor from `Cat` to `Cat` defined with `WithInitial`. -/
@[simps]
def pseudofunctor : Pseudofunctor Cat Cat where
  obj C := Cat.of (WithInitial C)
  map := map
  map₂ := map₂
  mapId C := mapId C
  mapComp := mapComp
  map₂_id := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
  map₂_comp := by
    intros
    apply NatTrans.ext
    funext X
    cases X <;> rfl
  map₂_whisker_left := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, map₂, mapComp_hom_app, Iso.refl_hom,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_whisker_right := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, map₂, mapComp_hom_app, Iso.refl_hom,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_associator := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, map₂, Bicategory.Strict.associator_eqToIso,
        eqToIso_refl, Iso.refl_hom, mapComp_hom_app, mapComp_inv_app, Iso.refl_inv,
        Category.comp_id, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Bicategory.whiskerRight, whiskerRight_app, mapComp_hom_app,
        Iso.refl_hom, down_id, Functor.map_id, Bicategory.whiskerLeft, whiskerLeft_app,
        mapComp_inv_app, Iso.refl_inv, Category.comp_id]
    · rfl
  map₂_left_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, Cat.id_map, map₂,
        Bicategory.Strict.leftUnitor_eqToIso, eqToIso_refl, Iso.refl_hom, mapComp_hom_app,
        Bicategory.whiskerRight, whiskerRight_app, mapId_hom_app, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
  map₂_right_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [map, Cat.comp_obj, Cat.comp_map, Cat.id_map, map₂,
        Bicategory.Strict.rightUnitor_eqToIso, eqToIso_refl, Iso.refl_hom, mapComp_hom_app,
        Bicategory.whiskerLeft, whiskerLeft_app, mapId_hom_app, Category.id_comp]
      rw [NatTrans.id_app, NatTrans.id_app]
      simp only [Cat.comp_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl

instance {X : WithInitial C} : Unique (star ⟶ X) where
  default :=
    match X with
    | of _x => PUnit.unit
    | star => PUnit.unit
  uniq := by aesop_cat

/-- `WithInitial.star` is initial. -/
def starInitial : Limits.IsInitial (star : WithInitial C) :=
  Limits.IsInitial.ofUnique _
#align category_theory.with_initial.star_initial CategoryTheory.WithInitial.starInitial

/-- Lift a functor `F : C ⥤ D` to `WithInitial C ⥤ D`. -/
@[simps]
def lift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : WithInitial C ⥤ D where
  obj X :=
    match X with
    | of x => F.obj x
    | star => Z
  map {X Y} f :=
    match X, Y, f with
    | of x, of y, f => F.map (down f)
    | star, of x, _ => M _
    | star, star, _ => 𝟙 _
#align category_theory.with_initial.lift CategoryTheory.WithInitial.lift

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps!]
def inclLift {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : incl ⋙ lift F M hM ≅ F where
  hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.with_initial.incl_lift CategoryTheory.WithInitial.inclLift

/-- The isomorphism between `(lift F _ _).obj WithInitial.star` with `Z`. -/
@[simps!]
def liftStar {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) : (lift F M hM).obj star ≅ Z :=
  eqToIso rfl
#align category_theory.with_initial.lift_star CategoryTheory.WithInitial.liftStar

theorem liftStar_lift_map {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
    (liftStar F M hM).hom ≫ (lift F M hM).map (starInitial.to (incl.obj x)) =
      M x ≫ (inclLift F M hM).hom.app x := by
  erw [Category.id_comp, Category.comp_id]
  rfl
#align category_theory.with_initial.lift_star_lift_map CategoryTheory.WithInitial.liftStar_lift_map

/-- The uniqueness of `lift`. -/
@[simp]
def liftUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (M : ∀ x : C, Z ⟶ F.obj x)
    (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F)
    (hG : G.obj star ≅ Z)
    (hh : ∀ x : C, hG.symm.hom ≫ G.map (starInitial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) :
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
        erw [← Iso.eq_inv_comp, ← Category.assoc, hh]
        simp
      · cases f
        change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _
        simp)
#align category_theory.with_initial.lift_unique CategoryTheory.WithInitial.liftUnique

/-- A variant of `lift` with `Z` an initial object. -/
@[simps!]
def liftToInitial {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    WithInitial C ⥤ D :=
  lift F (fun _x => hZ.to _) fun _x _y _f => hZ.hom_ext _ _
#align category_theory.with_initial.lift_to_initial CategoryTheory.WithInitial.liftToInitial

/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps!]
def inclLiftToInitial {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z) :
    incl ⋙ liftToInitial F hZ ≅ F :=
  inclLift _ _ _
#align category_theory.with_initial.incl_lift_to_initial CategoryTheory.WithInitial.inclLiftToInitial

/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps!]
def liftToInitialUnique {D : Type*} [Category D] {Z : D} (F : C ⥤ D) (hZ : Limits.IsInitial Z)
    (G : WithInitial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ liftToInitial F hZ :=
  liftUnique F (fun _z => hZ.to _) (fun _x _y _f => hZ.hom_ext _ _) G h hG fun _x => hZ.hom_ext _ _
#align category_theory.with_initial.lift_to_initial_unique CategoryTheory.WithInitial.liftToInitialUnique

/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
def homTo (X : C) : star ⟶ incl.obj X :=
  starInitial.to _
#align category_theory.with_initial.hom_to CategoryTheory.WithInitial.homTo

-- Porting note: need to do cases analysis
instance isIso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f :=
  match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩
#align category_theory.with_initial.is_iso_of_to_star CategoryTheory.WithInitial.isIso_of_to_star

end WithInitial

end CategoryTheory
