/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Bicategory.Functor
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
We define `WithTerminal.mapNatTrans` and `WithInitial.mapNatTrans` which map natural transformations
with respect to theses constructions.

The maps `WithTerminal.map` and `WithTerminal.mapNatTrans` are combined into a functor
`WithTerminal.mapFunc` and `WithInitial.map` and `WithInitial.mapNatTrans` are combined into the
functor `WitInitial.mapFunc`.

Given an equivalence `C≌D` we provide an equivalance  `WithTerminal C ≌ WithTerminal D` and
`WithInitial C ≌ WithInitial D`.

We provide an equivalence between:
- `WithTerminal C⥤ D` and the comma category `Comma (𝟭 (C ⥤ D)) (Functor.const C)`
- `WithInitial C⥤ D` and the comma category `Comma (Functor.const C) (𝟭 (C ⥤ D))`
- `WithTerminal Cᵒᵖ` and `(WithInitial C)ᵒᵖ`
- `WithInitial Cᵒᵖ` and `(WithTerminal C)ᵒᵖ`


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

attribute [local aesop safe cases (rule_sets [CategoryTheory])] WithTerminal

/-- Formally adjoin an initial object to a category. -/
inductive WithInitial : Type u
  | of : C → WithInitial
  | star : WithInitial
  deriving Inhabited
#align category_theory.with_initial CategoryTheory.WithInitial

attribute [local aesop safe cases (rule_sets [CategoryTheory])] WithInitial

namespace WithTerminal

variable {C}

/-- Morphisms for `WithTerminal C`. -/
-- porting note: unsupported `nolint has_nonempty_instance`
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

@[aesop safe destruct (rule_sets [CategoryTheory])]
lemma false_of_from_star {X : C} (f : star ⟶ of X) : False := (f : PEmpty).elim

/-- The inclusion from `C` into `WithTerminal C`. -/
def incl : C ⥤ WithTerminal C where
  obj := of
  map f := f
#align category_theory.with_terminal.incl CategoryTheory.WithTerminal.incl

instance : Full (incl : C ⥤ _) where
  preimage f := f

instance : Faithful (incl : C ⥤ _) where

/-- Map `WithTerminal` with respect to a functor `F : C ⥤ D`. -/
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

/--A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithTerminal C)`.-/
def mapId  (C : Type*) [Category C] : map (𝟭 C) ≅ 𝟭 (WithTerminal C) where
  hom := {app  := fun X =>  eqToHom (by cases X <;> rfl)}
  inv := {app  := fun X =>  eqToHom (by cases X <;> rfl)}

/--A natural isomorphism between the functor `map (F⋙G) ` and `map F ⋙ map G `.-/
def mapComp {D : Type*} [Category D] {E : Type*} [Category E] (F : C⥤ D) (G:D⥤ E) :
    map (F⋙G) ≅ map F ⋙ map G where
  hom := {app := fun X =>  eqToHom (by cases X <;> rfl)}
  inv := {app  := fun X =>  eqToHom (by cases X <;> rfl)}

/--From a natrual transformation of functors `C⥤D`, the induced natural transformation
of functors `WithTerminal C ⥤ WithTerminal D`. -/
def map₂  {D : Type*} [Category D]  {F G: C ⥤ D} (η : F ⟶ G) :
    map F ⟶ map G where
  app := fun X =>
        match X with
        | of x => η.app x
        | star => 𝟙 (star)
  naturality := by
          intro X Y f
          match X, Y, f with
          | of x, of y, f => exact η.naturality f
          | of x, star, _ => rfl
          | star, star, _ => rfl

/-- The pseudofunctor from `Cat` to `Cat` defined with `WithTerminal`.-/
def pseudofunctor: Pseudofunctor Cat Cat where
  obj C :=Cat.of (WithTerminal C)
  map {C D} F := map F
  map₂ := map₂
  mapId C := mapId C
  mapComp {C D E} F G  := mapComp F G
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
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold mapComp map  map₂
      simp only [Cat.comp_obj, Cat.comp_map, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_whisker_right := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold mapComp map  map₂
      simp only [Cat.comp_obj, Cat.comp_map, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_associator := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app]
      simp only [Bicategory.Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, Cat.comp_obj]
      unfold map₂ mapComp map
      rw [NatTrans.id_app,NatTrans.id_app]
      simp only [Cat.comp_obj, Cat.comp_map, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Bicategory.whiskerRight, whiskerRight_app, down_id, Functor.map_id, Bicategory.whiskerLeft,
        whiskerLeft_app, Category.comp_id, Category.id_comp]
    · rfl
  map₂_left_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold map₂ mapComp mapId map
      simp only [Cat.comp_obj, Cat.comp_map, Cat.id_map, Bicategory.Strict.leftUnitor_eqToIso,
        eqToIso_refl, Iso.refl_hom, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Bicategory.whiskerRight, Functor.id_obj, Functor.id_map, whiskerRight_app, Category.id_comp]
      rw [NatTrans.id_app,NatTrans.id_app]
      simp only [Cat.comp_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
  map₂_right_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold map₂ mapComp mapId map
      simp [Bicategory.whiskerLeft]
      rw [NatTrans.id_app,NatTrans.id_app]
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


/--From `WithTerminal C ⥤ D`, an object in the comma category defined by the functors `𝟭 (C ⥤ D)`
and `(Functor.const C)`. -/
def commaFromFunc {D : Type*} [Category D]  (G : WithTerminal C ⥤ D) :
    Comma (𝟭 (C ⥤ D)) (Functor.const C) where
  left  := incl ⋙ G
  right :=G.obj star
  hom := {
    app :=  fun x => G.map (starTerminal.from (incl.obj x))
    naturality := by
     simp_all only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map, ←
       G.map_comp, Limits.IsTerminal.comp_from, Functor.const_obj_map, Category.comp_id,
       implies_true]
     }

/--Form an object in the comma category defined by the functors `𝟭 (C ⥤ D)`
and `(Functor.const C)`, a functor `WithTerminal C ⥤ D`. -/
def funcFromComma {D : Type*} [Category D]
    (η : Comma (𝟭 (C ⥤ D)) (Functor.const C) )  : WithTerminal C ⥤ D :=by
  refine lift η.left (fun x => η.hom.app x) ?_
  simp only [NatTrans.naturality, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
    implies_true]

/--The function `commaFromFunc` is left-inverse to `commaFromFunc` -/
theorem funcFromComma_comp_commaFromFunc {D : Type*} [Category D]
    (η : Comma (𝟭 (C ⥤ D)) (Functor.const C) ):
    commaFromFunc (funcFromComma η) = η := by
  constructor

/--The function `commaFromFunc` is right-inverse to `commaFromFunc` -/
theorem commFromFunc_comp_funcFromComma {D : Type*} [Category D]
    (G : WithTerminal C ⥤ D):
    funcFromComma (commaFromFunc G) = G := by
  apply Functor.ext
  · intro X Y f
    match X, Y, f with
    | of x, of y, f => simp only [Functor.id_obj, eqToHom_refl, Category.comp_id, Category.id_comp]
                       rfl
    | of x, star, x_1 => simp only [Functor.id_obj, eqToHom_refl, Category.comp_id,
                               Category.id_comp]
                         rfl
    | star, star, x => simp only [Functor.id_obj, eqToHom_refl, Category.comp_id, Category.id_comp]
                       exact (G.map_id star).symm
  · intro X
    match X with
    | of x => rfl
    | star => rfl

/--From a natural transformation of functors `WithTerminal C ⥤ D`, a morphism in the comma category
 defined by the functors `𝟭 (C ⥤ D)` and `(Functor.const C)`-/
def commHomFromNatTrans {D : Type*} [Category D]  {G1 G2 : WithTerminal C ⥤ D} (η: G1 ⟶ G2) :
    commaFromFunc G1 ⟶ commaFromFunc G2 where
  left := whiskerLeft incl η
  right := η.app star
  w := by
     apply NatTrans.ext
     funext
     simp only [commaFromFunc, Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
       Functor.id_map, NatTrans.comp_app, whiskerLeft_app, Functor.const_map_app,
       NatTrans.naturality]

/--From a morphism in the comma category defined by the functors `𝟭 (C ⥤ D)` and
`(Functor.const C)`, a natural transformation of functors `WithTerminal C ⥤ D`,-/
def natTransFromCommaHom {D : Type*} [Category D]  {c1 c2: Comma (𝟭 (C ⥤ D)) (Functor.const C)}
    (η :c1⟶c2) :   funcFromComma c1 ⟶ funcFromComma c2 where
  app X :=  match X with
            | of x => η.left.app x
            | star => η.right
  naturality := by
      intro X Y f
      let h:= η.w
      match X, Y, f with
      | of x, of y, f => simp only [funcFromComma, Functor.id_obj, lift_obj, lift_map,
                           NatTrans.naturality]
      | of x, star, x_1 => simp only [Functor.id_obj, Functor.id_map] at h
                           change _=(η.left ≫ c2.hom).app x
                           rw [h]
                           rfl
      | star, star, _ => simp only [funcFromComma, Functor.id_obj, lift_obj, lift_map,
        Category.id_comp, Category.comp_id]

/--An equivalence of categoryes between the catgory of functors `(WithTerminal C ⥤ D)` and
the comma category `Comma (𝟭 (C ⥤ D)) (Functor.const C)`.-/
def equivToComma  {D : Type*} [Category D] :
    (WithTerminal C ⥤ D) ≌  Comma (𝟭 (C ⥤ D)) (Functor.const C) :=
  Equivalence.mk
    ({ obj := commaFromFunc, map := commHomFromNatTrans})
    ({ obj := funcFromComma, map := natTransFromCommaHom})
    ({ hom := {app := fun G =>  eqToHom (commFromFunc_comp_funcFromComma G).symm}
       inv := {app := fun G =>  eqToHom (commFromFunc_comp_funcFromComma G) } })
    ({ hom := {app := fun G =>  eqToHom (funcFromComma_comp_commaFromFunc G)}
       inv := {app := fun G =>  eqToHom (funcFromComma_comp_commaFromFunc G).symm }})


/--From a natrual transformation of functors `C⥤D`, the induced natural transformation
of functors `WithTerminal C⥤ WithTerminal D` -/
def mapNatTrans  {D : Type*} [Category D]  {F G: C ⥤ D} (η : F ⟶ G) :
    map F ⟶ map G where
  app := fun X =>
        match X with
        | of x => η.app x
        | star => 𝟙 (star)
  naturality := by
          intro X Y f
          match X, Y, f with
          | of x, of y, f => exact η.naturality f
          | of x, star, _ => rfl
          | star, star, _ => rfl

/--The functor taking `C⥤D` to `WithTerminal C ⥤ WithTerminal D`.-/
def mapFunc  {D : Type*} [Category D]  : (C⥤D)⥤ (WithTerminal C ⥤ WithTerminal D) where
  obj:= map
  map:= mapNatTrans

/--The extension of an equivalance `C ≌ D` to an equivalance `WithTerminal C ≌ WithTerminal D `.-/
def mapEquiv {D : Type*} [Category D]  (e: C ≌ D) : WithTerminal C ≌ WithTerminal D :=
  Equivalence.mk (map e.functor) (map e.inverse)
   ((eqToIso (map_id C).symm).trans
 ((Functor.mapIso mapFunc e.unitIso).trans
  (eqToIso (map_comp e.functor e.inverse))))
    ( (eqToIso (map_comp e.inverse e.functor).symm).trans
          ((Functor.mapIso mapFunc e.counitIso).trans (eqToIso (map_id D))))



end WithTerminal



namespace WithInitial

variable {C}

/-- Morphisms for `WithInitial C`. -/
-- porting note: unsupported `nolint has_nonempty_instance`
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

@[aesop safe destruct (rule_sets [CategoryTheory])]
lemma false_of_to_star {X : C} (f : of X ⟶ star) : False := (f : PEmpty).elim

/-- The inclusion of `C` into `WithInitial C`. -/
def incl : C ⥤ WithInitial C where
  obj := of
  map f := f
#align category_theory.with_initial.incl CategoryTheory.WithInitial.incl

instance : Full (incl : C ⥤ _) where
  preimage f := f

instance : Faithful (incl : C ⥤ _) where

/-- Map `WithInitial` with respect to a functor `F : C ⥤ D`. -/
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

/--A natural isomorphism between the functor `map (𝟭 C)` and `𝟭 (WithInitial C)`.-/
def mapId  (C : Type*) [Category C] : map (𝟭 C) ≅ 𝟭 (WithInitial C) where
  hom := {app  := fun X =>  eqToHom (by cases X <;> rfl)}
  inv := {app  := fun X =>  eqToHom (by cases X <;> rfl)}

/--A natural isomorphism between the functor `map (F⋙G) ` and `map F ⋙ map G `.-/
def mapComp {D : Type*} [Category D] {E : Type*} [Category E] (F : C⥤ D) (G:D⥤ E) :
    map (F⋙G) ≅ map F ⋙ map G where
  hom := {app := fun X =>  eqToHom (by cases X <;> rfl)}
  inv := {app  := fun X =>  eqToHom (by cases X <;> rfl)}

/--From a natrual transformation of functors `C⥤D`, the induced natural transformation
of functors `WithInitial C ⥤ WithInitial D`. -/
def map₂  {D : Type*} [Category D]  {F G: C ⥤ D} (η : F ⟶ G) :
    map F ⟶ map G where
  app := fun X =>
        match X with
        | of x => η.app x
        | star => 𝟙 (star)
  naturality := by
          intro X Y f
          match X, Y, f with
          | of x, of y, f => exact η.naturality f
          | star, of x, _ => rfl
          | star, star, _ => rfl

/-- The pseudofunctor from `Cat` to `Cat` defined with `WithInitial`.-/
def pseudofunctor: Pseudofunctor Cat Cat where
  obj C :=Cat.of (WithInitial C)
  map {C D} F := map F
  map₂ := map₂
  mapId C := mapId C
  mapComp {C D E} F G  := mapComp F G
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
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold mapComp map  map₂
      simp only [Cat.comp_obj, Cat.comp_map, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_whisker_right := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold mapComp map  map₂
      simp only [Cat.comp_obj, Cat.comp_map, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      rfl
    · rfl
  map₂_associator := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app,NatTrans.comp_app]
      simp only [Bicategory.Strict.associator_eqToIso, eqToIso_refl, Iso.refl_hom, Cat.comp_obj]
      unfold map₂ mapComp map
      rw [NatTrans.id_app,NatTrans.id_app]
      simp only [Cat.comp_obj, Cat.comp_map, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Bicategory.whiskerRight, whiskerRight_app, down_id, Functor.map_id, Bicategory.whiskerLeft,
        whiskerLeft_app, Category.comp_id, Category.id_comp]
    · rfl
  map₂_left_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold map₂ mapComp mapId map
      simp only [Cat.comp_obj, Cat.comp_map, Cat.id_map, Bicategory.Strict.leftUnitor_eqToIso,
        eqToIso_refl, Iso.refl_hom, Functor.comp_obj, Functor.comp_map, eqToHom_refl,
        Bicategory.whiskerRight, Functor.id_obj, Functor.id_map, whiskerRight_app, Category.id_comp]
      rw [NatTrans.id_app,NatTrans.id_app]
      simp only [Cat.comp_obj, Category.comp_id]
      rw [← Functor.map_id]
      rfl
    · rfl
  map₂_right_unitor := by
    intros
    apply NatTrans.ext
    funext X
    cases X
    · rw [NatTrans.comp_app,NatTrans.comp_app]
      unfold map₂ mapComp mapId map
      simp [Bicategory.whiskerLeft]
      rw [NatTrans.id_app,NatTrans.id_app]
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

-- Porting note : need to do cases analysis
instance isIso_of_to_star {X : WithInitial C} (f : X ⟶ star) : IsIso f :=
  match X with
  | of _X => f.elim
  | star => ⟨f, rfl, rfl⟩
#align category_theory.with_initial.is_iso_of_to_star CategoryTheory.WithInitial.isIso_of_to_star

/--From `WithInitial C ⥤ D`, an object in the comma category defined by the functors
 `(Functor.const C)` and `𝟭 (C ⥤ D)`. -/
def commaFromFunc {D : Type*} [Category D]  (G : WithInitial C ⥤ D) :
    Comma (Functor.const C) (𝟭 (C ⥤ D))  where
  left  := G.obj star
  right :=incl ⋙ G
  hom := {
    app :=  fun x => G.map (starInitial.to (incl.obj x))
    naturality := by
     simp only [Functor.const_obj_obj, Functor.id_obj, Functor.comp_obj, Functor.const_obj_map,
       Category.id_comp, Functor.comp_map, ← G.map_comp, Limits.IsInitial.to_comp, implies_true]
     }

/--Form an object in the comma category defined by the functors
 `(Functor.const C)` and `𝟭 (C ⥤ D)`, a functor `WithInitial C ⥤ D`. -/
def funcFromComma {D : Type*} [Category D]
    (η : Comma (Functor.const C)  (𝟭 (C ⥤ D)) )  : WithInitial C ⥤ D :=by
  refine lift η.right (fun x => η.hom.app x) ?_
  intro x y f
  have h:=η.hom.naturality f
  simp only [Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map, Category.id_comp] at h
  exact h.symm


/--The function `commaFromFunc` is left-inverse to `commaFromFunc` -/
theorem funcFromComma_comp_commaFromFunc {D : Type*} [Category D]
    (η : Comma  (Functor.const C) (𝟭 (C ⥤ D)) ):
    commaFromFunc (funcFromComma η) = η := by
  constructor

/--The function `commaFromFunc` is right-inverse to `commaFromFunc` -/
theorem commFromFunc_comp_funcFromComma {D : Type*} [Category D]
    (G : WithInitial C ⥤ D):
    funcFromComma (commaFromFunc G) = G := by
  apply Functor.ext
  · intro X Y f
    match X, Y, f with
    | of x, of y, f => simp only [Functor.id_obj, eqToHom_refl, Category.comp_id, Category.id_comp]
                       rfl
    | star, of y, x_1 => simp only [Functor.id_obj, eqToHom_refl, Category.comp_id,
                               Category.id_comp]
                         rfl
    | star, star, x => simp only [Functor.id_obj, eqToHom_refl, Category.comp_id, Category.id_comp]
                       exact (G.map_id star).symm
  · intro X
    match X with
    | of x => rfl
    | star => rfl

/--From a natural transformation of functors `WithInitial C ⥤ D`, a morphism in the comma category
 defined by the functors `(Functor.const C)` and `𝟭 (C ⥤ D)`-/
def commHomFromNatTrans {D : Type*} [Category D]  {G1 G2 : WithInitial C ⥤ D} (η: G1 ⟶ G2) :
    commaFromFunc G1 ⟶ commaFromFunc G2 where
  left := η.app star
  right := whiskerLeft incl η
  w := by
     apply NatTrans.ext
     funext
     simp only [commaFromFunc, Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj,
       Functor.id_map, NatTrans.comp_app, whiskerLeft_app, Functor.const_map_app,
       NatTrans.naturality]

/--From a morphism in the comma category defined by the functors
`(Functor.const C)` and `𝟭 (C ⥤ D)`, a natural transformation of functors `WithInitial C ⥤ D`.-/
def natTransFromCommaHom {D : Type*} [Category D]  {c1 c2: Comma (Functor.const C) (𝟭 (C ⥤ D)) }
    (η :c1⟶c2) :   funcFromComma c1 ⟶ funcFromComma c2 where
  app X :=  match X with
            | of x => η.right.app x
            | star => η.left
  naturality := by
      intro X Y f
      let h:= η.w
      match X, Y, f with
      | of x, of y, f => simp only [funcFromComma, Functor.id_obj, lift_obj, lift_map,
                           NatTrans.naturality]
      | star , of y, x_1 => simp only [Functor.id_obj, Functor.id_map] at h
                            change (c1.hom ≫ η.right ).app y=_
                            rw [← h]
                            rfl
      | star, star, _ => simp only [funcFromComma, Functor.id_obj, lift_obj, lift_map,
        Category.id_comp, Category.comp_id]

/--An equivalence of categoryes between the catgory of functors `(WithInitial C ⥤ D)` and
the comma category `Comma (Functor.const C) (𝟭 (C ⥤ D))`.-/
def equivToComma  {D : Type*} [Category D] :
    (WithInitial C ⥤ D) ≌  Comma (Functor.const C) (𝟭 (C ⥤ D)) :=
  Equivalence.mk
    ({ obj := commaFromFunc, map := commHomFromNatTrans})
    ({ obj := funcFromComma, map := natTransFromCommaHom})
    ({ hom := {app := fun G =>  eqToHom (commFromFunc_comp_funcFromComma G).symm}
       inv := {app := fun G =>  eqToHom (commFromFunc_comp_funcFromComma G) } })
    ({ hom := {app := fun G =>  eqToHom (funcFromComma_comp_commaFromFunc G)}
       inv := {app := fun G =>  eqToHom (funcFromComma_comp_commaFromFunc G).symm }})


end WithInitial
variable {C}
open Opposite

/--From an object in `WithTerminal C`, the corresponding object in `WithInitial Cᵒᵖ`-/
def WithTerminal.op' (X: WithTerminal C): WithInitial Cᵒᵖ :=
  match   X  with
  |  WithTerminal.of x =>  (WithInitial.of (Opposite.op x))
  |  WithTerminal.star =>  WithInitial.star

/--From an object in `WithInitial C`, the corresponding object in `WithTerminal Cᵒᵖ`-/
def WithInitial.op' (X: WithInitial C): WithTerminal Cᵒᵖ :=
  match   X  with
  |  WithInitial.of x =>  (WithTerminal.of (Opposite.op x))
  |  WithInitial.star =>  WithTerminal.star

/--From a morphism in `WithTerminal C`, the corresponding morphism in `WithInitial Cᵒᵖ`-/
def WithTerminal.homOp'   {X Y: WithTerminal C} (f : X ⟶ Y):
    WithTerminal.op' Y ⟶ WithTerminal.op'  X :=
  match X, Y, f  with
  | WithTerminal.of _, WithTerminal.of _, f' => (WithTerminal.down f').op
  | WithTerminal.of x,WithTerminal.star, _ =>
     (WithInitial.starInitial.to (WithInitial.of (Opposite.op x)))
  | WithTerminal.star, WithTerminal.star, _ => 𝟙 _

/--From a morphism in `WithInitial C`, the corresponding morphism in `WithTerminial Cᵒᵖ`-/
def WithInitial.homOp'   {X Y: WithInitial C} (f : X ⟶ Y):
    WithInitial.op' Y ⟶ WithInitial.op'  X :=
  match X, Y, f  with
  | WithInitial.of _, WithInitial.of _, f' => (WithTerminal.down f').op
  | WithInitial.star,WithInitial.of x, _ =>
     (WithTerminal.starTerminal.from (WithTerminal.of (Opposite.op x)))
  | WithInitial.star, WithInitial.star, _ => 𝟙 _

/--A functor from `(WithTerminal C)ᵒᵖ ` to `WithInitial Cᵒᵖ`.-/
def WithTerminal.op_to_op' : (WithTerminal C)ᵒᵖ ⥤ (WithInitial Cᵒᵖ) where
  obj X :=  WithTerminal.op' (unop X)
  map {X Y} f := WithTerminal.homOp' f.unop
  map_id :=by
     intro X
     cases X
     aesop_cat
  map_comp :=by
     intro X Y Z f g
     cases X; cases Y; cases Z; cases f; cases g;
     rename_i Xp Yp Zp fp gp
     rw [unop_op,unop_op] at fp gp
     aesop_cat

/--A functor from `(WithInitial C)ᵒᵖ ` to `WithTerminal Cᵒᵖ`.-/
def WithInitial.op_to_op' : (WithInitial C)ᵒᵖ ⥤ (WithTerminal Cᵒᵖ) where
  obj X :=  WithInitial.op' (unop X)
  map {X Y} f := WithInitial.homOp' f.unop
  map_id :=by
     intro X
     cases X
     aesop_cat
  map_comp :=by
     intro X Y Z f g
     cases X; cases Y; cases Z; cases f; cases g;
     rename_i Xp Yp Zp fp gp
     rw [unop_op,unop_op] at fp gp
     aesop_cat

/--A functor from `WithInitial Cᵒᵖ` to  `(WithTerminal C)ᵒᵖ `.-/
def WithTerminal.op'_to_op : (WithInitial Cᵒᵖ) ⥤ (WithTerminal C)ᵒᵖ   where
  obj X :=
    match  X  with
    |  WithInitial.of x =>  op (WithTerminal.of (unop x))
    |  WithInitial.star =>  op WithTerminal.star
  map {X Y} f :=
    match X, Y, f with
    | WithInitial.of _, WithInitial.of _, f' => f'
    | WithInitial.star, WithInitial.of x, _ =>
        (WithTerminal.starTerminal.from ((WithTerminal.of (unop x)))).op
    | WithInitial.star, WithInitial.star, _ => 𝟙 _

/--A functor from `WithTerminal Cᵒᵖ` to  `(WithInitial C)ᵒᵖ `.-/
def WithInitial.op'_to_op : (WithTerminal Cᵒᵖ) ⥤ (WithInitial C)ᵒᵖ   where
  obj X :=
    match  X  with
    |  WithTerminal.of x =>  op (WithInitial.of (unop x))
    |  WithTerminal.star =>  op WithInitial.star
  map {X Y} f :=
    match X, Y, f with
    | WithTerminal.of _, WithTerminal.of _, f' => f'
    | WithTerminal.of x,WithTerminal.star, _ =>
        (WithInitial.starInitial.to ((WithInitial.of (unop x)))).op
    | WithTerminal.star, WithTerminal.star, _ => 𝟙 _

/--An equivalance between the categories `WithInitial Cᵒᵖ` and  `(WithTerminal C)ᵒᵖ`.-/
def equivWithInitialOfOpWithTerminalOp (C : Type*) [Category C]:
    WithInitial Cᵒᵖ  ≌ (WithTerminal C)ᵒᵖ  where
  functor := WithTerminal.op'_to_op
  inverse := WithTerminal.op_to_op'
  unitIso := {
    hom := {app := fun X => eqToHom (by cases X <;> rfl)}
    inv := {app := fun X => eqToHom (by cases X <;> rfl) }
  }
  counitIso := {
    hom := {
      app := fun X => eqToHom (by cases X; rename_i X;  cases X  <;> rfl)
      naturality := by
          intro X Y f
          cases X; cases Y; cases f;
          rename_i Xp Yp fp
          cases Xp <;> cases Yp <;>
          simp only [Functor.id_obj, Functor.comp_obj, unop_op, Functor.id_map,
            eqToHom_refl, Category.comp_id, Functor.comp_map, Category.id_comp]
          any_goals rfl
          exact (WithTerminal.false_of_from_star fp).elim
    }
    inv := {
      app := fun X => eqToHom (by cases X; rename_i X;  cases X  <;> rfl)
      naturality := by
          intro X Y f
          cases X; cases Y; cases f;
          rename_i Xp Yp fp
          cases Xp <;> cases Yp <;>
          simp only [Functor.id_obj, Functor.comp_obj, unop_op, Functor.id_map,
            eqToHom_refl, Category.comp_id, Functor.comp_map, Category.id_comp]
          any_goals rfl
          exact (WithTerminal.false_of_from_star fp).elim
    }
  }

/--An equivalance between the categories `WithTerminal Cᵒᵖ` and  `(WithInitial C)ᵒᵖ`.-/
def equivWithTerminalOfOpWithInitialOp (C : Type*) [Category C]:
    WithTerminal Cᵒᵖ  ≌ (WithInitial C)ᵒᵖ  where
  functor := WithInitial.op'_to_op
  inverse := WithInitial.op_to_op'
  unitIso := {
    hom := {app := fun X => eqToHom (by cases X <;> rfl)}
    inv := {app := fun X => eqToHom (by cases X <;> rfl) }
  }
  counitIso := {
    hom := {
      app := fun X => eqToHom (by cases X; rename_i X;  cases X  <;> rfl)
      naturality := by
          intro X Y f
          cases X; cases Y; cases f;
          rename_i Xp Yp fp
          cases Xp <;> cases Yp <;>
          simp only [Functor.id_obj, Functor.comp_obj, unop_op, Functor.id_map,
            eqToHom_refl, Category.comp_id, Functor.comp_map, Category.id_comp]
          any_goals rfl
          exact (WithInitial.false_of_to_star fp).elim
    }
    inv := {
      app := fun X => eqToHom (by cases X; rename_i X;  cases X  <;> rfl)
      naturality := by
          intro X Y f
          cases X; cases Y; cases f;
          rename_i Xp Yp fp
          cases Xp <;> cases Yp <;>
          simp only [Functor.id_obj, Functor.comp_obj, unop_op, Functor.id_map,
            eqToHom_refl, Category.comp_id, Functor.comp_map, Category.id_comp]
          any_goals rfl
          exact (WithInitial.false_of_to_star fp).elim
    }
  }


end CategoryTheory
