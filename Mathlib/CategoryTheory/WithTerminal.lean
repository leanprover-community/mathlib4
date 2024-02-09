/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

#align_import category_theory.with_terminal from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!

# `WithInitial` and `WithTerminal`

Given a category `C`, this file constructs two objects:
1. `WithTerminal C`, the category built from `C` by formally adjoining a terminal object.
2. `WithInitial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `WithTerminal.star` resp. `WithInitial.star`, and
the proofs that these are terminal resp. initial are in `WithTerminal.star_terminal`
and `WithInitial.star_initial`.

The inclusion from `C` intro `WithTerminal C` resp. `WithInitial C` is denoted
`WithTerminal.incl` resp. `WithInitial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `WithTerminal C` resp. `WithInitial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `inclLift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `liftUnique` provides the uniqueness property of `lift`.

In addition to this, we provide `WithTerminal.map` and `WithInitial.map` providing the
functoriality of these constructions with respect to functors on the base categories.

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

/--From a functor `C⥤D`, the induced `WithTerminal C⥤ WithTerminal D`.-/
def extendFunctor {D : Type*} [Category D]  (F: C ⥤ D) : WithTerminal C ⥤  WithTerminal D where
  obj  := fun X =>
        match X with
        | of x => of (F.obj x)
        | star => star
  map := fun {X Y} f =>
        match X, Y, f with
        | of x, of y, f => F.map (down f)
        | of x, star, _ => starTerminal.from (of (F.obj x))
        | star, star, _ => 𝟙 _

/--The map  `extendFunctor` preserves identities.-/
theorem extendFunctor_id (D : Type*) [Category D]  : extendFunctor (𝟭  D) = 𝟭 (WithTerminal D) := by
  unfold extendFunctor
  apply Functor.ext
  intro X Y f
  match X, Y, f with
  | of x, of y, f => simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.comp_id,
    Category.id_comp]
                     rfl
  | of x, star, _ => rfl
  | star, star, _ => rfl
  intro X
  match X with
  | of x => rfl
  | star => rfl

theorem extendFunctor_comp {D : Type*} [Category D] {E : Type*} [Category E] (F : C⥤ D) (G:D⥤ E) :
    extendFunctor (F⋙G) = (extendFunctor F )⋙ (extendFunctor G) := by
  unfold extendFunctor
  apply Functor.ext
  intro X Y f
  match X, Y, f with
  | of x, of y, f => simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.comp_id,
    Category.id_comp]
                     rfl
  | of x, star, _ => rfl
  | star, star, _ => rfl
  intro X
  match X with
  | of x => rfl
  | star => rfl

/--From a natrual transformation of functors `C⥤D`, the induced natural transformation
of functors `WithTerminal C⥤ WithTerminal D` -/
def extendNatTrans  {D : Type*} [Category D]  {F G: C ⥤ D} (η : F ⟶ G) :
    extendFunctor F ⟶ extendFunctor G where
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
/--The map `extendNatTrans` preserves identities between fuctors.-/
theorem  extendNatTrans_id  {D : Type*} [Category D]  {F : C ⥤ D}  :
    extendNatTrans (𝟙 (F)) = 𝟙 (extendFunctor F):= by
  aesop_cat
/--The map `extendNatTrans` preserves horizontal compositions of natural transformations.-/
theorem  extendNatTrans_comp   {D : Type*} [Category D]  {F G H : C ⥤ D} (η : F⟶ G) (μ : G⟶ H) :
    extendNatTrans (η ≫ μ ) = extendNatTrans η≫ extendNatTrans μ  := by
  aesop_cat

/--The extension of a natural isomorphism between functors.-/
def extendFuncIso {D : Type*} [Category D] {F G: C⥤ D} (η : F ≅ G) :
    extendFunctor F ≅ extendFunctor G where
  hom := extendNatTrans η.hom
  inv := extendNatTrans η.inv
  hom_inv_id := by rw [← extendNatTrans_comp,η.hom_inv_id,extendNatTrans_id]
  inv_hom_id := by rw [← extendNatTrans_comp,η.inv_hom_id,extendNatTrans_id]

/--The extension of an equivalance `C ≌ D` to an equivalance `WithTerminal C ≌ WithTerminal D `.-/
def extendEquiv {D : Type*} [Category D]  (e: C ≌ D) : WithTerminal C ≌ WithTerminal D :=
  Equivalence.mk (extendFunctor e.functor) (extendFunctor e.inverse)
   ((eqToIso (extendFunctor_id C).symm).trans
 ((extendFuncIso e.unitIso).trans (eqToIso (extendFunctor_comp e.functor e.inverse))))
    ( (eqToIso (extendFunctor_comp e.inverse e.functor).symm).trans
          ((extendFuncIso e.counitIso).trans (eqToIso (extendFunctor_id D))))



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

/--From a functor `C⥤D`, the induced `WithInitial C⥤ WithInitial D`.-/
def extendFunctor {D : Type*} [Category D]  (F: C ⥤ D) : WithInitial C ⥤  WithInitial D where
  obj  := fun X =>
        match X with
        | of x => of (F.obj x)
        | star => star
  map := fun {X Y} f =>
        match X, Y, f with
        | of x, of y, f => F.map (down f)
        | star, of x, _ => starInitial.to (of (F.obj x))
        | star, star, _ => 𝟙 _

/--The map `extendFunctor` preserves identities.-/
theorem extendFunctor_id (D : Type*) [Category D]  : extendFunctor (𝟭  D) = 𝟭 (WithInitial D) := by
  unfold extendFunctor
  apply Functor.ext
  intro X Y f
  match X, Y, f with
  | of x, of y, f => simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.comp_id,
    Category.id_comp]
                     rfl
  | star, of x, _ => rfl
  | star, star, _ => rfl
  intro X
  match X with
  | of x => rfl
  | star => rfl

/--The map `extendFunctor` preserves compositions.-/
theorem extendFunctor_comp {D : Type*} [Category D] {E : Type*} [Category E] (F : C⥤ D) (G:D⥤ E) :
    extendFunctor (F⋙G) = (extendFunctor F )⋙ (extendFunctor G) := by
  unfold extendFunctor
  apply Functor.ext
  intro X Y f
  match X, Y, f with
  | of x, of y, f => simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.comp_id,
    Category.id_comp]
                     rfl
  | star, of x,  _ => rfl
  | star, star, _ => rfl
  intro X
  match X with
  | of x => rfl
  | star => rfl

/--From a natrual transformation of functors `C⥤D`, the induced natural transformation
of functors `WithInitial C⥤ WithInitial D` -/
def extendNatTrans  {D : Type*} [Category D]  {F G: C ⥤ D} (η : F ⟶ G) :
    extendFunctor F ⟶ extendFunctor G where
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

/--The map `extendNatTrans` preserves identities.-/
theorem  extendNatTrans_id  {D : Type*} [Category D]  {F : C ⥤ D}  :
    extendNatTrans (𝟙 (F)) = 𝟙 (extendFunctor F):= by
  aesop_cat

/--The map `extendNatTrans` preserves compositions.-/
theorem  extendNatTrans_comp   {D : Type*} [Category D]  {F G H : C ⥤ D} (η : F⟶ G) (μ : G⟶ H) :
    extendNatTrans (η ≫ μ ) = extendNatTrans η≫ extendNatTrans μ  := by
  aesop_cat

/--Given an natural isomorphism between functors `C⥤D` we get a natural isomorphism between
the functors `liftFunctor F ≅ liftFunctor G `.-/
def extendFuncIso {D : Type*} [Category D] {F G: C⥤ D} (η : F ≅ G) :
    extendFunctor F ≅ extendFunctor G where
  hom := extendNatTrans η.hom
  inv := extendNatTrans η.inv
  hom_inv_id := by rw [← extendNatTrans_comp,η.hom_inv_id,extendNatTrans_id]
  inv_hom_id := by rw [← extendNatTrans_comp,η.inv_hom_id,extendNatTrans_id]

/--Given an equivalence between two categories `C` and `D` we get an equivalance between the
categories  `WithInitial C` and  `WithInitial D  `.-/
def extendEquiv {D : Type*} [Category D]  (e: C ≌ D) : WithInitial C ≌ WithInitial D :=
  Equivalence.mk (extendFunctor e.functor) (extendFunctor e.inverse)
   ((eqToIso (extendFunctor_id C).symm).trans
 ((extendFuncIso e.unitIso).trans (eqToIso (extendFunctor_comp e.functor e.inverse))))
    ( (eqToIso (extendFunctor_comp e.inverse e.functor).symm).trans
          ((extendFuncIso e.counitIso).trans (eqToIso (extendFunctor_id D))))




end WithInitial
variable {C}
open Opposite
/--From an object in `WithTerminal C`, the corresponding object in `WithInitial Cᵒᵖ`-/
private def withTerminalOpToWithInitialOfOpObj (X: WithTerminal C):
    WithInitial Cᵒᵖ :=
  match   X  with
  |  WithTerminal.of x =>  (WithInitial.of (Opposite.op x))
  |  WithTerminal.star =>  WithInitial.star

/--From a morphism in `WithTerminal C`, the corresponding morphism in `WithInitial Cᵒᵖ`-/
private def withTerminalOpToWithInitialOfOpHom   {X Y: WithTerminal C} (f : X ⟶ Y):
    withTerminalOpToWithInitialOfOpObj Y ⟶ withTerminalOpToWithInitialOfOpObj  X :=
  match X, Y, f  with
  | WithTerminal.of _, WithTerminal.of _, f' => (WithTerminal.down f').op
  | WithTerminal.of x,WithTerminal.star, _ =>
     (WithInitial.starInitial.to (WithInitial.of (Opposite.op x)))
  | WithTerminal.star, WithTerminal.star, _ => 𝟙 _
/--A functor from `(WithTerminal C)ᵒᵖ ` to `WithInitial Cᵒᵖ`.-/
def withTerminalOpToWithInitialOfOp : (WithTerminal C)ᵒᵖ ⥤ (WithInitial Cᵒᵖ) where
  obj X :=  withTerminalOpToWithInitialOfOpObj (unop X)
  map {X Y} f := withTerminalOpToWithInitialOfOpHom f.unop
  map_id :=by
     intro X
     cases X
     aesop_cat
  map_comp :=by
     intro X Y Z f g
     cases X; cases Y; cases Z; cases f; cases g;
     rename_i Xp Yp Zp fp gp
     rw [unop_op,unop_op] at fp gp
     simp only [unop_op, unop_comp]
     aesop_cat
/--A functor from `WithInitial Cᵒᵖ` to  `(WithTerminal C)ᵒᵖ `.-/
def withInitialOfOpToWithTerminal : (WithInitial Cᵒᵖ) ⥤ (WithTerminal C)ᵒᵖ   where
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



lemma withInitialOfOpToWithTerminal_comp_withTerminalOpToWithInitialOfOp (X : (WithInitial Cᵒᵖ)) :
    (withTerminalOpToWithInitialOfOp).obj ((withInitialOfOpToWithTerminal).obj X) = X := by
  cases X <;> rfl

lemma withTerminalOpToWithInitialOfOp_comp_withInitialOfOpToWithTerminal (X : (WithTerminal C)ᵒᵖ) :
    (withInitialOfOpToWithTerminal ).obj ((withTerminalOpToWithInitialOfOp).obj X) = X := by
  unfold withTerminalOpToWithInitialOfOp
  simp
  cases X
  rename_i Y
  simp only [unop_op]
  aesop_cat


/--An equivalance between the categories `WithInitial Cᵒᵖ` and  `(WithTerminal C)ᵒᵖ`.-/
def equivWithInitialOfOpWithTerminalOp (C : Type*) [Category C]:
    WithInitial Cᵒᵖ  ≌ (WithTerminal C)ᵒᵖ  where
  functor := withInitialOfOpToWithTerminal
  inverse := withTerminalOpToWithInitialOfOp
  unitIso := {
    hom := {app := fun G =>
     eqToHom (withInitialOfOpToWithTerminal_comp_withTerminalOpToWithInitialOfOp G).symm}
    inv := {app := fun G =>
     eqToHom (withInitialOfOpToWithTerminal_comp_withTerminalOpToWithInitialOfOp G) }
  }
  counitIso := {
    hom := {
      app := fun G =>
        eqToHom (withTerminalOpToWithInitialOfOp_comp_withInitialOfOpToWithTerminal  G)
      naturality := by
          intro X Y f
          cases X; cases Y; cases f;
          rename_i Xp Yp fp
          cases Xp <;> cases Yp <;>
          simp only [Functor.id_obj, Functor.comp_obj, unop_op, Functor.id_map,
            eqToHom_refl, Category.comp_id, Functor.comp_map, Category.id_comp]
          any_goals rfl
          simp only [unop_op] at fp
          exact (WithTerminal.false_of_from_star fp).elim
    }
    inv := {
      app := fun G =>
         eqToHom (withTerminalOpToWithInitialOfOp_comp_withInitialOfOpToWithTerminal G).symm
      naturality := by
          intro X Y f
          cases X; cases Y; cases f;
          rename_i Xp Yp fp
          cases Xp <;> cases Yp <;>
          simp only [Functor.id_obj, Functor.comp_obj, unop_op, Functor.id_map,
            eqToHom_refl, Category.comp_id, Functor.comp_map, Category.id_comp]
          any_goals rfl
          simp only [unop_op] at fp
          exact (WithTerminal.false_of_from_star fp).elim
    }
  }
/--An equivalance between the categories ` WithTerminal Cᵒᵖ ` and  `(WithInitial C)ᵒᵖ`.-/
def equivWithTerminalOfOpWithInitialOp : WithTerminal Cᵒᵖ  ≌ (WithInitial C)ᵒᵖ :=
  ((Equivalence.op (WithInitial.extendEquiv (opOpEquivalence C)).symm).trans
    ((Equivalence.op (equivWithInitialOfOpWithTerminalOp Cᵒᵖ)).trans
      (opOpEquivalence (WithTerminal Cᵒᵖ)))).symm

end CategoryTheory
