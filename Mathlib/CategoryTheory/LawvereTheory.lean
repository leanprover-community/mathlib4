/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory

universe v v' u u'

/--
TODO
-/
inductive ProdWord (S : Type u) where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

/--
TODO
-/
structure LawvereTheory (S : Type u) where
  /-- TODO -/
  hom : ProdWord S → ProdWord S → Type v
  /-- TODO -/
  id (P : ProdWord S) : hom P P
  /-- TODO -/
  comp {P Q R : ProdWord S} : hom P Q → hom Q R → hom P R
  id_comp {P Q : ProdWord S} (f : hom P Q) : comp (id _) f = f
  comp_id {P Q : ProdWord S} (f : hom P Q) : comp f (id _) = f
  assoc {P Q R W : ProdWord S} (f : hom P Q) (g : hom Q R) (h : hom R W) :
    comp (comp f g) h = comp f (comp g h)
  /-- TODO -/
  fst' (H T : ProdWord S) : hom (H.prod T) H
  /-- TODO -/
  snd' (H T : ProdWord S): hom (H.prod T) T
  /-- TODO -/
  lift' {T X Y : ProdWord S} (f : hom T X) (g : hom T Y) : hom T (X.prod Y)
  lift_fst' {T X Y : ProdWord S} (f : hom T X) (g : hom T Y) :
    comp (lift' f g) (fst' _ _) = f
  lift_snd' {T X Y : ProdWord S} (f : hom T X) (g : hom T Y) :
    comp (lift' f g) (snd' _ _) = g
  lift_unique' {T X Y : ProdWord S} (f g : hom T (X.prod Y)) :
    comp f (fst' _ _) = comp g (fst' _ _) →
    comp f (snd' _ _) = comp g (snd' _ _) →
    f = g
  /-- TODO -/
  toNil (P : ProdWord S) :
    hom P .nil
  toNil_unique {P : ProdWord S} (f g : hom P .nil) :
    f = g

namespace LawvereTheory

variable {S : Type u} (L : LawvereTheory.{v} S)


/--
TODO
-/
structure Carrier (L : LawvereTheory.{v} S) where
  /-- TODO -/
  as : ProdWord S

instance : CoeSort (LawvereTheory.{v} S) (Type u) where
  coe L := L.Carrier

instance (L : LawvereTheory.{v} S) : Category.{v} L where
  Hom X Y := L.hom X.as Y.as
  id _ := L.id _
  comp := L.comp
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.assoc

instance : ChosenFiniteProducts L where
  product X Y := .mk
    (Limits.BinaryFan.mk (L.fst' X.as Y.as) (L.snd' X.as Y.as))
    (Limits.BinaryFan.isLimitMk
      (fun S => L.lift' S.fst S.snd)
      (fun S => L.lift_fst' _ _)
      (fun S => L.lift_snd' _ _)
      (fun S m h1 h2 => L.lift_unique' _ _
        (by simpa [L.lift_fst'] using h1)
        (by simpa [L.lift_snd'] using h2)))
  terminal := .mk
    (.mk (.mk .nil) <| .mk (fun x => x.as.elim) (fun x => x.as.elim))
    (.mk (fun S => L.toNil _) (fun _ x => x.as.elim) (fun _ _ _ => L.toNil_unique _ _))

abbrev of (X : ProdWord S) : L := .mk X
abbrev singleton (X : S) : L := .mk <| .of X

open ChosenFiniteProducts MonoidalCategory

@[simp]
lemma Carrier.of_nil : L.of .nil = 𝟙_ _ := rfl

@[simp]
lemma Carrier.of_prod (X Y : ProdWord S) : L.of (X.prod Y) = L.of X ⊗ L.of Y := rfl

@[simp]
lemma Carrier.of_of (X : S) : L.of (.of X) = L.singleton X := rfl

structure Algebra (C : Type u') [Category.{v'} C] where
  functor : L ⥤ C
  isLimit (X Y : L) :
    Limits.IsLimit (Limits.BinaryFan.mk
      (functor.map <| fst X Y)
      (functor.map <| snd X Y))
  isTerminal : Limits.IsTerminal (functor.obj <| 𝟙_ _)

variable {L}
def Algebra.lift
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f : T ⟶ A.functor.obj X)
    (g : T ⟶ A.functor.obj Y) :
    T ⟶ A.functor.obj (X ⊗ Y) :=
  (A.isLimit _ _).lift <| Limits.BinaryFan.mk f g

@[reassoc (attr := simp)]
lemma Algebra.lift_fst
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f : T ⟶ A.functor.obj X) (g : T ⟶ A.functor.obj Y) :
    A.lift f g ≫ A.functor.map (fst _ _) = f :=
  (A.isLimit _ _).fac _ <| .mk .left

@[reassoc (attr := simp)]
lemma Algebra.lift_snd
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f : T ⟶ A.functor.obj X) (g : T ⟶ A.functor.obj Y) :
    A.lift f g ≫ A.functor.map (snd _ _) = g :=
  (A.isLimit _ _).fac _ <| .mk .right

@[ext 1050]
def Algebra.hom_ext
    {C : Type u'} [Category.{v'} C] (A : L.Algebra C) {T : C} {X Y : L}
    (f g : T ⟶ A.functor.obj (X ⊗ Y))
    (h_fst : f ≫ A.functor.map (fst _ _) = g ≫ A.functor.map (fst _ _))
    (h_snd : f ≫ A.functor.map (snd _ _) = g ≫ A.functor.map (snd _ _)) : f = g := by
  apply (A.isLimit _ _).hom_ext
  rintro (_|_)
  · exact h_fst
  · exact h_snd

instance (C : Type u') [Category.{v'} C] : Category (L.Algebra C) :=
  InducedCategory.category fun A => A.functor

variable (L) in
@[simps]
def algebraForget (C : Type u') [Category.{v'} C] :
    L.Algebra C ⥤ (S → C) where
  obj A X := A.functor.obj <| L.singleton X
  map f X := f.app _

instance (C : Type u') [Category.{v'} C] : Faithful (L.algebraForget C) where
  map_injective {X Y f g} h := by
    apply NatTrans.ext ; funext ⟨P⟩
    induction P with
    | of T =>
      apply congr_fun h
    | prod U V h1 h2 =>
      dsimp only [Carrier.of_prod]
      apply Y.hom_ext
      · simp only [← NatTrans.naturality, h1]
      · simp only [← NatTrans.naturality, h2]
    | nil => apply Y.isTerminal.hom_ext

@[ext]
lemma Algebra.morphism_ext {C : Type u'} [Category.{v'} C] {X Y : L.Algebra C}
    (f g : X ⟶ Y) (h : ∀ (X : S), f.app (L.singleton X) = g.app (L.singleton X)) :
    f = g :=
  (algebraForget L C).map_injective <| funext h

section free

variable (L) (X : S → Type u')
inductive FreeRep : ProdWord S → Type (max v u u') where
  | of {T : S} : X T → FreeRep (.of T)
  | map {A B : ProdWord S} : L.hom A B → FreeRep A → FreeRep B
  | lift {A B : ProdWord S} : FreeRep A → FreeRep B → FreeRep (A.prod B)
  | unit : FreeRep .nil

inductive FreeRel :
    {A : ProdWord S} → L.FreeRep X A → L.FreeRep X A → Prop where
  | rfl {A : ProdWord S} (f : L.FreeRep X A) : FreeRel f f
  | symm {A : ProdWord S} {f g : L.FreeRep X A} : FreeRel f g → FreeRel g f
  | trans {A : ProdWord S} {f g h : L.FreeRep X A} :
    FreeRel f g → FreeRel g h → FreeRel f h
  | map_congr {A B : ProdWord S} {x y : L.FreeRep X A} {f : L.hom A B} :
      FreeRel x y → FreeRel (x.map f) (y.map f)
  | map_id {A : ProdWord S} (x : L.FreeRep X A) :
      FreeRel (x.map <| L.id A) x
  | map_comp {A B C : ProdWord S} (f : L.hom A B) (g : L.hom B C) (x : L.FreeRep X A) :
      FreeRel (x.map <| L.comp f g) ((x.map f).map g)
  | lift_fst {A B : ProdWord S} (x : L.FreeRep X A) (y : L.FreeRep X B) :
      FreeRel ((FreeRep.lift x y).map <| L.fst' _ _) x
  | lift_snd {A B : ProdWord S} (x : L.FreeRep X A) (y : L.FreeRep X B) :
      FreeRel ((FreeRep.lift x y).map <| L.snd' _ _) y
  | lift_unique {A B : ProdWord S} (x y : L.FreeRep X (A.prod B)) :
      FreeRel (x.map <| L.fst' _ _) (y.map <| L.fst' _ _) →
      FreeRel (x.map <| L.snd' _ _) (y.map <| L.snd' _ _) →
      FreeRel x y
  | lift_congr {A B : ProdWord S}
      {x x' : L.FreeRep X A}
      {y y' : L.FreeRep X B} :
      FreeRel x x' →
      FreeRel y y' →
      FreeRel (x.lift y) (x'.lift y')
  | unit_unique (x y : L.FreeRep X .nil) : FreeRel x y

def FreeSetoid (A : ProdWord S) :
    Setoid (L.FreeRep X A) where
  r := L.FreeRel _
  iseqv := ⟨.rfl, .symm, .trans⟩

def Free (A : ProdWord S) : Type _ :=
  Quotient <| L.FreeSetoid X A

variable {L X}
def Free.fst {A B : ProdWord S} :
    L.Free X (A.prod B) → L.Free X A :=
  Quotient.lift (fun a => Quotient.mk _ <| a.map <| L.fst' _ _)
  fun _ _ h => Quotient.sound <| .map_congr h

def Free.snd {A B : ProdWord S} :
    L.Free X (A.prod B) → L.Free X B :=
  Quotient.lift (fun a => Quotient.mk _ <| a.map <| L.snd' _ _)
  fun _ _ h => Quotient.sound <| .map_congr h

def Free.lift {A B : ProdWord S}
    (x : L.Free X A) (y : L.Free X B) :
    L.Free X (A.prod B) :=
  Quotient.liftOn₂ x y (fun a b => Quotient.mk _ <| .lift a b)
  fun _ _ _ _ h₁ h₂ => Quotient.sound <| .lift_congr h₁ h₂

lemma Free.lift_fst {A B : ProdWord S}
    (x : L.Free X A) (y :  L.Free X B) :
    (x.lift y).fst = x := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply Quotient.sound
  apply FreeRel.lift_fst

lemma Free.lift_snd {A B : ProdWord S}
    (x : L.Free X A) (y :  L.Free X B) :
    (x.lift y).snd = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply Quotient.sound
  apply FreeRel.lift_snd

lemma Free.lift_ext {A B : ProdWord S}
    (x y : L.Free X (A.prod B))
    (h_fst : x.fst = y.fst)
    (h_snd : x.snd = y.snd) :
    x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply Quotient.sound
  apply FreeRel.lift_unique
  exact Quotient.exact h_fst
  exact Quotient.exact h_snd

lemma Free.unit_ext
    (x y : L.Free X .nil) : x = y := by
  rcases x with ⟨x⟩
  rcases y with ⟨x⟩
  apply Quotient.sound
  apply FreeRel.unit_unique

variable (L X)
def FreeAlgebra : L.Algebra (Type (max v u u')) where
  functor := {
    obj := fun A => L.Free X A.as
    map := fun f =>
      Quotient.lift
      (fun r => Quotient.mk _ <| FreeRep.map f r)
      fun a b h => Quotient.sound <| .map_congr h
    map_id := by
      rintro ⟨A⟩
      ext ⟨T⟩
      apply Quotient.sound
      apply FreeRel.map_id
    map_comp := by
      rintro ⟨A⟩ ⟨B⟩ ⟨C⟩ f g
      ext ⟨T⟩
      apply Quotient.sound
      apply FreeRel.map_comp }
  isLimit := fun ⟨A⟩ ⟨B⟩ => Limits.BinaryFan.isLimitMk
    (fun S x => Free.lift _ _)
    (fun S => funext fun x => Free.lift_fst _ _)
    (fun S => funext fun x => Free.lift_snd _ _)
    (fun S m h1 h2 => funext fun x => Free.lift_ext _ _
      (by simp only [Free.lift_fst] ; exact congr_fun h1 _)
      (by simp only [Free.lift_snd] ; exact congr_fun h2 _))
  isTerminal := .mk
    (fun S _ => Quotient.mk _ <| .unit)
    (fun S j => j.as.elim)
    (fun S _ _ => funext fun _ => Free.unit_ext _ _)

end free

end LawvereTheory
end CategoryTheory
