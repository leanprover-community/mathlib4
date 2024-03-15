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

open ChosenFiniteProducts MonoidalCategory

@[simp]
lemma Carrier.mk_nil : L.of .nil = 𝟙_ _ := rfl

@[simp]
lemma Carrier.mk_prod (X Y : ProdWord S) : L.of (X.prod Y) = L.of X ⊗ L.of Y := rfl

structure Algebra (C : Type u') [Category.{v'} C] where
  functor : L ⥤ C
  prod (X Y : L) :
    Limits.IsLimit (Limits.BinaryFan.mk
      (functor.map <| fst X Y)
      (functor.map <| snd X Y))
  unit : Limits.IsTerminal (functor.obj <| 𝟙_ _)

instance (C : Type u') [Category.{v'} C] : Category (L.Algebra C) :=
  InducedCategory.category fun A => A.functor

end LawvereTheory
end CategoryTheory
