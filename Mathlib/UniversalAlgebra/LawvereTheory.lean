import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.Tactic

universe v u

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

inductive LawvereWord {S : Type u} (op : ProdWord S → S → Type v) :
    ProdWord S → ProdWord S → Type (max v u) where
  | of {P : ProdWord S} {T : S} (f : op P T) :
      LawvereWord op P (.of T)
  | id (P : ProdWord S) :
      LawvereWord op P P
  | comp {P Q R : ProdWord S} :
      LawvereWord op P Q →
      LawvereWord op Q R →
      LawvereWord op P R
  | fst (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) P
  | snd (P Q : ProdWord S) :
      LawvereWord op (P.prod Q) Q
  | lift {T P Q : ProdWord S} :
      LawvereWord op T P →
      LawvereWord op T Q →
      LawvereWord op T (P.prod Q)
  | toNil (P : ProdWord S) :
      LawvereWord op P .nil

structure LawverePresentation (S : Type u) where
  op : ProdWord S → S → Type v
  rel : {P Q : ProdWord S} → LawvereWord op P Q → LawvereWord op P Q → Prop

open CategoryTheory Limits

structure LawvereTheory (S : Type u) where
  hom : ProdWord S → ProdWord S → Type v
  id (P : ProdWord S) : hom P P
  comp {P Q R : ProdWord S} : hom P Q → hom Q R → hom P R
  id_comp {P Q : ProdWord S} (f : hom P Q) : comp (id _) f = f
  comp_id {P Q : ProdWord S} (f : hom P Q) : comp f (id _) = f
  comp_assoc {P Q R W : ProdWord S} (f : hom P Q) (g : hom Q R) (h : hom R W) :
    comp (comp f g) h = comp f (comp g h)
  fst (P Q : ProdWord S) : hom (P.prod Q) P
  snd (P Q : ProdWord S) : hom (P.prod Q) Q
  lift {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) : hom T (P.prod Q)
  lift_fst {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) :
    comp (lift f g) (fst _ _) = f
  lift_snd {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) :
    comp (lift f g) (snd _ _) = g
  lift_unique {T P Q : ProdWord S} {f g : hom T (P.prod Q)} :
    comp f (fst _ _) = comp g (fst _ _) →
    comp f (snd _ _) = comp g (snd _ _) →
    f = g
  toNil (P : ProdWord S) : hom P .nil
  toNil_unique {P : ProdWord S} (f g : hom P .nil) : f = g

namespace LawvereTheory

variable {S : Type u} (L : LawvereTheory.{v} S)

structure type (L : LawvereTheory.{v} S) : Type u where as : ProdWord S

instance : CoeSort (LawvereTheory.{v} S) (Type u) where coe L := L.type

instance (L : LawvereTheory.{v} S) : Category.{v} L where
  Hom X Y := L.hom X.as Y.as
  id X := L.id X.as
  comp := L.comp
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.comp_assoc

def prod (P Q : L) : L := .mk <| P.as.prod Q.as

@[simps!]
def binaryFan (P Q : L) : BinaryFan P Q :=
  BinaryFan.mk (P := L.prod P Q) (L.fst _ _) (L.snd _ _)

@[simps!]
def isLimitBinaryFan (P Q : L) : IsLimit (L.binaryFan P Q) :=
  BinaryFan.isLimitMk
    (fun S => L.lift S.fst S.snd)
    (fun S => L.lift_fst _ _)
    (fun S => L.lift_snd _ _)
    (fun S m hfst hsnd =>
      L.lift_unique (by simpa [L.lift_fst]) (by simpa [L.lift_snd]))

def emptyCone : Cone (Functor.empty L) where
  pt := .mk <| .nil
  π := { app := fun ⟨X⟩ => X.elim }

def isLimitEmptyCone : IsLimit L.emptyCone where
  lift _ := L.toNil _
  fac _ := fun ⟨j⟩ => j.elim
  uniq _ _ _ := L.toNil_unique _ _

-- :-)
instance (L : LawvereTheory.{v} S) : MonoidalCategory L :=
  monoidalOfChosenFiniteProducts
    ⟨L.emptyCone, L.isLimitEmptyCone⟩ fun {_ _} =>
      ⟨L.binaryFan _ _, L.isLimitBinaryFan _ _⟩

end LawvereTheory
