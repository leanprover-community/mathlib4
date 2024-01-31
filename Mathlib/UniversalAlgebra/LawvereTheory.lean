import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Tactic

universe v v' u u'

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

def ProdWord.unpack {S : Type u} : ProdWord S → Array S
  | .of X => #[X]
  | .prod a b => a.unpack ++ b.unpack
  | .nil => #[]

def ProdWord.lift {S : Type u} {S' : Type u'} (f : S → ProdWord S') : ProdWord S → ProdWord S'
  | .of t => f t
  | .prod a b => .prod (a.lift f) (b.lift f)
  | .nil => .nil

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

inductive LawvereRel {S : Type u} {op : ProdWord S → S → Type v}
    (rel : {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop) :
    {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop where
  | of {X Y : ProdWord S} {f g : LawvereWord op X Y} : rel f g → LawvereRel rel f g
  | rfl {X Y : ProdWord S} (f : LawvereWord op X Y) : LawvereRel rel f f
  | symm {X Y : ProdWord S} {f g : LawvereWord op X Y} :
      LawvereRel rel f g → LawvereRel rel g f
  | trans {X Y : ProdWord S} {f g h : LawvereWord op X Y} :
      LawvereRel rel f g → LawvereRel rel g h → LawvereRel rel f h
  | comp_congr {X Y Z : ProdWord S}
      {f f' : LawvereWord op X Y}
      {g g' : LawvereWord op Y Z} :
      LawvereRel rel f f' → LawvereRel rel g g' → LawvereRel rel (f.comp g) (f'.comp g')
  | id_comp {X Y : ProdWord S} (f : LawvereWord op X Y) :
      LawvereRel rel (LawvereWord.id _ |>.comp f) f
  | comp_id {X Y : ProdWord S} (f : LawvereWord op X Y) :
      LawvereRel rel (f.comp <| .id _) f
  | assoc {X Y Z W : ProdWord S}
      (f : LawvereWord op X Y)
      (g : LawvereWord op Y Z)
      (h : LawvereWord op Z W) :
      LawvereRel rel ((f.comp g).comp h) (f.comp (g.comp h))
  | lift_congr
      {T P Q : ProdWord S}
      {f f' : LawvereWord op T P}
      {g g' : LawvereWord op T Q} :
      LawvereRel rel f f' →
      LawvereRel rel g g' →
      LawvereRel rel (.lift f g) (.lift f' g')
  | lift_fst
      {T P Q : ProdWord S}
      (f : LawvereWord op T P)
      (g : LawvereWord op T Q) :
      LawvereRel rel ((LawvereWord.lift f g).comp <| .fst _ _) f
  | lift_snd
      {T P Q : ProdWord S}
      (f : LawvereWord op T P)
      (g : LawvereWord op T Q) :
      LawvereRel rel ((LawvereWord.lift f g).comp <| .snd _ _) g
  | lift_unique
      {T P Q : ProdWord S}
      (f g : LawvereWord op T (P.prod Q)) :
      LawvereRel rel (f.comp <| .fst _ _) (g.comp <| .fst _ _) →
      LawvereRel rel (f.comp <| .snd _ _) (g.comp <| .snd _ _) →
      LawvereRel rel f g
  | toNil_unique {P : ProdWord S} (f g : LawvereWord op P .nil) : LawvereRel rel f g

def LawvereSetoid {S : Type u} {op : ProdWord S → S → Type v}
    (rel : {X Y : ProdWord S} → LawvereWord op X Y → LawvereWord op X Y → Prop)
    (X Y : ProdWord S) :
    Setoid (LawvereWord op X Y) where
  r := LawvereRel rel
  iseqv := ⟨LawvereRel.rfl, LawvereRel.symm, LawvereRel.trans⟩

structure LawvereTheory (S : Type u) where
  hom : ProdWord S → ProdWord S → Type v
  id (P : ProdWord S) : hom P P
  comp {P Q R : ProdWord S} : hom P Q → hom Q R → hom P R
  id_comp {P Q : ProdWord S} (f : hom P Q) : comp (id _) f = f
  comp_id {P Q : ProdWord S} (f : hom P Q) : comp f (id _) = f
  assoc {P Q R W : ProdWord S} (f : hom P Q) (g : hom Q R) (h : hom R W) :
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

variable {S : Type u} {S' : Type u'}

structure Morphism (L : LawvereTheory.{v} S) (L' : LawvereTheory.{v'} S') where
  obj : ProdWord S → ProdWord S'
  map {P Q : ProdWord S} : (L.hom P Q) → (L'.hom (obj P) (obj Q))
  map_id (P : ProdWord S) : map (L.id P) = L'.id (obj P)
  map_comp {P Q R : ProdWord S} (a : L.hom P Q) (b : L.hom Q R) :
    map (L.comp a b) = L'.comp (map a) (map b)
  toNil (P : ProdWord S') : L'.hom P (obj .nil)
  toNil_unique {P : ProdWord S'} (f g : L'.hom P (obj .nil)) : f = g
  fst (P Q : ProdWord S) : L'.hom (obj (P.prod Q)) (obj P)
  snd (P Q : ProdWord S) : L'.hom (obj (P.prod Q)) (obj Q)
  lift {T : ProdWord S'} {P Q : ProdWord S}
    (a : L'.hom T (obj P)) (b : L'.hom T (obj Q)) :
    L'.hom T (obj (P.prod Q))
  lift_fst {T : ProdWord S'} {P Q : ProdWord S}
    (a : L'.hom T (obj P)) (b : L'.hom T (obj Q)) :
    L'.comp (lift a b) (fst P Q) = a
  lift_snd {T : ProdWord S'} {P Q : ProdWord S}
    (a : L'.hom T (obj P)) (b : L'.hom T (obj Q)) :
    L'.comp (lift a b) (snd P Q) = b
  lift_unique {T : ProdWord S'} {P Q : ProdWord S} {a b : L'.hom T (obj (P.prod Q))} :
    L'.comp a (fst _ _) = L'.comp b (fst _ _) →
    L'.comp a (snd _ _) = L'.comp b (snd _ _) →
    a = b

end LawvereTheory
