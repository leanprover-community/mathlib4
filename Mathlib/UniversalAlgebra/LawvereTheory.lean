import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.Data.FinEnum
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Tactic

universe v v' u u'

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

def ProdWord.toList {S : Type u} : ProdWord S → List S := fun
  | .of X => [X]
  | .prod A B => A.toList ++ B.toList
  | .nil => []

def ProdWord.unpack {S : Type u} : ProdWord S → Array S
  | .of X => #[X]
  | .prod a b => a.unpack ++ b.unpack
  | .nil => #[]

def ProdWord.lift {S : Type u} {S' : Type u'} (f : S → ProdWord S') : ProdWord S → ProdWord S'
  | .of t => f t
  | .prod a b => .prod (a.lift f) (b.lift f)
  | .nil => .nil

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
