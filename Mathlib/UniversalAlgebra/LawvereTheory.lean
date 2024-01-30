import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.Data.FinEnum
import Mathlib.Tactic

universe u u' v v'

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

def ProdWord.unpack {S : Type u} : ProdWord S → List S
  | .of X => [X]
  | .prod a b => a.unpack ++ b.unpack
  | .nil => []

def ProdWord.map {S : Type u} {S' : Type u'} (f : S → S') : ProdWord S → ProdWord S'
  | .of t => .of (f t)
  | .prod a b => .prod (map f a) (map f b)
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

structure FiniteLawverePresentation where
  numSort : ℕ
  sortName (S : Fin numSort) : String
  numOps (P : ProdWord (Fin numSort)) (Q : Fin numSort) : ℕ
  opName (P : ProdWord (Fin numSort)) (S : Fin numSort) (op : Fin (numOps P S)) : Lean.Name
  rels {P Q : ProdWord (Fin numSort)} :
    List (Lean.Name × LawvereWord (fun a b => Fin (numOps a b)) P Q ×
      LawvereWord (fun a b => Fin (numOps a b)) P Q)

structure LawvereTheory where
  S : Type u
  hom : ProdWord S → ProdWord S → Type v
  id (P : ProdWord S) : hom P P
  comp {P Q R : ProdWord S} : hom P Q → hom Q R → hom P R
  id_comp {P Q : ProdWord S} (f : hom P Q) : comp (id _) f = f
  comp_id {P Q : ProdWord S} (f : hom P Q) : comp f (id _) = f
  assoc {P Q R W : ProdWord S} (f : hom P Q) (g : hom Q R) (h : hom R W) :
    comp (comp f g) h = comp f (comp g h)
  fst' (P Q : ProdWord S) : hom (P.prod Q) P
  snd' (P Q : ProdWord S) : hom (P.prod Q) Q
  lift' {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) : hom T (P.prod Q)
  lift'_fst' {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) :
    comp (lift' f g) (fst' _ _) = f
  lift'_snd' {T P Q : ProdWord S} (f : hom T P) (g : hom T Q) :
    comp (lift' f g) (snd' _ _) = g
  lift'_unique {T P Q : ProdWord S} {f g : hom T (P.prod Q)} :
    comp f (fst' _ _) = comp g (fst' _ _) →
    comp f (snd' _ _) = comp g (snd' _ _) →
    f = g
  toNil' (P : ProdWord S) : hom P .nil
  toNil'_unique {P : ProdWord S} (f g : hom P .nil) : f = g

namespace LawvereTheory

variable (L : LawvereTheory.{u,v}) (L' : LawvereTheory.{u',v'})

structure Obj : Type u where as : ProdWord L.S

instance : CoeSort LawvereTheory (Type _) where coe := Obj

open CategoryTheory

instance : Category.{v} L where
  Hom X Y := L.hom X.as Y.as
  id X := L.id X.as
  comp := L.comp
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.assoc

def nil : L := .mk .nil

def toNil (P : L) : P ⟶ L.nil := L.toNil' _

def prod (P Q : L) : L := .mk <| P.as.prod Q.as

def fst (P Q : L) : L.prod P Q ⟶ P := L.fst' _ _
def snd (P Q : L) : L.prod P Q ⟶ Q := L.snd' _ _

def lift {T P Q : L} (a : T ⟶ P) (b : T ⟶ Q) : T ⟶ L.prod P Q := L.lift' a b

@[ext]
structure Morphism  (L : LawvereTheory.{u,v}) (L' : LawvereTheory.{u',v'}) where
  obj : L → L'
  map {P Q : L} : (P ⟶ Q) → (obj P ⟶ obj Q)
  map_id (P : L) : map (𝟙 P) = 𝟙 (obj P)
  map_comp {P Q R : L} (a : P ⟶ Q) (b : Q ⟶ R) :
    map (a ≫ b) = map a ≫ map b
  toNil (P : L') : P ⟶ (obj L.nil)
  toNil_unique {P : L'} (f g : P ⟶ obj L.nil) : f = g
  fst (P Q : L) : (obj (L.prod P Q)) ⟶ obj P
  snd (P Q : L) : (obj (L.prod P Q)) ⟶ obj Q
  lift {T : L'} {P Q : L} (a : T ⟶ obj P) (b : T ⟶ obj Q) :
    T ⟶ obj (L.prod P Q)
  lift_fst {T : L'} {P Q : L} (a : T ⟶ obj P) (b : T ⟶ obj Q) :
    lift a b ≫ fst P Q = a
  lift_snd {T : L'} {P Q : L} (a : T ⟶ obj P) (b : T ⟶ obj Q) :
    lift a b ≫ snd P Q = b
  lift_unique {T : L'} {P Q : L} {a b : T ⟶ obj (L.prod P Q)} :
    a ≫ fst _ _ = b ≫ fst _ _ →
    a ≫ snd _ _ = b ≫ snd _ _ →
    a = b

def Morphism.preservesNil {L L' : LawvereTheory} (F : Morphism L L') :
    F.obj L.nil ≅ L'.nil where
  hom := L'.toNil _
  inv := F.toNil _
  hom_inv_id := sorry
  inv_hom_id := sorry

def Morphism.preservesProd {L L' : LawvereTheory} (F : Morphism L L') (P Q : L) :
    F.obj (L.prod P Q) ≅ L'.prod (F.obj P) (F.obj Q) where
  hom := L'.lift (F.map <| L.fst _ _) (F.map <| L.snd _ _)
  inv := F.lift (L'.fst _ _) (L'.snd _ _)
  hom_inv_id := sorry
  inv_hom_id := sorry

def Morphism.id (L : LawvereTheory.{u,v}) : Morphism L L where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
  toNil _ := L.toNil' _
  toNil_unique := sorry
  fst _ _ := L.fst _ _
  snd _ _ := L.snd _ _
  lift := L.lift
  lift_fst := sorry
  lift_snd := sorry
  lift_unique := sorry

def Morphism.comp {L L' L'' : LawvereTheory} (f : Morphism L L') (g : Morphism L' L'') :
    Morphism L L'' where
  obj X := g.obj (f.obj X)
  map a := g.map (f.map a)
  map_id _ := by simp [f.map_id, g.map_id]
  map_comp := by simp [f.map_comp, g.map_comp]
  toNil X := g.toNil _ ≫ g.map (f.toNil _)
  toNil_unique := sorry
  fst P Q := g.map <| f.map <| L.fst _ _
  snd P Q := g.map <| f.map <| L.snd _ _
  lift a b := g.lift a b ≫ g.map (f.lift (L'.fst _ _) (L'.snd _ _))
  lift_fst := sorry
  lift_snd := sorry
  lift_unique := sorry

end LawvereTheory
