import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathlib.Tactic

#check Quiver.Hom
universe v v' u u'

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

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

attribute [simp]
  LawvereTheory.id_comp
  LawvereTheory.comp_id
  LawvereTheory.assoc
  LawvereTheory.lift_fst
  LawvereTheory.lift_snd

attribute [ext]
  LawvereTheory.lift_unique
  LawvereTheory.toNil_unique

namespace LawvereTheory

scoped notation:10 A " ⟶[" L "]" B:11 => LawvereTheory.hom L A B
scoped notation "𝟙[" L "]" => LawvereTheory.id L
scoped notation:80 A " ≫[" L "]" B:81 => LawvereTheory.comp L A B

variable {S : Type u} (L : LawvereTheory.{v} S)

/-
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
-/

structure MorphismAlong {S : Type u} {S' : Type u'} (f : S → S')
    (L : LawvereTheory.{v} S) (L' : LawvereTheory.{v'} S') where
  map {P Q : ProdWord S} : (P ⟶[L] Q) → ((P.map f) ⟶[L'] (Q.map f))
  map_id (P : ProdWord S) : map (𝟙[L] P) = 𝟙[L'] _
  map_comp {P Q R : ProdWord S} (a : P ⟶[L] Q) (b : Q ⟶[L] R) :
    map (a ≫[L] b) = (map a) ≫[L'] (map b)
  toMapNil (P : ProdWord S') : P ⟶[L'] (ProdWord.nil.map f)
  toMapNil_unique {P : ProdWord S'} (a b : P ⟶[L'] (ProdWord.nil.map f)) : a = b
  fst (P Q : ProdWord S) : ((P.prod Q).map f) ⟶[L'] (P.map f)
  snd (P Q : ProdWord S) : ((P.prod Q).map f) ⟶[L'] (Q.map f)
  lift {T : ProdWord S'} {P Q : ProdWord S}
    (a : T ⟶[L'] P.map f) (b : T ⟶[L'] Q.map f) : T ⟶[L'] (P.prod Q).map f
  lift_fst {T : ProdWord S'} {P Q : ProdWord S}
    (a : T ⟶[L'] P.map f) (b : T ⟶[L'] Q.map f) : lift a b ≫[L'] fst P Q = a
  lift_snd {T : ProdWord S'} {P Q : ProdWord S}
    (a : T ⟶[L'] P.map f) (b : T ⟶[L'] Q.map f) : lift a b ≫[L'] snd P Q = b
  lift_unique {T : ProdWord S'} {P Q : ProdWord S}
    {a b : T ⟶[L'] (P.prod Q).map f} :
    a ≫[L'] fst _ _ = b ≫[L'] fst _ _ →
    a ≫[L'] snd _ _ = b ≫[L'] snd _ _ →
    a = b

scoped notation:26 L " ⥤[" f "]" L':27 => MorphismAlong f L L' -- type as \func

attribute [simp]
  MorphismAlong.map_id
  MorphismAlong.map_comp
  MorphismAlong.lift_fst
  MorphismAlong.lift_snd

attribute [simp]
  MorphismAlong.lift_unique
  MorphismAlong.toMapNil_unique

structure Iso (a b : ProdWord S) where
  hom : a ⟶[L] b
  inv : b ⟶[L] a
  hom_inv_id : hom ≫[L] inv = 𝟙[L] a
  inv_hom_id : inv ≫[L] hom = 𝟙[L] b

scoped notation:10 A " ≅[" L "]" B:11 => LawvereTheory.Iso L A B

@[simps]
def mapNilIso {S : Type u} {S' : Type u'} {f : S → S'}
    {L : LawvereTheory.{v} S} {L' : LawvereTheory.{v'} S'}
    (F : L ⥤[f] L') :
    ProdWord.nil.map f ≅[L'] ProdWord.nil where
  hom := L'.toNil _
  inv := F.toMapNil _
  hom_inv_id := F.toMapNil_unique _ _
  inv_hom_id := L'.toNil_unique _ _

@[simps]
def mapProdIso {S : Type u} {S' : Type u'} {f : S → S'}
    {L : LawvereTheory.{v} S} {L' : LawvereTheory.{v'} S'}
    (F : L ⥤[f] L') (P Q : ProdWord S) :
    (P.prod Q).map f ≅[L'] (P.map f).prod (Q.map f) where
  hom := L'.lift (F.fst _ _) (F.snd _ _)
  inv := F.lift (L'.fst _ _) (L'.snd _ _)
  hom_inv_id := by
    apply F.lift_unique
    · rw [L'.id_comp, L'.assoc, F.lift_fst, L'.lift_fst]
    · rw [L'.id_comp, L'.assoc, F.lift_snd, L'.lift_snd]
  inv_hom_id := by
    apply L'.lift_unique
    · rw [L'.id_comp, L'.assoc, L'.lift_fst, F.lift_fst]
    · rw [L'.id_comp, L'.assoc, L'.lift_snd, F.lift_snd]

end LawvereTheory
