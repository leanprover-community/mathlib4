/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplexCategoryWithInitial
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.WithTerminal
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-! # The join of simplicial sets

We construct the join of augmented simplicial sets defined as contravariant functors from
`WithInitial SimplexCategory`.

We show that the join of two augmented standard simplicies is equivalent to a augmented standard
simplex.

## ToDo

1. Show that the join forms a monoidal structure on augmented simplicial sets.
2. Define the join of simplicial sets.
3. Show that the join of standard simplicies is equivalent to a standard simplex.
4. Show that the join defines a monoidal structure on simplicial sets.

-/

universe v u
open CategoryTheory CategoryTheory.Limits
open Simplicial
open WithInitial
open SimplexCategory.WithInitial

namespace SSet
namespace FromWithInitial


def pairFun : (SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (joinClassifying.Elements ⥤ Type u) where
  obj S := toWithInitialWithInitial.rightOp ⋙
    (prodOpEquiv (WithInitial SimplexCategory)).functor ⋙ S.1.prod S.2 ⋙
    {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)}
  map η := whiskerRight
    (whiskerLeft
      (toWithInitialWithInitial.rightOp ⋙ (prodOpEquiv (WithInitial SimplexCategory)).functor)
      (NatTrans.prod η.1 η.2))
    {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)}

def tripleFun1' :  (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    ( joinClassifying.Elements × (WithInitial SimplexCategory)ᵒᵖ ⥤ Type u × Type u ) where
  obj S := (pairFun.obj (S.1, S.2.1)).prod S.2.2
  map η := (NatTrans.prod (pairFun.map (η.1, η.2.1)) η.2.2)

def tripleFun1_o : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifier1.Elements ⥤ Type u) :=
  tripleFun1' ⋙ ((whiskeringLeft _ _ _).obj assoc1ToWithInitialWithInitial)
  ⋙ ((whiskeringRight _ _ _).obj
  {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)})

def tripleFunSnd' :  (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    ( (WithInitial SimplexCategory)ᵒᵖ × joinClassifying.Elements  ⥤ Type u × Type u ) where
  obj S := S.1.prod (pairFun.obj S.2)
  map η := (NatTrans.prod η.1 (pairFun.map  η.2))

def tensorType : Type u × Type u ⥤ Type u :=
    {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)}

def tensorTypeAssocComp (S : Type u × Type u × Type u ) :
   ((prod.associativity _ _ _).inverse ⋙ (tensorType.prod (𝟭 (Type u)) ⋙ tensorType)).obj S
    ≅ ((𝟭 (Type u)).prod tensorType ⋙ tensorType).obj S where
  hom := fun s => ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
  inv := fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩

def tensorTypeAssoc  :
   ((prod.associativity _ _ _).inverse ⋙ (tensorType.prod (𝟭 (Type u)) ⋙ tensorType))
    ≅ ((𝟭 (Type u)).prod tensorType ⋙ tensorType) :=
  NatIso.ofComponents (tensorTypeAssocComp)

def tripleFunSndO : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifierSnd.Elements ⥤ Type u) :=
  tripleFunSnd' ⋙ ((whiskeringLeft _ _ _).obj assocSndToWithInitialWithInitial)
  ⋙ ((whiskeringRight _ _ _).obj tensorType)

def tripleFunSndX' :  (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    ((WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ
    × (WithInitial SimplexCategory)ᵒᵖ   ⥤ Type u × Type u × Type u) where
  obj S := S.1.prod  (S.2.1.prod S.2.2)
  map η := (NatTrans.prod η.1 (NatTrans.prod η.2.1 η.2.2))

def tripleFunSndT : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    ((WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ
    × (WithInitial SimplexCategory)ᵒᵖ  ⥤ Type u) :=
  tripleFunSndX'  ⋙ ((whiskeringRight _ _ _).obj ((𝟭 (Type u)).prod tensorType ⋙ tensorType))

def tripleFunFstT : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    ((WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ
    × (WithInitial SimplexCategory)ᵒᵖ  ⥤ Type u) :=
  tripleFunSndX'  ⋙ ((whiskeringRight _ _ _).obj
  ((prod.associativity _ _ _).inverse ⋙ (tensorType.prod (𝟭 (Type u)) ⋙ tensorType)))


def tripleFunTIso : tripleFunSndT ≅ tripleFunFstT :=
  ((whiskeringLeft _ _ _).obj tripleFunSndX').mapIso  (
  (whiskeringRight _ _ _).mapIso tensorTypeAssoc.symm)

def tripleFunSnd : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifierSnd.Elements ⥤ Type u) :=
  tripleFunSndT ⋙ ((whiskeringLeft _ _ _).obj assocSndTo3WithInitial)

def tripleFun1 : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifier1.Elements ⥤ Type u) :=
  tripleFunSndX'  ⋙ ((whiskeringRight _ _ _).obj
  ((prod.associativity _ _ _).inverse ⋙ (tensorType.prod (𝟭 (Type u)) ⋙ tensorType)))
   ⋙ ((whiskeringLeft _ _ _).obj assocFstTo3WithInitial)


@[simp]
def assoc1 (S1 S2 S3 : SSet.FromWithInitial) : SSet.FromWithInitial :=
    assocClassifier1.liftFunc (tripleFun1.obj (S1, (S2,S3)))

@[simp]
def assocSnd (S1 S2 S3 : SSet.FromWithInitial) : SSet.FromWithInitial :=
    assocClassifierSnd.liftFunc (tripleFunSnd.obj (S1, (S2,S3)))

def join : SSet.FromWithInitial × SSet.FromWithInitial ⥤ SSet.FromWithInitial :=
  pairFun ⋙ joinClassifying.liftFuncFunc

def assoc1Func : SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial
    ⥤ SSet.FromWithInitial :=
  tripleFun1 ⋙ assocClassifier1.liftFuncFunc

def assocSndFunc : SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial
    ⥤ SSet.FromWithInitial :=
  tripleFunSnd ⋙ assocClassifierSnd.liftFuncFunc

def assocIsoFunc : assocSndFunc ≅ assoc1Func :=
  ((whiskeringLeft _ _ _).obj tripleFunSnd).mapIso (CategoryOfElements.liftIsoFunc assocIso)
  ≪≫
  ((whiskeringRight _ _ _).obj assocClassifier1.liftFuncFunc).mapIso
  (NatIso.hcomp tripleFunTIso ((whiskeringLeft _ _ _).mapIso assocIsoWithInitial.symm))


@[simps!]
def join''_assoc1 (S1 S2 S3 : SSet.FromWithInitial) (X : (WithInitial SimplexCategory)ᵒᵖ) :
    (joinClassifying.liftFunc
     (pairFun.obj (joinClassifying.liftFunc (pairFun.obj (S1, S2)), S3))).obj X ≃
     (assocClassifier1.liftFunc (tripleFun1.obj (S1, (S2,S3)))).obj X where
  toFun := fun s => ⟨⟨s.1 , s.2.1.1⟩, ⟨s.2.1.2, s.2.2⟩⟩
  invFun := fun s => ⟨s.1.1, ⟨⟨s.1.2, s.2.1⟩, s.2.2 ⟩⟩
  left_inv s := by
    aesop
  right_inv s := by
    aesop

@[simps!]
def join''_assocSnd (S1 S2 S3 : SSet.FromWithInitial) (X : (WithInitial SimplexCategory)ᵒᵖ) :
    (joinClassifying.liftFunc
     (pairFun.obj (S1, joinClassifying.liftFunc (pairFun.obj (S2, S3))))).obj X ≃
     (assocClassifierSnd.liftFunc (tripleFunSnd.obj (S1, (S2,S3)))).obj X where
  toFun := fun s => ⟨⟨s.1 , s.2.2.1⟩, ⟨s.2.1, s.2.2.2⟩⟩
  invFun := fun s => ⟨s.1.1, ⟨s.2.1, ⟨s.1.2, s.2.2⟩ ⟩⟩
  left_inv s := by
    aesop
  right_inv s := by
    aesop

def join''_isoFst (S1 S2 S3 : SSet.FromWithInitial)  :
    (joinClassifying.liftFunc
     (pairFun.obj (joinClassifying.liftFunc (pairFun.obj (S1, S2)), S3))) ≅
     (assocClassifier1.liftFunc (tripleFun1.obj (S1, (S2,S3)))) :=
  NatIso.ofComponents (fun X => Equiv.toIso (join''_assoc1 S1 S2 S3 X)) (by
   intro X Y f
   simp_all only [Equiv.toIso_hom]
   rfl)

@[simps!]
def join''_isoSnd (S1 S2 S3 : SSet.FromWithInitial) :
    (joinClassifying.liftFunc
     (pairFun.obj (S1, joinClassifying.liftFunc (pairFun.obj (S2, S3))))) ≅
     (assocClassifierSnd.liftFunc (tripleFunSnd.obj (S1, (S2,S3)))) :=
  NatIso.ofComponents (fun X => Equiv.toIso (join''_assocSnd S1 S2 S3 X)) (by
   intro X Y f
   simp_all only [Equiv.toIso_hom]
   rfl)

def assoc1Iso : assoc1Func ≅ (prod.associativity _ _ _).inverse ⋙
    (join.prod (𝟭 (SSet.FromWithInitial))) ⋙ join :=
  NatIso.ofComponents (fun S => (join''_isoFst S.1 S.2.1 S.2.2).symm) (by aesop_cat)

def assoc2Iso : assocSndFunc ≅
    ((𝟭 (SSet.FromWithInitial)).prod join ) ⋙ join :=
  NatIso.ofComponents (fun S => (join''_isoSnd S.1 S.2.1 S.2.2).symm) (by aesop_cat)

def associativity :  (prod.associativity _ _ _).inverse ⋙
    (join.prod (𝟭 (SSet.FromWithInitial))) ⋙ join ≅
    ((𝟭 (SSet.FromWithInitial)).prod join ) ⋙ join :=
  assoc1Iso.symm ≪≫ assocIsoFunc.symm ≪≫ assoc2Iso
