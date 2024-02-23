/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.WithTerminal
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic

universe v u
open CategoryTheory CategoryTheory.Limits
open Simplicial
open WithInitial
open SimplexCategory.WithInitial

--Computable version of tensor functor. Really just want to work with (
-- (MonoidalCategory.tensor (Type u))
def tensorTypes : Type u × Type u ⥤  Type u where
  obj := (MonoidalCategory.tensor (Type u)).obj
  map {X Y} f := fun s => (f.1 s.1, f.2 s.2)

lemma tensorEquiv : (MonoidalCategory.tensor (Type u)) = tensorTypes := rfl

def joinPair (S T : SSet.FromWithInitial) :
    (WithInitial SimplexCategory × WithInitial SimplexCategory)ᵒᵖ ⥤ Type u :=
  (prodOpEquiv (WithInitial SimplexCategory)).functor ⋙ S.prod T ⋙ tensorTypes

def joinNatTrans {S1 S2 T1 T2 : SSet.FromWithInitial}
    (η1 : S1 ⟶ T1) (η2 : S2 ⟶ T2) : (joinPair S1 S2) ⟶ (joinPair T1 T2) :=
  whiskerRight
    (whiskerLeft
      (prodOpEquiv (WithInitial SimplexCategory)).functor
      (NatTrans.prod η1 η2))
    tensorTypes

inductive JoinStruct (S T : SSet.FromWithInitial)
    (X : WithInitial SimplexCategory)  where
  | comp : (i : Fin (Nat.succ (len X)))
    → (joinPair S T).obj (Opposite.op (Split.obj X i))
    → JoinStruct S T X

def joinMap (S T : SSet.FromWithInitial)
    {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (s : JoinStruct S T Y) : JoinStruct S T X :=
  match s with
  | JoinStruct.comp i s =>
    JoinStruct.comp (Split.sourceValue f i) ((joinPair S T).map (Split.map f i).op s)

lemma JoinStruct.ext {S T : SSet.FromWithInitial}
    {X : WithInitial SimplexCategory}
    (s t : JoinStruct S T X) (h1 : s.1 = t.1)
    (h : (joinPair S T).map ((Split.objEquiv h1).inv).op s.2 =t.2):
    s = t := by
  match s, t with
  | JoinStruct.comp i s, JoinStruct.comp j t =>
    simp at h1
    subst h1
    congr
    rw [Split.objEquiv_refl] at h
    simp only [Iso.refl_inv, op_id, FunctorToTypes.map_id_apply] at h
    exact h

def join (S T : SSet.FromWithInitial) : SSet.FromWithInitial where
  obj X := JoinStruct S T (Opposite.unop X)
  map f := joinMap S T f.unop
  map_id Z := by
    match Z with
    | ⟨Z⟩ =>
    funext s
    simp
    refine JoinStruct.ext _ _ (Split.sourceValue_id s.1) ?_
    simp [joinMap]
    rw [← types_comp_apply ((joinPair S T).map _) ((joinPair S T).map _),
      ← (joinPair S T).map_comp, ← op_comp]
    rw [ Split.map_id s.1, op_id, FunctorToTypes.map_id_apply]
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | ⟨X⟩, ⟨Y⟩, ⟨Z⟩, ⟨f⟩, ⟨g⟩ =>
    funext s
    symm
    refine JoinStruct.ext ((joinMap S T g ∘  joinMap S T f) s) (joinMap S T (g ≫ f) s)
     (Split.sourceValue_comp g f s.1) ?_
    simp [joinMap]
    repeat rw [← types_comp_apply ((joinPair S T).map _) ((joinPair S T).map _),
    ← (joinPair S T).map_comp, ← op_comp]
    apply congrFun
    repeat apply congrArg
    rw [Category.assoc, Split.map_comp g f s.1]

def join.map {S1 T1 S2 T2: SSet.FromWithInitial} (η : S1 ⟶ S2)
    (ε : T1 ⟶ T2) : join S1 T1 ⟶ join S2 T2 where
  app X := fun (s : JoinStruct S1 T1 (Opposite.unop X)) =>
      JoinStruct.comp s.1
        ((joinNatTrans η ε).app (Opposite.op (Split.obj (Opposite.unop X) s.1)) s.2)
  naturality {X Y} f := by
    match X, Y, f with
    | ⟨X⟩, ⟨Y⟩, ⟨f⟩ =>
    funext s
    apply JoinStruct.ext _ _ (by rfl) ?_
    change (joinPair S2 T2).map _ (((joinPair S1 T1).map _ ≫ (joinNatTrans η ε).app _) _) =_
    erw [(joinNatTrans η ε).naturality, Split.objEquiv_refl, op_id, (joinPair S2 T2).map_id]
    rfl

def join.func : (SSet.FromWithInitial × SSet.FromWithInitial) ⥤ SSet.FromWithInitial where
  obj S := join S.1 S.2
  map η := join.map η.1 η.2

open SSet.FromWithInitial in
def joinStandardSimplex (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    standardSimplex.obj X ≅
     ((standardSimplex.prod standardSimplex) ⋙ join.func).obj (Split.obj X i) where
  hom := {
    app := fun Δop => fun f => by
      let f' := standardSimplex.objEquiv X Δop f
      let p := Split.sourceValue f' i
      let Δ1Δ2 :=  ((prodOpEquiv (WithInitial SimplexCategory)).functor.obj
         (Opposite.op (Split.obj Δop.unop p)))
      let m1 : (standardSimplex.obj (Split.obj X i).1).obj Δ1Δ2.1 :=
         (standardSimplex.objEquiv (Split.obj X i).1 Δ1Δ2.1).invFun (Split.map f' i ).1
      let m2 : (standardSimplex.obj (Split.obj X i).2).obj Δ1Δ2.2 :=
         (standardSimplex.objEquiv (Split.obj X i).2 Δ1Δ2.2).invFun (Split.map f' i ).2
      exact JoinStruct.comp p (m1,m2)
    naturality := by
      intro Y Z f
      funext s
      refine JoinStruct.ext _ _ ?_ ?_
      sorry
  }
  inv := {
    app := fun Δop => fun f => by
      let p := f.1
      let Δ1Δ2 :=  ((prodOpEquiv (WithInitial SimplexCategory)).functor.obj
         (Opposite.op (Split.obj Δop.unop f.1)))
      let m1 : (standardSimplex.obj (Split.obj X i).1).obj Δ1Δ2.1 := f.2.1
      let f1 : (Opposite.unop Δ1Δ2.1) ⟶ (Split.obj X i).1 :=
         (standardSimplex.objEquiv (Split.obj X i).1 Δ1Δ2.1).toFun f.2.1
      let f2 : (Opposite.unop Δ1Δ2.2) ⟶ (Split.obj X i).2 :=
         (standardSimplex.objEquiv (Split.obj X i).2 Δ1Δ2.2).toFun f.2.2
      let o1 := SimplexCategory.WithInitial.join.obj ((Opposite.unop Δ1Δ2.1), (Opposite.unop Δ1Δ2.2))
      let o2 := SimplexCategory.WithInitial.join.obj ((Split.obj X i).1, (Split.obj X i).2)
      let f : o1 ⟶ o2 := SimplexCategory.WithInitial.join.map (f1,f2)
      let f' : Δop.unop ⟶ X := sorry



      sorry

  }
