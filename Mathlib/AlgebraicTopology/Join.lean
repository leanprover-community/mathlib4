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

/-- The functor `(WithInitial SimplexCategory × WithInitial SimplexCategory)ᵒᵖ ⥤ Type u`
induced by two objects `S` and `T` in `SSet.FromWithInitial` taking `(op X,op Z)`
to `S.obj (op X) × T.obj (op Z)`. -/
def pair (S T : SSet.FromWithInitial) :
    (WithInitial SimplexCategory × WithInitial SimplexCategory)ᵒᵖ ⥤ Type u :=
  (prodOpEquiv (WithInitial SimplexCategory)).functor ⋙ S.prod T ⋙
  {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)}

/-- Given two morphisms in `SSet.FromWithInitial` the corresponding natural transformation
between paired objects. -/
def pairMap {S1 S2 T1 T2 : SSet.FromWithInitial}
    (η1 : S1 ⟶ T1) (η2 : S2 ⟶ T2) : pair S1 S2 ⟶ pair T1 T2 :=
  whiskerRight
    (whiskerLeft
      (prodOpEquiv (WithInitial SimplexCategory)).functor
      (NatTrans.prod η1 η2))
    {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)}

/-- Given an `X` in `WithInitial SimplexCategory` and `S`, `T` in `SSet.FromWithInitial`, the
disjoint union of types `S.obj (op Z) × T.obj (op Y)` such that `Z` and `Y` split `X` -/
inductive joinType (S T : SSet.FromWithInitial)
    (X : WithInitial SimplexCategory)  where
  | comp : (i : Fin (Nat.succ (len X)))
    → (pair S T).obj (Opposite.op (Split.obj X i))
    → joinType S T X

lemma joinType_ext {S T : SSet.FromWithInitial}
    {X : WithInitial SimplexCategory}
    (s t : joinType S T X) (h1 : s.1 = t.1)
    (h : (pair S T).map ((Split.indexEqToIso h1).inv).op s.2 =t.2):
    s = t := by
  match s, t with
  | joinType.comp i s, joinType.comp j t =>
    simp at h1
    subst h1
    congr
    rw [Split.indexEqToIso_refl] at h
    simp only [Iso.refl_inv, op_id, FunctorToTypes.map_id_apply] at h
    exact h

/-- Given a morphism `f : X ⟶ Y` in `SSet.FromWithInitial`, a map from `joinType S T Y` to
`joinType S T X`. -/
def joinTypeMap (S T : SSet.FromWithInitial)
    {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (s : joinType S T Y) : joinType S T X :=
  match s with
  | joinType.comp i s =>
    joinType.comp (Split.sourceValue f i) ((pair S T).map (Split.map f i).op s)

/-- The join of two objects in `SSet.FromWithInitial`. -/
def join (S T : SSet.FromWithInitial) : SSet.FromWithInitial where
  obj X := joinType S T (Opposite.unop X)
  map f := joinTypeMap S T f.unop
  map_id Z := by
    match Z with
    | ⟨Z⟩ =>
    funext s
    simp
    refine joinType_ext _ _ (Split.sourceValue_of_id s.1) ?_
    simp [joinTypeMap]
    rw [← types_comp_apply ((pair S T).map _) ((pair S T).map _),
      ← (pair S T).map_comp, ← op_comp]
    rw [ Split.map_id s.1, op_id, FunctorToTypes.map_id_apply]
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | ⟨X⟩, ⟨Y⟩, ⟨Z⟩, ⟨f⟩, ⟨g⟩ =>
    funext s
    symm
    refine joinType_ext ((joinTypeMap S T g ∘  joinTypeMap S T f) s) (joinTypeMap S T (g ≫ f) s)
     (Split.sourceValue_of_comp g f s.1) ?_
    simp [joinTypeMap]
    repeat rw [← types_comp_apply ((pair S T).map _) ((pair S T).map _),
    ← (pair S T).map_comp, ← op_comp]
    apply congrFun
    repeat apply congrArg
    rw [Category.assoc, Split.map_comp g f s.1]

/-- The join of two morphisms in `SSet.FromWithInitial`. -/
def joinMap {S1 T1 S2 T2: SSet.FromWithInitial} (η : S1 ⟶ S2)
    (ε : T1 ⟶ T2) : join S1 T1 ⟶ join S2 T2 where
  app X := fun (s : joinType S1 T1 (Opposite.unop X)) =>
      joinType.comp s.1
        ((pairMap η ε).app (Opposite.op (Split.obj (Opposite.unop X) s.1)) s.2)
  naturality {X Y} f := by
    match X, Y, f with
    | ⟨X⟩, ⟨Y⟩, ⟨f⟩ =>
    funext s
    apply joinType_ext _ _ (by rfl) ?_
    change (pair S2 T2).map _ (((pair S1 T1).map _ ≫ (pairMap η ε).app _) _) =_
    erw [(pairMap η ε).naturality, Split.indexEqToIso_refl, op_id, (pair S2 T2).map_id]
    rfl

/-- The functor from `SSet.FromWithInitial × SSet.FromWithInitial` to `SSet.FromWithInitial`
taking pairs of objects and morphisms to their join. -/
def joinFunc : (SSet.FromWithInitial × SSet.FromWithInitial) ⥤ SSet.FromWithInitial where
  obj S := join S.1 S.2
  map η := joinMap η.1 η.2

section standardSimplex
open SSet.FromWithInitial
/-- The join of standard simplicies in `WithInitial SimplexCategory`-/
def joinStandardSimplex (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    SSet.FromWithInitial :=
  ((standardSimplex.prod standardSimplex) ⋙ joinFunc).obj (Split.obj X i)

/-- An equivalence between the type `(joinStandardSimplex X i).obj Δop` and the type
`Split.hom Δop.unop X i`. -/
def joinStandardSimplexTypeEquiv (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    (Δop : (WithInitial SimplexCategory)ᵒᵖ) :
    (joinStandardSimplex X i).obj Δop ≃ Split.hom Δop.unop X i where
  toFun s :=
    Split.hom.split s.1
      ((standardSimplex.objEquiv (Split.obj X i).1
         (Opposite.op (Split.obj Δop.unop s.1).1)).toFun s.2.1,
       (standardSimplex.objEquiv (Split.obj X i).2
          (Opposite.op (Split.obj Δop.unop s.1).2)).toFun s.2.2)
  invFun s :=
    joinType.comp s.1
      ((standardSimplex.objEquiv (Split.obj X i).1
         (Opposite.op (Split.obj Δop.unop s.1).1)).invFun s.2.1,
       (standardSimplex.objEquiv (Split.obj X i).2
          (Opposite.op (Split.obj Δop.unop s.1).2)).invFun s.2.2)
  left_inv := by
    aesop_cat
  right_inv := by
    aesop_cat

lemma joinStandardSimplexTypeEquiv_nat (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    {Δop1 Δop2 : (WithInitial SimplexCategory)ᵒᵖ} (f : Δop1 ⟶  Δop2) :
    (Equiv.toIso (joinStandardSimplexTypeEquiv X i Δop2).symm).hom ∘ (Split.homMap X i f.unop)
    = (joinStandardSimplex X i).map f ∘ (Equiv.toIso (joinStandardSimplexTypeEquiv X i Δop1).symm).hom := by
  rfl

lemma standardSimplexType_nat (X : WithInitial SimplexCategory)
    {Δop1 Δop2 : (WithInitial SimplexCategory)ᵒᵖ} (f : Δop1 ⟶  Δop2) :
    ((Equiv.toIso (standardSimplex.objEquiv X Δop2)).hom ∘ (standardSimplex.obj X).map f) =
    (CategoryStruct.comp f.unop ) ∘ (Equiv.toIso (standardSimplex.objEquiv X Δop1)).hom := by
  rfl

/-- An equivalance between
` (standardSimplex.obj X).obj Δop` and `(joinStandardSimplexEquiv X i).obj Δop` -/
def joinStandardSimplexEquivStandard (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    (Δop : (WithInitial SimplexCategory)ᵒᵖ) :
    (standardSimplex.obj X).obj Δop ≅ (joinStandardSimplex X i).obj Δop  :=
  Equiv.toIso (standardSimplex.objEquiv X Δop) ≪≫
  Equiv.toIso (Split.splitJoinUnitEquiv X Δop.unop i).symm ≪≫
  Equiv.toIso (joinStandardSimplexTypeEquiv X i Δop).symm

/-- An equivalence in  `WithInitial SimplexCategory` between the standard simplex
`standardSimplex.obj X` and for any `i` in `Fin (Nat.succ (len X))` the object
`joinStandardSimplex X i `. -/
def joinStandardSimplexEquiv (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    standardSimplex.obj X ≅ joinStandardSimplex X i :=  by
  refine NatIso.ofComponents (joinStandardSimplexEquivStandard X i) ?_
  intro Z1 Z2 f
  change (
    (Equiv.toIso (joinStandardSimplexTypeEquiv X i Z2).symm).hom
    ∘ (Equiv.toIso (Split.splitJoinUnitEquiv X Z2.unop i).symm ).hom
    ∘ (Equiv.toIso (standardSimplex.objEquiv X Z2)).hom
    ∘ (standardSimplex.toPrefunctor.obj X).map f
    )  =_
  rw [standardSimplexType_nat]
  rw [← Function.comp.assoc, ← Function.comp.assoc]
  nth_rewrite 2 [Function.comp.assoc]
  rw [Split.splitJoinUnitEquiv_naturality_equiv, ← Function.comp.assoc,
    joinStandardSimplexTypeEquiv_nat]
  rfl

end standardSimplex
end FromWithInitial
end SSet
