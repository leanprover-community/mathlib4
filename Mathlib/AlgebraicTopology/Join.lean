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

def tripleFunSndO : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifierSnd.Elements ⥤ Type u) :=
  tripleFunSnd' ⋙ ((whiskeringLeft _ _ _).obj assocSndToWithInitialWithInitial)
  ⋙ ((whiskeringRight _ _ _).obj tensorType)

def tripleFunSndX' :  (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    ((WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ
    × (WithInitial SimplexCategory)ᵒᵖ   ⥤ Type u × Type u × Type u) where
  obj S := S.1.prod  (S.2.1.prod S.2.2)
  map η := (NatTrans.prod η.1 (NatTrans.prod η.2.1 η.2.2))

def tripleFunSnd : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifierSnd.Elements ⥤ Type u) :=
  tripleFunSndX'  ⋙ ((whiskeringRight _ _ _).obj ((𝟭 (Type u)).prod tensorType ⋙ tensorType))
   ⋙ ((whiskeringLeft _ _ _).obj assocSndTo3WithInitial)

def tripleFun1 : (SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial) ⥤
    (assocClassifier1.Elements ⥤ Type u) :=
  tripleFunSndX'  ⋙ ((whiskeringRight _ _ _).obj
  ((prod.associativity _ _ _).inverse ⋙ (tensorType.prod (𝟭 (Type u)) ⋙ tensorType)))
   ⋙ ((whiskeringLeft _ _ _).obj assocFstTo3WithInitial)


inductive joinType' (S T : SSet.FromWithInitial) (X : (WithInitial SimplexCategory)ᵒᵖ)  where
  | comp : (i : joinClassifying.obj X) → (pairFun.obj (S, T)).obj (joinLiftObj i) → joinType' S T X

lemma joinType'.ext {S T : SSet.FromWithInitial} (X : (WithInitial SimplexCategory)ᵒᵖ)
    (s t : joinType' S T X) (h1 : s.1 = t.1)
    (h2 : ((pairFun.obj (S, T)).map (joinLiftObjEqIso h1).hom) s.2 = t.2 ) :
      s = t := by
  match s, t with
  | ⟨s1, s2⟩, ⟨t1, t2⟩ =>
    congr
    simp at h1
    subst h1
    rw [joinLiftObjEqIso_refl] at h2
    simp at h2
    simp only [heq_eq_eq]
    exact h2


@[simp]
def joinTypeMap' (S T : SSet.FromWithInitial)
    {X Y : (WithInitial SimplexCategory)ᵒᵖ } (f : X ⟶ Y)
    (s : joinType' S T X) : joinType' S T Y :=
    ⟨(joinClassifying.map f) s.1, ((pairFun.obj (S, T)).map (coCartesianLift f s.1)) s.2⟩

@[simp]
def join'' (S T : SSet.FromWithInitial) : SSet.FromWithInitial :=
    joinClassifying.liftFunc (pairFun.obj (S, T))

@[simp]
def assoc1 (S1 S2 S3 : SSet.FromWithInitial) : SSet.FromWithInitial :=
    assocClassifier1.liftFunc (tripleFun1.obj (S1, (S2,S3)))

@[simp]
def assocSnd (S1 S2 S3 : SSet.FromWithInitial) : SSet.FromWithInitial :=
    assocClassifierSnd.liftFunc (tripleFunSnd.obj (S1, (S2,S3)))

def join''Func : SSet.FromWithInitial × SSet.FromWithInitial ⥤ SSet.FromWithInitial :=
  pairFun ⋙ joinClassifying.liftFuncFunc

def assoc1Func : SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial
    ⥤ SSet.FromWithInitial :=
  tripleFun1 ⋙ assocClassifier1.liftFuncFunc

def assocSndFunc : SSet.FromWithInitial × SSet.FromWithInitial × SSet.FromWithInitial
    ⥤ SSet.FromWithInitial :=
  tripleFunSnd ⋙ assocClassifierSnd.liftFuncFunc

def iso1 : assocSndFunc ≅ tripleFunSnd ⋙  ⋙ assocClassifierfst.liftFuncFunc

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
    (join''Func.prod (𝟭 (SSet.FromWithInitial))) ⋙ join''Func :=
  NatIso.ofComponents (fun S => (join''_isoFst S.1 S.2.1 S.2.2).symm) (by aesop_cat)

def assoc2Iso : assocSndFunc ≅
    ((𝟭 (SSet.FromWithInitial)).prod join''Func ) ⋙ join''Func :=
  NatIso.ofComponents (fun S => (join''_isoSnd S.1 S.2.1 S.2.2).symm) (by aesop_cat)

@[simp]
def join' (S T : SSet.FromWithInitial) : SSet.FromWithInitial where
  obj X := joinType' S T X
  map f := joinTypeMap' S T f
  map_id Z := by
    ext a
    apply joinType'.ext
    swap
    simp only [joinClassifying_obj, joinTypeMap', types_id_apply, joinClassifying.map_id]
    simp only [types_id_apply, joinTypeMap', joinClassifying_map, coCartesianLift_id,
      joinClassifying_obj, id_eq, eq_mpr_eq_cast]
    rw [← types_comp_apply ((pairFun.obj _).map _) ((pairFun.obj _).map _)]
    rw [← (pairFun.obj _).map_comp, ← Iso.trans_hom, joinLiftObjEqIso_symm]
    rw [Iso.refl_hom, (pairFun.obj _).map_id]
    rfl
  map_comp {X Y Z} f g := by
    ext a
    apply joinType'.ext
    swap
    simp only [joinClassifying_obj, joinTypeMap', types_comp_apply, joinClassifying.map_comp]
    simp only [types_comp_apply, joinTypeMap']
    repeat rw [← types_comp_apply ((pairFun.obj _).map _) ((pairFun.obj _).map _),
     ← (pairFun.obj _).map_comp]
    apply congrFun
    apply congrArg
    exact coCartesianLift_comp _ _ _

/-- The join of two morphisms in `SSet.FromWithInitial`. -/
def joinMap' {S T : SSet.FromWithInitial × SSet.FromWithInitial} (η : S ⟶ T):
   join' S.1 S.2 ⟶ join' T.1 T.2 where
  app X := fun (s : joinType' S.1 S.2 X) =>
      joinType'.comp s.1 (((pairFun.map η).app ⟨X, s.1⟩) s.2)
  naturality {X Y} f := by
    ext a
    apply joinType'.ext
    swap
    congr
    simp only [join', joinClassifying_obj, types_comp_apply, joinTypeMap', joinClassifying_map]
    rw [← types_comp_apply ((pairFun.obj (S.1, S.2)).map _) ((pairFun.map η).app _) ]
    rw [(pairFun.map η).naturality]
    rw [joinLiftObjEqIso_refl]
    simp only [types_comp_apply, join', joinClassifying_obj, joinTypeMap', joinClassifying_map,
      Iso.refl_hom, FunctorToTypes.map_id_apply]
    rfl

/-- The functor from `SSet.FromWithInitial × SSet.FromWithInitial` to `SSet.FromWithInitial`
taking pairs of objects and morphisms to their join. -/
def joinFunc' : (SSet.FromWithInitial × SSet.FromWithInitial) ⥤ SSet.FromWithInitial where
  obj S := join' S.1 S.2
  map η := joinMap' η


/-- The functor `(WithInitial SimplexCategory × WithInitial SimplexCategory)ᵒᵖ ⥤ Type u`
induced by two objects `S` and `T` in `SSet.FromWithInitial` taking `(op X,op Z)`
to `S.obj (op X) × T.obj (op Z)`. -/
def pair (S T : SSet.FromWithInitial) :
    (WithInitial SimplexCategory × WithInitial SimplexCategory)ᵒᵖ ⥤ Type u :=
  (prodOpEquiv (WithInitial SimplexCategory)).functor ⋙ S.prod T ⋙
  {obj := (MonoidalCategory.tensor (Type u)).obj, map := fun f s => (f.1 s.1, f.2 s.2)}

/-- Given two morphisms in `SSet.FromWithInitial` the corresponding natural transformation
between paired objects. -/
def pairMap {S1 S2 T1 T2 : SSet.FromWithInitial} (η1 : S1 ⟶ T1) (η2 : S2 ⟶ T2) :
    pair S1 S2 ⟶ pair T1 T2 :=
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

@[simp]
lemma joinType_fst {S T : SSet.FromWithInitial} {X : WithInitial SimplexCategory}
    (i : Fin (Nat.succ (len X))) (s : (pair S T).obj (Opposite.op (Split.obj X i))) :
  (joinType.comp i s).1 = i := rfl

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

section Associator

def assocTypeMap1 {S T L : SSet.FromWithInitial} {X : WithInitial SimplexCategory}
    (s : (join (join S T) L).obj (Opposite.op X)) : (join S (join T L)).obj (Opposite.op X) :=
  joinType.comp
      (Split.inclSucc₁ s.2.1.1)
      (S.map (Split.swap₃ s.1 s.2.1.1).inv.op s.2.1.2.1,
      joinType.comp
        (Split.preimageInclSucc₂' s.1 s.2.1.1)
        (T.map ((Split.swap₁ s.1 s.2.1.1).inv.op) s.2.1.2.2,
           L.map (Split.swap₂ s.1 s.2.1.1).inv.op s.2.2))

def assocTypeMap2 {S T L : SSet.FromWithInitial} {X : WithInitial SimplexCategory}
    (s : (join S (join T L)).obj (Opposite.op X)) : (join (join S T) L).obj (Opposite.op X)  :=
  joinType.comp
      (Split.inclSucc₂ s.2.2.1)
      (joinType.comp
        (Split.preimageInclSucc₁' s.1 s.2.2.1)
        (S.map (Split.swap₃' s.1 s.2.2.1).inv.op s.2.1,
          T.map (Split.swap₁' s.1 s.2.2.1).inv.op s.2.2.2.1),
      (L.map (Split.swap₂' s.1 s.2.2.1).inv.op s.2.2.2.2))

lemma left_inv_assocType (S T L : SSet.FromWithInitial) (X : WithInitial SimplexCategory) :
    Function.LeftInverse (@assocTypeMap2 S T L X) (@assocTypeMap1 S T L X)  := fun s => by
  refine joinType_ext _ _ (Split.preimageInclSucc₂'_inclSucc₂ s.1 s.2.1.1) ?_
  simp [pair, assocTypeMap1, assocTypeMap2]
  apply Prod.ext
  simp [join, joinTypeMap]
  refine joinType_ext _ _ ?_ ?_
  simp
  rw [Split.indexEqToIso, Split.sourceValue_of_iso_inv, Fin.eq_iff_veq]
  rfl
  simp [pair]
  apply Prod.ext
  all_goals
    simp
    repeat rw [← types_comp_apply (Prefunctor.map _ _) (Prefunctor.map _ _), ← Functor.map_comp]
    repeat rw [← Category.assoc]
    rw [← op_comp, ← Iso.trans_inv]
    try rw [Split.swap₁_swap₁']
    try rw [Split.swap₂_swap₂']
    try rw [Split.swap₃_swap₃']
    try refine @Eq.trans _ _ (S.map (𝟙 (_)).op s.2.1.2.1) _ ?_ (by rw [op_id, S.map_id]; rfl)
    try refine @Eq.trans _ _ (T.map (𝟙 _).op s.2.1.2.2) _ ?_ (by rw [op_id, T.map_id]; rfl)
    try refine @Eq.trans _ _ (L.map (𝟙 (_)).op s.2.2) _ ?_ (by rw [op_id, L.map_id]; rfl)
    apply congrFun
    repeat rw [← op_comp]
    repeat apply congrArg
    simp [Split.indexEqToIso]
    apply hom_eq_if_toOrderHom_eq
    apply OrderHom.ext
    funext a
    repeat rw [toOrderHom_comp]
  · rw [Split.map_lenIso_inv_fst]
    simp [toOrderHomIso_apply_inv]
    rw [@toOrderHom_id (Split.obj (Split.obj X s.1).1 s.2.1.1).1]
    rfl
  · rw [Split.map_lenIso_inv_snd]
    simp [toOrderHomIso_apply_inv]
  · simp [toOrderHomIso_apply_inv]

def assocTypeEquiv (S T L : SSet.FromWithInitial) (X : WithInitial SimplexCategory) :
    (join (join S T) L).obj (Opposite.op X) ≃ (join S (join T L)).obj (Opposite.op X)  where
  toFun := assocTypeMap1
  invFun := assocTypeMap2
  left_inv := left_inv_assocType S T L X
  right_inv := fun s => by
    refine joinType_ext _ _ (Split.preimageInclSucc₁'_inclSucc₁ s.1 s.2.2.1) ?_
    simp [pair, assocTypeMap1, assocTypeMap2]
    apply Prod.ext
    swap
    simp [join, joinTypeMap]
    refine joinType_ext _ _ ?_ ?_
    simp
    rw [Split.indexEqToIso, Split.sourceValue_of_iso_inv, Fin.eq_iff_veq]
    simp [Split.preimageInclSucc₂', Split.preimageInclSucc₂, Split.len_obj₁, Split.inclSucc₂,
    Split.inclSucc₁, Split.preimageInclSucc₁', Split.preimageInclSucc₁]
    simp [pair]
    apply Prod.ext
    all_goals
      simp
      repeat rw [← types_comp_apply (Prefunctor.map _ _) (Prefunctor.map _ _), ← Functor.map_comp]
      repeat rw [← Category.assoc]
      rw [← op_comp, ← Iso.trans_inv]
      try rw [Split.swap₁'_swap₁]
      try rw [Split.swap₂'_swap₂]
      try rw [Split.swap₃'_swap₃]
      try refine @Eq.trans _ _ (S.map (𝟙 (_)).op s.2.1) _ ?_ (by rw [op_id, S.map_id]; rfl)
      try refine @Eq.trans _ _ (T.map (𝟙 _).op s.2.2.2.1) _ ?_ (by rw [op_id, T.map_id]; rfl)
      try refine @Eq.trans _ _ (L.map (𝟙 (_)).op  s.2.2.2.2) _ ?_ (by rw [op_id, L.map_id]; rfl)
      apply congrFun
      repeat rw [← op_comp]
      repeat apply congrArg
      simp [Split.indexEqToIso]
      apply hom_eq_if_toOrderHom_eq
      apply OrderHom.ext
      funext a
      repeat rw [toOrderHom_comp]
    · rw [Split.map_lenIso_inv_fst]
      simp [toOrderHomIso_apply_inv]
    · rw [Split.map_lenIso_inv_snd]
      simp [toOrderHomIso_apply_inv]
    · simp [toOrderHomIso_apply_inv]
      rw [@toOrderHom_id (Split.obj X s.1).1]
      rfl

lemma assocTypeNat (S T L : SSet.FromWithInitial) {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) :
    (assocTypeEquiv S T L X).toFun ∘ (join (join S T) L).map f.op =
    (join S (join T L)).map f.op ∘ (assocTypeEquiv S T L Y).toFun  := by
  funext s
  simp [assocTypeEquiv, assocTypeMap1]
  match s with
  | joinType.comp i (s1, s2) =>
  match s1 with
  | joinType.comp p s3 =>
  refine joinType_ext _ _ (Split.sourceValue_map₁ f i p) ?_
  simp only [pair, prod_Hom, MonoidalCategory.tensor_obj, Opposite.unop_op, prodOpEquiv_functor_obj,
    Functor.prod_obj, joinType_fst, Functor.comp_obj, Functor.comp_map, prodOpEquiv_functor_map,
    Quiver.Hom.unop_op, Functor.prod_map]
  apply Prod.ext
  swap
  simp [join, joinTypeMap]
  refine joinType_ext _ _ ?_ ?_
  simp only [pair, prod_Hom, MonoidalCategory.tensor_obj, Functor.comp_map, prodOpEquiv_functor_obj,
    Opposite.unop_op, prodOpEquiv_functor_map, Quiver.Hom.unop_op, Functor.prod_obj,
    Functor.prod_map, joinTypeMap, joinType_fst, Split.indexEqToIso._eq_1,
    Split.sourceValue_of_iso_inv]
  -- simp
  sorry
  simp [pair]
  apply Prod.ext
  all_goals
    simp [join, joinTypeMap, pair]
    repeat rw [← types_comp_apply (Prefunctor.map _ _) (Prefunctor.map _ _), ← Functor.map_comp]
    apply congrFun
    repeat rw [← op_comp]
    repeat apply congrArg
    simp [Split.indexEqToIso]
    apply hom_eq_if_toOrderHom_eq
    apply OrderHom.ext
    funext a
    repeat rw [toOrderHom_comp]
  · rw [Fin.eq_iff_veq]
    simp [toOrderHomIso_apply_inv]
    simp [Split.toOrderHom_snd_apply, Split.toOrderHom_fst_apply, Split.incl₂, Split.incl₁,
    toOrderHomIso_apply_inv, Split.inclSucc₁]
    apply congrFun
    repeat apply congrArg
    rw [Fin.eq_iff_veq]
    simp













end Associator

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

lemma joinStandardSimplexTypeEquiv_nat (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X)))
    {Δop1 Δop2 : (WithInitial SimplexCategory)ᵒᵖ} (f : Δop1 ⟶  Δop2) :
    (Equiv.toIso (joinStandardSimplexTypeEquiv X i Δop2).symm).hom ∘ (Split.homMap X i f.unop)
    = (joinStandardSimplex X i).map f ∘
    (Equiv.toIso (joinStandardSimplexTypeEquiv X i Δop1).symm).hom := by
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
