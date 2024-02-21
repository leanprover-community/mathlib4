/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.WithTerminal

universe v u
open CategoryTheory CategoryTheory.Limits
open Simplicial
open WithInitial
open SimplexCategory.WithInitial

def joinType  (S T : (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u ) {n : ℕ}
    (i : Fin (Nat.succ n)) : Type u :=
  S.obj (Opposite.op (mk i.val)) × T.obj (Opposite.op (mk i.rev.val))

lemma joinType.Iso {n : ℕ} {i j: Fin (Nat.succ n)}
    (S T : (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u ) (hij : i = j) :
    joinType S T i  = joinType S T j := by
  rw [hij]

inductive JoinStruct (S T : (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u)
    (n : ℕ)  where
  | comp : (i : Fin (Nat.succ n)) → joinType S T i → JoinStruct S T n

lemma JoinStruct.ext {S T : (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u} {n : ℕ}
    (s t : JoinStruct S T n) (h1 : s.1 = t.1)
    (h41 : S.map (homMk ((Fin.castIso ((fin_eq_to_val h1).symm)) : Fin t.1.val →o Fin s.1.val)).op s.2.1 =t.2.1)
    (h42 : T.map (homMk ((Fin.castIso ((fin_eq_to_rev h1).symm)) : Fin t.1.rev →o Fin s.1.rev.val)).op s.2.2 =t.2.2) :
    s = t := by
  match s, t with
  |  JoinStruct.comp i s, JoinStruct.comp j t =>
    simp at h1
    subst h1
    congr
    change S.map (homMk (OrderHom.id :  Fin i.val →o Fin i.val)).op s.1 = _ at h41
    change T.map (homMk (OrderHom.id :  Fin i.rev.val →o Fin i.rev.val)).op s.2 = _ at h42
    rw [homMk_id, op_id, S.map_id]  at h41
    rw [homMk_id, op_id, T.map_id]  at h42
    simp at h41 h42
    change (s.1, s.2) = (t.1, t.2)
    rw [h41, h42]


def joinMap (S T :  (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u)
    {Z1 Z2 : WithInitial SimplexCategory} (f : Z1 ⟶ Z2)
    (s : JoinStruct S T (len Z2)) : JoinStruct S T (len Z1) :=
  match s with
  | JoinStruct.comp i s =>
    JoinStruct.comp
      (nat (preimageInitialSegmentObj f i))
      (S.map (map₁ f i).op s.1, T.map (revMap₁ f i).op s.2)

def join (S T : (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u) :
    (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u where
  obj X := JoinStruct S T (len (Opposite.unop X))
  map f := joinMap S T f.unop
  map_id := by
    intro Z
    cases Z
    rename_i Z
    funext s
    refine JoinStruct.ext (joinMap S T (𝟙 Z) s) s ?_ ?_ ?_
    · exact nat_id s.1 (preimageInitialSegmentObj (𝟙 Z) s.1) (by rfl)
    · simp [joinMap]
      rw [← types_comp_apply (S.map _) (S.map _),← S.map_comp, ← op_comp]
      nth_rewrite 3 [show s.2.1 = S.map (𝟙  ((mk s.1))).op s.2.1 by
        rw [op_id, S.map_id, types_id_apply]]
      apply congrFun
      repeat apply congrArg
      exact map₁_id s.1
    · simp [joinMap]
      rw [← types_comp_apply (T.map _) (T.map _),← T.map_comp, ← op_comp]
      nth_rewrite 3 [show s.2.2 = T.map (𝟙  ((mk s.1.rev))).op s.2.2 by
        rw [op_id, T.map_id, types_id_apply]]
      apply congrFun
      repeat apply congrArg
      exact revMap₁_id s.1
  map_comp := by
    intro X Y Z f g
    cases X
    cases Y
    cases Z
    cases f
    cases g
    rename_i X Y Z g f
    funext s
    symm
    refine JoinStruct.ext ((joinMap S T f ∘  joinMap S T g) s) (joinMap S T (f ≫ g) s) ?_ ?_ ?_
    · exact nat_comp f g s.1
    · simp [joinMap]
      repeat rw [← types_comp_apply (S.map _) (S.map _),← S.map_comp, ← op_comp]
      apply congrFun
      repeat apply congrArg
      symm
      simp [Category.assoc]
      exact map₁_comp f g s.1
    · simp [joinMap]
      repeat rw [← types_comp_apply (T.map _) (T.map _),← T.map_comp, ← op_comp]
      apply congrFun
      repeat apply congrArg
      symm
      simp [Category.assoc]
      exact revMap₁_comp f g s.1

def join.map {S1 T1 S2 T2: (WithInitial SimplexCategory)ᵒᵖ ⥤  Type u} (η : S1 ⟶ S2)
    (ε : T1 ⟶ T2) : join S1 T1 ⟶ join S2 T2 where
  app X := fun (s : JoinStruct S1 T1 (len (Opposite.unop X))) =>
      JoinStruct.comp s.1 ((η.app (Opposite.op (mk s.1.val))) s.2.1,
         (ε.app (Opposite.op (mk s.1.rev.val))) s.2.2 )
  naturality := by
    intro X Y f
    cases X
    cases Y
    cases f
    rename_i X Y f
    funext s
    apply JoinStruct.ext _ _ ?_ ?_ ?_
    · rfl
    · change S2.map (homMk OrderHom.id).op ( η.app _  (S1.map ((map₁ f s.1).op) s.2.1)) =
          (η.app (Opposite.op (mk ↑s.1)) ≫ S2.map ((map₁ f s.1).op)) ( s.2.1)
      rw [homMk_id, op_id, S2.map_id]
      rw [← η.naturality]
      rfl
    · change T2.map (homMk OrderHom.id).op ( ε.app _  (T1.map ((revMap₁ f s.1).op) s.2.2)) =
          ( ε.app (Opposite.op (mk ↑s.1.rev)) ≫ T2.map ((revMap₁ f s.1).op)) (s.2.2)
      rw [homMk_id, op_id, T2.map_id]
      rw [← ε.naturality]
      rfl

def join.func :
    (((WithInitial SimplexCategory)ᵒᵖ ⥤  Type u) × ((WithInitial SimplexCategory)ᵒᵖ ⥤  Type u))
    ⥤  ((WithInitial SimplexCategory)ᵒᵖ ⥤  Type u) where
  obj S := join S.1 S.2
  map η := join.map η.1 η.2

def join.fun_terminal :  ((WithTerminal (SimplexCategory)ᵒᵖ ⥤  Type u) × (WithTerminal (SimplexCategory)ᵒᵖ ⥤  Type u))
    ⥤  ((WithInitial SimplexCategory)ᵒᵖ ⥤  Type u)  := sorry

def join.fun_augmented : SSet.Augmented × SSet.Augmented ⥤ SSet.Augmented := by
