/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.ChosenFiniteProducts

universe v u

inductive ProdWord (S : Type u) : Type u where
  | of : S → ProdWord S
  | prod : ProdWord S → ProdWord S → ProdWord S
  | nil : ProdWord S

open CategoryTheory Limits

structure LawvereTheory (S : Type u) where
  isCat : Category.{v} (ProdWord S)
  fst' (X Y : ProdWord S) : X.prod Y ⟶ X
  snd' (X Y : ProdWord S) : X.prod Y ⟶ Y
  lift' {X Y T : ProdWord S} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X.prod Y
  lift'_fst' {X Y T : ProdWord S} (f : T ⟶ X) (g : T ⟶ Y) :
    lift' f g ≫ fst' _ _ = f
  lift'_snd' {X Y T : ProdWord S} (f : T ⟶ X) (g : T ⟶ Y) :
    lift' f g ≫ snd' _ _ = g
  hom_ext_prod {X Y T : ProdWord S} {f g : T ⟶ X.prod Y} :
    f ≫ fst' _ _ = g ≫ fst' _ _ → f ≫ snd' _ _ = g ≫ snd' _ _ → f = g
  toNil (X : ProdWord S) : X ⟶ .nil
  hom_ext_nil {X : ProdWord S} (f g : X ⟶ .nil) : f = g

namespace LawvereTheory

variable {S : Type u} (T : LawvereTheory.{v} S)

structure Carrier (T : LawvereTheory.{v} S) where
  as : ProdWord S

instance : CoeSort (LawvereTheory.{v} S) (Type u) where
  coe T := T.Carrier

instance : Category T :=
  letI : Category (ProdWord S) := T.isCat
  InducedCategory.category fun x => x.as

instance : ChosenFiniteProducts T where
  product X Y := {
    cone := BinaryFan.mk (T.fst' X.as Y.as) (T.snd' X.as Y.as)
    isLimit := BinaryFan.isLimitMk
      (fun S => T.lift' S.fst S.snd)
      (fun S => T.lift'_fst' _ _)
      (fun S => T.lift'_snd' _ _)
      (fun S m hfst hsnd => T.hom_ext_prod (by simpa [T.lift'_fst']) (by simpa [T.lift'_snd']))
  }
  terminal := {
    cone := {
      pt := .mk .nil
      π := Discrete.natTrans fun x => x.as.elim
    }
    isLimit := {
      lift := fun S => T.toNil _
      uniq := fun _ _ _ => T.hom_ext_nil _ _
    }
  }

open MonoidalCategory ChosenFiniteProducts

lemma as_tensor (X Y : T) : (X ⊗ Y).as = X.as.prod Y.as := rfl

lemma as_unit : (𝟙_ T).as = .nil := rfl

structure Algebra (C : Type*) [Category.{v} C] extends T ⥤ C where
  preservesLimitPair (X Y : T) : PreservesLimit.{0} (pair X Y) toFunctor
  preservesLimitEmpty : PreservesLimit.{0} (Functor.empty _) toFunctor

namespace Algebra

variable {T}
variable {C : Type*} [Category C] (A : T.Algebra C)

def lift {Q : C} {X Y : T} (f : Q ⟶ A.obj X) (g : Q ⟶ A.obj Y) : Q ⟶ A.obj (X ⊗ Y) :=
  A.preservesLimitPair X Y
    |>.preserves (ChosenFiniteProducts.product X Y).isLimit
    |>.lift {
      pt := Q
      π := {
        app := fun t =>
          match t with
          | .mk .left => f
          | .mk .right => g
        naturality := by rintro ⟨_|_⟩ ⟨_|_⟩ ⟨_|_⟩ <;> aesop_cat
      }
    }

@[reassoc (attr := simp)]
lemma lift_map_fst {Q : C} {X Y : T} (f : Q ⟶ A.obj X) (g : Q ⟶ A.obj Y) :
    A.lift f g ≫ A.map (fst _ _) = f :=
  (A.preservesLimitPair X Y).preserves _ |>.fac _ _

@[reassoc (attr := simp)]
lemma lift_map_snd {Q : C} {X Y : T} (f : Q ⟶ A.obj X) (g : Q ⟶ A.obj Y) :
    A.lift f g ≫ A.map (snd _ _) = g :=
  (A.preservesLimitPair X Y).preserves _ |>.fac _ _

lemma hom_ext_objTensor {Q : C} {X Y : T} (f g : Q ⟶ A.obj (X ⊗ Y)) :
    f ≫ A.map (fst _ _) = g ≫ A.map (fst _ _) →
    f ≫ A.map (snd _ _) = g ≫ A.map (snd _ _) →
    f = g := fun h1 h2 =>
  (A.preservesLimitPair X Y).preserves (ChosenFiniteProducts.product X Y).isLimit
    |>.hom_ext fun j => match j with
      | .mk .left => h1
      | .mk .right => h2

set_option pp.universes true in
def toObjUnit (Q : C) : Q ⟶ A.obj (𝟙_ _) :=
  A.preservesLimitEmpty.preserves ChosenFiniteProducts.terminal.isLimit |>.lift
    ⟨_, Discrete.natTrans fun i => i.as.elim⟩

def hom_ext_objUnit {Q : C} (f g : Q ⟶ A.obj (𝟙_ _)) : f = g :=
  A.preservesLimitEmpty.preserves
    (ChosenFiniteProducts.terminal (C := T)).isLimit |>.hom_ext
    fun j => j.as.elim

instance (Q : C) : Unique (Q ⟶ A.obj (𝟙_ _)) where
  default := A.toObjUnit _
  uniq _ := A.hom_ext_objUnit _ _

end Algebra

end LawvereTheory
