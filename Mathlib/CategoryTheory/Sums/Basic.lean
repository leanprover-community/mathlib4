/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.sums.basic
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EqToHom

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/


namespace CategoryTheory

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
open Sum

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

/-- `sum C D` gives the direct sum of two categories.
-/
instance sum : Category.{v₁} (Sum C D)
    where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => X ⟶ Y
    | inl X, inr Y => PEmpty
    | inr X, inl Y => PEmpty
    | inr X, inr Y => X ⟶ Y
  id X :=
    match X with
    | inl X => 𝟙 X
    | inr X => 𝟙 X
  comp X Y Z f g :=
    match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g => f ≫ g
    | inr X, inr Y, inr Z, f, g => f ≫ g
#align category_theory.sum CategoryTheory.sum

@[simp]
theorem sum_comp_inl {P Q R : C} (f : (inl P : Sum C D) ⟶ inl Q) (g : (inl Q : Sum C D) ⟶ inl R) :
    @CategoryStruct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
      @CategoryStruct.comp _ _ (inl P) (inl Q) (inl R) (f : P ⟶ Q) (g : Q ⟶ R) :=
  rfl
#align category_theory.sum_comp_inl CategoryTheory.sum_comp_inl

@[simp]
theorem sum_comp_inr {P Q R : D} (f : (inr P : Sum C D) ⟶ inr Q) (g : (inr Q : Sum C D) ⟶ inr R) :
    @CategoryStruct.comp _ _ P Q R (f : P ⟶ Q) (g : Q ⟶ R) =
      @CategoryStruct.comp _ _ (inr P) (inr Q) (inr R) (f : P ⟶ Q) (g : Q ⟶ R) :=
  rfl
#align category_theory.sum_comp_inr CategoryTheory.sum_comp_inr

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps]
def inl_ : C ⥤ Sum C D where
  obj X := inl X
  map X Y f := f
#align category_theory.sum.inl_ CategoryTheory.sum.inl_

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps]
def inr_ : D ⥤ Sum C D where
  obj X := inr X
  map X Y f := f
#align category_theory.sum.inr_ CategoryTheory.sum.inr_

/-- The functor exchanging two direct summand categories. -/
def swap : Sum C D ⥤ Sum D C
    where
  obj X :=
    match X with
    | inl X => inr X
    | inr X => inl X
  map X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => f
    | inr X, inr Y, f => f
#align category_theory.sum.swap CategoryTheory.sum.swap

@[simp]
theorem swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X :=
  rfl
#align category_theory.sum.swap_obj_inl CategoryTheory.sum.swap_obj_inl

@[simp]
theorem swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X :=
  rfl
#align category_theory.sum.swap_obj_inr CategoryTheory.sum.swap_obj_inr

@[simp]
theorem swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f :=
  rfl
#align category_theory.sum.swap_map_inl CategoryTheory.sum.swap_map_inl

@[simp]
theorem swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f :=
  rfl
#align category_theory.sum.swap_map_inr CategoryTheory.sum.swap_map_inr

namespace Swap

/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
def equivalence : Sum C D ≌ Sum D C :=
  Equivalence.mk (swap C D) (swap D C)
    (NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by tidy))
    (NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by tidy))
#align category_theory.sum.swap.equivalence CategoryTheory.sum.swap.equivalence

instance isEquivalence : IsEquivalence (swap C D) :=
  (by infer_instance : IsEquivalence (equivalence C D).Functor)
#align category_theory.sum.swap.is_equivalence CategoryTheory.sum.swap.isEquivalence

/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (Sum C D) :=
  (equivalence C D).unitIso.symm
#align category_theory.sum.swap.symmetry CategoryTheory.sum.swap.symmetry

end Swap

end Sum

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₁} [Category.{v₁} B] {C : Type u₁}
  [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]

namespace Functor

/-- The sum of two functors. -/
def sum (F : A ⥤ B) (G : C ⥤ D) : Sum A C ⥤ Sum B D
    where
  obj X :=
    match X with
    | inl X => inl (F.obj X)
    | inr X => inr (G.obj X)
  map X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => F.map f
    | inr X, inr Y, f => G.map f
  map_id' X := by cases X <;> unfold_aux; erw [F.map_id]; rfl; erw [G.map_id]; rfl
  map_comp' X Y Z f g :=
    match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g => by
      unfold_aux
      erw [F.map_comp]
      rfl
    | inr X, inr Y, inr Z, f, g => by
      unfold_aux
      erw [G.map_comp]
      rfl
#align category_theory.functor.sum CategoryTheory.Functor.sum

@[simp]
theorem sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.Sum G).obj (inl a) = inl (F.obj a) :=
  rfl
#align category_theory.functor.sum_obj_inl CategoryTheory.Functor.sum_obj_inl

@[simp]
theorem sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.Sum G).obj (inr c) = inr (G.obj c) :=
  rfl
#align category_theory.functor.sum_obj_inr CategoryTheory.Functor.sum_obj_inr

@[simp]
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : inl a ⟶ inl a') :
    (F.Sum G).map f = F.map f :=
  rfl
#align category_theory.functor.sum_map_inl CategoryTheory.Functor.sum_map_inl

@[simp]
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : inr c ⟶ inr c') :
    (F.Sum G).map f = G.map f :=
  rfl
#align category_theory.functor.sum_map_inr CategoryTheory.Functor.sum_map_inr

end Functor

namespace NatTrans

/-- The sum of two natural transformations. -/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.Sum H ⟶ G.Sum I
    where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality' X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => by unfold_aux; erw [α.naturality]; rfl
    | inr X, inr Y, f => by unfold_aux; erw [β.naturality]; rfl
#align category_theory.nat_trans.sum CategoryTheory.NatTrans.sum

@[simp]
theorem sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum α β).app (inl a) = α.app a :=
  rfl
#align category_theory.nat_trans.sum_app_inl CategoryTheory.NatTrans.sum_app_inl

@[simp]
theorem sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
    (sum α β).app (inr c) = β.app c :=
  rfl
#align category_theory.nat_trans.sum_app_inr CategoryTheory.NatTrans.sum_app_inr

end NatTrans

end CategoryTheory

