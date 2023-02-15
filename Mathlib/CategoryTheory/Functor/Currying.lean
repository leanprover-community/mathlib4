/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.functor.currying
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Products.Bifunctor

/-!
# Curry and uncurry, as functors.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

-/


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

/-- The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
@[simps]
def uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E
    where
  obj F :=
    { obj := fun X => (F.obj X.1).obj X.2
      map := fun X Y f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp' := fun X Y Z f g =>
        by
        simp only [prod_comp_fst, prod_comp_snd, functor.map_comp, nat_trans.comp_app,
          category.assoc]
        slice_lhs 2 3 => rw [← nat_trans.naturality]
        rw [category.assoc] }
  map F G T :=
    { app := fun X => (T.app X.1).app X.2
      naturality' := fun X Y f =>
        by
        simp only [prod_comp_fst, prod_comp_snd, category.comp_id, category.assoc, Functor.map_id,
          functor.map_comp, nat_trans.id_app, nat_trans.comp_app]
        slice_lhs 2 3 => rw [nat_trans.naturality]
        slice_lhs 1 2 => rw [← nat_trans.comp_app, nat_trans.naturality, nat_trans.comp_app]
        rw [category.assoc] }
#align category_theory.uncurry CategoryTheory.uncurry

/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E
    where
  obj X :=
    { obj := fun Y => F.obj (X, Y)
      map := fun Y Y' g => F.map (𝟙 X, g) }
  map X X' f := { app := fun Y => F.map (f, 𝟙 Y) }
#align category_theory.curry_obj CategoryTheory.curryObj

/-- The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
@[simps obj_obj_obj obj_obj_map obj_map_app map_app_app]
def curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  obj F := curryObj F
  map F G T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality' := fun Y Y' g => by
            dsimp [curry_obj]
            rw [nat_trans.naturality] }
      naturality' := fun X X' f => by
        ext; dsimp [curry_obj]
        rw [nat_trans.naturality] }
#align category_theory.curry CategoryTheory.curry

-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of functor categories given by currying/uncurrying.
-/
@[simps]
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E :=
  Equivalence.mk uncurry curry
    (NatIso.ofComponents
      (fun F =>
        NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => Iso.refl _) (by tidy))
          (by tidy))
      (by tidy))
    (NatIso.ofComponents (fun F => NatIso.ofComponents (fun X => eqToIso (by simp)) (by tidy))
      (by tidy))
#align category_theory.currying CategoryTheory.currying

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps]
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (Prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents (fun d => NatIso.ofComponents (fun c => Iso.refl _) (by tidy)) (by tidy)
#align category_theory.flip_iso_curry_swap_uncurry CategoryTheory.flipIsoCurrySwapUncurry

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps]
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ Prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents (fun p => Iso.refl _) (by tidy)
#align category_theory.uncurry_obj_flip CategoryTheory.uncurryObjFlip

variable (B C D E)

/-- A version of `category_theory.whiskering_right` for bifunctors, obtained by uncurrying,
applying `whiskering_right` and currying back
-/
@[simps]
def whiskeringRight₂ : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E :=
  uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry
#align category_theory.whiskering_right₂ CategoryTheory.whiskeringRight₂

end CategoryTheory

