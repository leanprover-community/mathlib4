/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Products.Bifunctor

#align_import category_theory.functor.currying from "leanprover-community/mathlib"@"369525b73f229ccd76a6ec0e0e0bf2be57599768"

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
      map := fun {X} {Y} f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
      map_comp := fun f g => by
        simp only [prod_comp_fst, prod_comp_snd, Functor.map_comp, NatTrans.comp_app,
          Category.assoc]
        slice_lhs 2 3 => rw [← NatTrans.naturality]
        rw [Category.assoc] }
  map T :=
    { app := fun X => (T.app X.1).app X.2
      naturality := fun X Y f => by
        simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.assoc, Functor.map_id,
          Functor.map_comp, NatTrans.id_app, NatTrans.comp_app]
        slice_lhs 2 3 => rw [NatTrans.naturality]
        slice_lhs 1 2 => rw [← NatTrans.comp_app, NatTrans.naturality, NatTrans.comp_app]
        rw [Category.assoc] }
#align category_theory.uncurry CategoryTheory.uncurry

/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E
    where
  obj X :=
    { obj := fun Y => F.obj (X, Y)
      map := fun g => F.map (𝟙 X, g)
      map_id := fun Y => by simp only [F.map_id]; rw [←prod_id]; exact F.map_id ⟨X,Y⟩
      map_comp := fun f g => by simp [←F.map_comp]}
  map f :=
    { app := fun Y => F.map (f, 𝟙 Y)
      naturality := fun {Y} {Y'} g => by simp [←F.map_comp] }
  map_id := fun X => by ext Y; exact F.map_id _
  map_comp := fun f g => by ext Y; dsimp; simp [←F.map_comp]
#align category_theory.curry_obj CategoryTheory.curryObj

/-- The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
@[simps! obj_obj_obj obj_obj_map obj_map_app map_app_app]
def curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E where
  obj F := curryObj F
  map T :=
    { app := fun X =>
        { app := fun Y => T.app (X, Y)
          naturality := fun Y Y' g => by
            dsimp [curryObj]
            rw [NatTrans.naturality] }
      naturality := fun X X' f => by
        ext; dsimp [curryObj]
        rw [NatTrans.naturality] }
#align category_theory.curry CategoryTheory.curry

-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of functor categories given by currying/uncurrying.
-/
@[simps!]
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E :=
  Equivalence.mk uncurry curry
    (NatIso.ofComponents fun F =>
        NatIso.ofComponents fun X => NatIso.ofComponents fun Y => Iso.refl _)
    (NatIso.ofComponents fun F => NatIso.ofComponents (fun X => eqToIso (by simp))
      (by intros X Y f; cases X; cases Y; cases f; dsimp at *; rw [←F.map_comp]; simp ))
#align category_theory.currying CategoryTheory.currying

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps!]
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (Prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents fun d => NatIso.ofComponents fun c => Iso.refl _
#align category_theory.flip_iso_curry_swap_uncurry CategoryTheory.flipIsoCurrySwapUncurry

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps!]
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ Prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents fun p => Iso.refl _
#align category_theory.uncurry_obj_flip CategoryTheory.uncurryObjFlip

variable (B C D E)

/-- A version of `CategoryTheory.whiskeringRight` for bifunctors, obtained by uncurrying,
applying `whiskeringRight` and currying back
-/
@[simps!]
def whiskeringRight₂ : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E :=
  uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry
#align category_theory.whiskering_right₂ CategoryTheory.whiskeringRight₂

namespace Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]

lemma uncurry_obj_curry_obj (F : C₁ × C₂ ⥤ D) : uncurry.obj (curry.obj F) = F := by
  refine' Functor.ext _ _
  . simp
  . intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
    dsimp
    rw [← F.map_comp, Category.id_comp, Category.comp_id]
    aesop_cat

lemma curry_obj_injective {F₁ F₂ : C₁ × C₂ ⥤ D} (h : curry.obj F₁ = curry.obj F₂) : F₁ = F₂ := by
  rw [← uncurry_obj_curry_obj F₁, ← uncurry_obj_curry_obj F₂, h]

lemma curry_obj_uncurry_obj (F : C₁ ⥤ C₂ ⥤ D) : curry.obj (uncurry.obj F) = F := by
  refine' Functor.ext _ _
  . intro X₁
    exact Functor.ext (by simp) (by simp)
  . intros X₁ X₂ f
    aesop_cat

lemma uncurry_obj_injective {F₁ F₂ : C₁ ⥤ C₂ ⥤ D}
  (h : uncurry.obj F₁ = uncurry.obj F₂) : F₁ = F₂ := by
  rw [← curry_obj_uncurry_obj F₁, ← curry_obj_uncurry_obj F₂, h]

lemma flip_flip (F : C₁ ⥤ C₂ ⥤ D) : F.flip.flip = F := rfl

lemma flip_injective {F₁ F₂ : C₁ ⥤ C₂ ⥤ D} (h : F₁.flip = F₂.flip) : F₁ = F₂ := by
  rw [← flip_flip F₁, ← flip_flip F₂, h]

lemma uncurry_obj_curry_obj_flip_flip {C₁' : Type u₄} {C₂' : Type u₅}
  [Category.{v₄} C₁'] [Category.{v₅} C₂']
  (F₁ : C₁ ⥤ C₁') (F₂ : C₂ ⥤ C₂') (G : C₁' × C₂' ⥤ D) :
    uncurry.obj (F₂ ⋙ (F₁ ⋙ curry.obj G).flip).flip = (F₁.prod F₂) ⋙ G := by
  refine' Functor.ext _ _
  . simp
  . intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp]
    aesop_cat

lemma uncurry_obj_curry_obj_flip_flip' {C₁' : Type u₄} {C₂' : Type u₅}
  [Category.{v₄} C₁'] [Category.{v₅} C₂']
  (F₁ : C₁ ⥤ C₁') (F₂ : C₂ ⥤ C₂') (G : C₁' × C₂' ⥤ D) :
    uncurry.obj (F₁ ⋙ (F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂) ⋙ G := by
  refine' Functor.ext _ _
  . simp
  . intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp]
    aesop_cat

end Functor

end CategoryTheory
