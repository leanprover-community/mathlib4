/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.Prod.Basic
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Curry and uncurry, as functors.

We define `curry : ((C × D) ⥤ E) ⥤ (C ⥤ (D ⥤ E))` and `uncurry : (C ⥤ (D ⥤ E)) ⥤ ((C × D) ⥤ E)`,
and verify that they provide an equivalence of categories
`currying : (C ⥤ (D ⥤ E)) ≌ ((C × D) ⥤ E)`.

This is used in `CategoryTheory.Category.Cat.CartesianClosed` to equip the category of small
categories `Cat.{u, u}` with a Cartesian closed structure.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

open scoped Prod

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E] {H : Type u₅} [Category.{v₅} H]

/-- The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
@[simps]
def uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E where
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
        simp only [Category.assoc]
        slice_lhs 2 3 => rw [NatTrans.naturality]
        slice_lhs 1 2 => rw [← NatTrans.comp_app, NatTrans.naturality, NatTrans.comp_app]
        rw [Category.assoc] }

/-- The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curryObj (F : C × D ⥤ E) : C ⥤ D ⥤ E where
  obj X :=
    { obj := fun Y => F.obj (X, Y)
      map := fun g => F.map (𝟙 X ×ₘ g)
      map_id := fun Y => by rw [← prod_id]; exact F.map_id ⟨X,Y⟩
      map_comp := fun f g => by simp [← F.map_comp] }
  map f :=
    { app := fun Y => F.map (f ×ₘ 𝟙 Y)
      naturality := fun {Y} {Y'} g => by simp [← F.map_comp] }
  map_id := fun X => by ext Y; exact F.map_id _
  map_comp := fun f g => by ext Y; simp [← F.map_comp]

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

-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of functor categories given by currying/uncurrying.
-/
@[simps!]
def currying : C ⥤ D ⥤ E ≌ C × D ⥤ E where
  functor := uncurry
  inverse := curry
  unitIso := NatIso.ofComponents (fun _ ↦ NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)))
  counitIso := NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      dsimp at f₁ f₂ ⊢
      simp only [← F.map_comp, prod_comp, Category.comp_id, Category.id_comp]))

/-- The equivalence of functor categories given by flipping. -/
@[simps!]
def flipping : C ⥤ D ⥤ E ≌ D ⥤ C ⥤ E where
  functor := flipFunctor _ _ _
  inverse := flipFunctor _ _ _
  unitIso := NatIso.ofComponents (fun _ ↦ NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ ↦ NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)))

/-- The functor `uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E` is fully faithful. -/
def fullyFaithfulUncurry : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).FullyFaithful :=
  currying.fullyFaithfulFunctor

/-- The functor `curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E` is fully faithful. -/
def fullyFaithfulCurry : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).FullyFaithful :=
  currying.fullyFaithfulInverse

instance : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).Full :=
  fullyFaithfulCurry.full

instance : (curry : (C × D ⥤ E) ⥤ C ⥤ D ⥤ E).Faithful :=
  fullyFaithfulCurry.faithful

instance : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).Full :=
  fullyFaithfulUncurry.full

instance : (uncurry : (C ⥤ D ⥤ E) ⥤ C × D ⥤ E).Faithful :=
  fullyFaithfulUncurry.faithful

/-- Given functors `F₁ : C ⥤ D`, `F₂ : C' ⥤ D'` and `G : D × D' ⥤ E`, this is the isomorphism
between `curry.obj ((F₁.prod F₂).comp G)` and
`F₁ ⋙ curry.obj G ⋙ (whiskeringLeft C' D' E).obj F₂` in the category `C ⥤ C' ⥤ E`. -/
@[simps!]
def curryObjProdComp {C' D' : Type*} [Category* C'] [Category* D']
    (F₁ : C ⥤ D) (F₂ : C' ⥤ D') (G : D × D' ⥤ E) :
    curry.obj ((F₁.prod F₂).comp G) ≅
      F₁ ⋙ curry.obj G ⋙ (whiskeringLeft C' D' E).obj F₂ :=
  NatIso.ofComponents (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦ Iso.refl _))

/-- `F.flip` is isomorphic to uncurrying `F`, swapping the variables, and currying. -/
@[simps!]
def flipIsoCurrySwapUncurry (F : C ⥤ D ⥤ E) : F.flip ≅ curry.obj (Prod.swap _ _ ⋙ uncurry.obj F) :=
  NatIso.ofComponents fun d => NatIso.ofComponents fun _ => Iso.refl _

/-- The uncurrying of `F.flip` is isomorphic to
swapping the factors followed by the uncurrying of `F`. -/
@[simps!]
def uncurryObjFlip (F : C ⥤ D ⥤ E) : uncurry.obj F.flip ≅ Prod.swap _ _ ⋙ uncurry.obj F :=
  NatIso.ofComponents fun _ => Iso.refl _

variable (B C D E)

/-- A version of `CategoryTheory.whiskeringRight` for bifunctors, obtained by uncurrying,
applying `whiskeringRight` and currying back
-/
@[simps!]
def whiskeringRight₂ : (C ⥤ D ⥤ E) ⥤ (B ⥤ C) ⥤ (B ⥤ D) ⥤ B ⥤ E :=
  uncurry ⋙
    whiskeringRight _ _ _ ⋙ (whiskeringLeft _ _ _).obj (prodFunctorToFunctorProd _ _ _) ⋙ curry

variable {B C D E}

lemma uncurry_obj_curry_obj (F : B × C ⥤ D) : uncurry.obj (curry.obj F) = F :=
  Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [← F.map_comp, Category.id_comp, Category.comp_id, prod_comp])

lemma curry_obj_injective {F₁ F₂ : C × D ⥤ E} (h : curry.obj F₁ = curry.obj F₂) :
    F₁ = F₂ := by
  rw [← uncurry_obj_curry_obj F₁, ← uncurry_obj_curry_obj F₂, h]

lemma curry_obj_uncurry_obj (F : B ⥤ C ⥤ D) : curry.obj (uncurry.obj F) = F :=
  Functor.ext (fun _ => Functor.ext (by simp) (by simp)) (by cat_disch)

lemma uncurry_obj_injective {F₁ F₂ : B ⥤ C ⥤ D} (h : uncurry.obj F₁ = uncurry.obj F₂) :
    F₁ = F₂ := by
  rw [← curry_obj_uncurry_obj F₁, ← curry_obj_uncurry_obj F₂, h]

lemma flip_flip (F : B ⥤ C ⥤ D) : F.flip.flip = F := rfl

lemma flip_injective {F₁ F₂ : B ⥤ C ⥤ D} (h : F₁.flip = F₂.flip) :
    F₁ = F₂ := by
  rw [← flip_flip F₁, ← flip_flip F₂, h]

lemma uncurry_obj_curry_obj_flip_flip (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) :
    uncurry.obj (F₂ ⋙ (F₁ ⋙ curry.obj G).flip).flip = (F₁.prod F₂) ⋙ G :=
  Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

lemma uncurry_obj_curry_obj_flip_flip' (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) :
    uncurry.obj (F₁ ⋙ (F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂) ⋙ G :=
  Functor.ext (by simp) (fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩ => by
    dsimp
    simp only [Category.id_comp, Category.comp_id, ← G.map_comp, prod_comp])

/-- Natural isomorphism witnessing `comp_flip_uncurry_eq`. -/
@[simps!]
def compFlipUncurryIso (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip ≅ (𝟭 C).prod F ⋙ uncurry.obj G.flip := .refl _

lemma comp_flip_uncurry_eq (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip = (𝟭 C).prod F ⋙ uncurry.obj G.flip := rfl

/-- Natural isomorphism witnessing `comp_flip_curry_eq`. -/
@[simps!]
def curryObjCompIso (F : C × B ⥤ D) (G : D ⥤ E) :
    (curry.obj (F ⋙ G)).flip ≅ (curry.obj F).flip ⋙ (whiskeringRight _ _ _).obj G := .refl _

lemma curry_obj_comp_flip (F : C × B ⥤ D) (G : D ⥤ E) :
    (curry.obj (F ⋙ G)).flip =
      (curry.obj F).flip ⋙ (whiskeringRight _ _ _).obj G := rfl

/-- The equivalence of types of bifunctors giving by flipping the arguments. -/
@[simps!]
def flippingEquiv : C ⥤ D ⥤ E ≃ D ⥤ C ⥤ E where
  toFun F := F.flip
  invFun F := F.flip
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence of types of bifunctors given by currying. -/
@[simps!]
def curryingEquiv : C ⥤ D ⥤ E ≃ C × D ⥤ E where
  toFun F := uncurry.obj F
  invFun G := curry.obj G
  left_inv := curry_obj_uncurry_obj
  right_inv := uncurry_obj_curry_obj

/-- The flipped equivalence of types of bifunctors given by currying. -/
@[simps!]
def curryingFlipEquiv : D ⥤ C ⥤ E ≃ C × D ⥤ E :=
  flippingEquiv.trans curryingEquiv

end Functor

end CategoryTheory
