/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brendan Murphy
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Data.Fin.Tuple.Curry

/-!
# Trifunctors obtained by composition of bifunctors and currying

Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, we define
the trifunctor `bifunctorComp₁₂ F₁₂ G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃`.

Similarly, given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, we define
the trifunctor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `(F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)`.

Finally we establish the ternary version of currying functors.
-/

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₄] [Category C₁₂] [Category C₂₃]

section

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)

/-- Auxiliary definition for `bifunctorComp₁₂`. -/
@[simps]
def bifunctorComp₁₂Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {X₃ Y₃} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

/-- Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps]
def bifunctorComp₁₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₁₂Obj F₁₂ G X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (G.map ((F₁₂.map φ).app X₂)).app X₃ }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃
        dsimp
        simp only [← NatTrans.comp_app, ← G.map_comp, NatTrans.naturality] }

end

section

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)

/-- Auxiliary definition for `bifunctorComp₂₃`. -/
@[simps]
def bifunctorComp₂₃Obj (X₁ : C₁) : C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)
      map := fun {X₃ Y₃} φ => (F.obj X₁).map ((G₂₃.obj X₂).map φ) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (F.obj X₁).map ((G₂₃.map φ).app X₃)
      naturality := fun {X₃ Y₃} φ => by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality] }

/-- Given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps]
def bifunctorComp₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₂₃Obj F G₂₃ X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (F.map φ).app ((G₂₃.obj X₂).obj X₃) } }

end


/-- The action on objects of a trifunctor. -/
def Functor.obj₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) (X : C₁) (Y : C₂) (Z : C₃) : C₄ :=
  ((F.obj X).obj Y).obj Z

/-- The component of a morphism of trifunctors at three objects. -/
def NatTrans.app₃ {F G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄} (α : NatTrans F G)
    (X : C₁) (Y : C₂) (Z : C₃) : F.obj₃ X Y Z ⟶ G.obj₃ X Y Z :=
  ((α.app X).app Y).app Z

/-- The action on morphisms of a trifunctor. -/
def Functor.map₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) {X X' : C₁} {Y Y' : C₂} {Z Z' : C₃}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    F.obj₃ X Y Z ⟶ F.obj₃ X' Y' Z' :=
  (F.map f).app₂ Y Z ≫ (F.obj X').map₂ g h

-- create projection simp lemmas even though this isn't a `{ .. }`.
/-- The equivalence of trifunctor categories given by currying/uncurrying. -/
@[simps!]
def currying₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ≌ C₁ × C₂ × C₃ ⥤ C₄ :=
  .trans (@currying C₁ _ C₂ _ (C₃ ⥤ C₄) _)
  $ .trans (@currying (C₁ × C₂) _ C₃ _ C₄ _)
  $ (prod.associativity C₁ C₂ C₃).congrLeft (E := C₄)
-- why is this so slow???

/-- The ternary uncurrying functor, taking a functor `C₁ ⥤ (C₂ ⥤ (C₃ ⥤ C₄))` and
producing a functor `(C₁ × C₂ × C₃) ⥤ C₄`.-/
@[simps!] def uncurry₃ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ × C₂ × C₃ ⥤ C₄ := currying₃.functor

/-- The ternary currying functor, taking a functor `(C₁ × C₂ × C₃) ⥤ C₄` and
producing a functor `C₁ ⥤ (C₂ ⥤ (C₃ ⥤ C₄))`.
-/
@[simps!] def curry₃ : (C₁ × C₂ × C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ := currying₃.inverse

lemma uncurry₃_obj_obj_eq_uncurry₃_obj₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) :
    (uncurry₃.obj F).obj = F.obj₃.uncurry₃ := rfl

lemma uncurry₃_obj_map_eq_uncurry₃_map₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄) {X Y : C₁ × C₂ × C₃} :
    ((uncurry₃.obj F).map : (X ⟶ Y) → _) = F.map₃.uncurry₃ :=
  funext $ fun _ => Category.assoc _ _ _

lemma curry₃_obj_obj₃_eq_curry₃_obj (F : C₁ × C₂ × C₃ ⥤ C₄) :
    (curry₃.obj F).obj₃ = F.obj.curry₃ := rfl

lemma curry₃_obj_map₃_eq_curry₃_map (F : C₁ × C₂ × C₃ ⥤ C₄) {X X' Y Y' Z Z'} :
    (curry₃.obj F).map₃
    = (F.map (X := (X, Y, Z)) (Y := (X', Y', Z'))).curry₃ :=
  funext₃ $ fun _ _ _ =>
    Eq.trans (congrArg (_ ≫ .) (F.map_comp _ _).symm)
    $ Eq.trans (F.map_comp _ _).symm $ congrArg _
    $ congrArg₂ _ (Eq.trans (congrArg _ (Category.comp_id _)) (Category.comp_id _))
    $ congrArg₂ _ (Eq.trans (Category.id_comp _) (Category.comp_id _))
                  (Eq.trans (Category.id_comp _) (Category.id_comp _))

end CategoryTheory
