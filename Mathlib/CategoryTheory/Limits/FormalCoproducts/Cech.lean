/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# The Cech object for formal coproducts

Let `C` be a category that has finite products. In this file, we define a
functor `cechFunctor : FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct of objects `U j` (for `j : ι`) to the simplicial object
which sends `⦋n⦌` to the formal coproduct, indexed by `i : Fin (n + 1) → ι`,
of the products of the objects `U (i a)` for all `a : Fin (n + 1)`.

-/

@[expose] public section

universe w t v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Given `U : FormalCoproduct C` and a type `α`, this is the formal coproduct
indexed by all `i : α → U.I` of the products of the objects `U.obj (i a)`
for all `a : α`. -/
@[simps]
noncomputable def power (U : FormalCoproduct.{w} C) (α : Type t)
    [HasProductsOfShape α C] : FormalCoproduct.{max w t} C where
  I := α → U.I
  obj i := ∏ᶜ (U.obj ∘ i)

/-- For any morphism `f : U ⟶ V` in `FormalCoproduct C` and a type `α`,
this is the induced map `U.power α ⟶ V.power α`. -/
@[simps -fullyApplied]
noncomputable def powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V) (α : Type t)
    [HasProductsOfShape α C] :
    U.power α ⟶ V.power α where
  f i := f.f ∘ i
  φ i := Pi.map (fun a ↦ f.φ (i a))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma powerMap_id (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α C] :
    powerMap (𝟙 U) α = 𝟙 _ := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma powerMap_comp {U V W : FormalCoproduct.{w} C} (f : U ⟶ V) (g : V ⟶ W) (α : Type t)
    [HasProductsOfShape α C] :
    powerMap (f ≫ g) α = powerMap f α ≫ powerMap g α := by
  ext
  · cat_disch
  · dsimp
    ext
    simp only [Category.comp_id, Category.assoc, Pi.map_π, Function.comp_apply,
      Pi.map_π_assoc]
    apply Pi.map_π

attribute [local simp] powerMap_comp

/-- Given a type `α`, this is the functor `FormalCoproduct C ⥤ FormalCoproduct C`
which sends `U` to `U.power α`. -/
@[simps]
noncomputable def powerFunctor (α : Type t) [HasProductsOfShape α C] :
    FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C where
  obj U := U.power α
  map f := powerMap f α

/-- The functoriality of `FormalCoproduct.power` with respect to the index type. -/
@[simps -fullyApplied]
noncomputable def mapPower (U : FormalCoproduct.{w} C) {α β : Type t}
    [HasProductsOfShape α C] [HasProductsOfShape β C] (f : α → β) :
    U.power β ⟶ U.power α where
  f i := i ∘ f
  φ _ := Pi.lift (fun _ ↦ Pi.π _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mapPower_id (U : FormalCoproduct.{w} C) (α : Type t)
    [HasProductsOfShape α C] :
    U.mapPower (id : α → α) = 𝟙 _ := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mapPower_comp (U : FormalCoproduct.{w} C) {α β γ : Type t}
    [HasProductsOfShape α C] [HasProductsOfShape β C] [HasProductsOfShape γ C]
    (f : α → β) (g : β → γ) :
    U.mapPower (g ∘ f) = U.mapPower g ≫ U.mapPower f := by
  ext
  · cat_disch
  · dsimp
    ext
    dsimp
    simp only [Category.comp_id, Category.assoc, Pi.lift_π]
    apply Pi.lift_π

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mapPower_powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V)
    {α β : Type t} [HasProductsOfShape α C] [HasProductsOfShape β C] (g : α → β) :
    U.mapPower g ≫ powerMap f α = powerMap f β ≫ V.mapPower g := by
  ext
  · cat_disch
  · dsimp
    ext
    simp only [Function.comp_apply, limit.lift_map, Cones.postcompose, Fan.mk_pt, Category.comp_id,
      Category.assoc, limit.lift_π, Fan.mk_π_app, Pi.map_π]
    apply limit.lift_π

attribute [local simp] mapPower_comp mapPower_powerMap

set_option backward.isDefEq.respectTransparency false in
/-- The functor `(Type t)ᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C`
which sends a type `α` and `U : FormalCoproduct C` to `U.power α`. -/
@[simps]
noncomputable def powerBifunctor [HasProducts.{t} C] :
    (Type t)ᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C where
  obj α := powerFunctor α.unop
  map f := { app _ := mapPower _ f.unop }
  map_comp _ _ := by ext : 2; dsimp; apply mapPower_comp

variable [HasFiniteProducts C]

/-- Given `U : FormalCoproduct C`, this is the simplicial object
in `FormalCoproduct C` which sends `⦋n⦌` to `U.power (Fin (n + 1))`. -/
@[simps]
noncomputable def cech (U : FormalCoproduct.{w} C) :
    SimplicialObject (FormalCoproduct.{w} C) where
  obj n := U.power (ToType n.unop)
  map f := U.mapPower f.unop.toOrderHom.toFun

/-- The functor `FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct to its Cech object. -/
@[simps]
noncomputable def cechFunctor :
    FormalCoproduct.{w} C ⥤ SimplicialObject (FormalCoproduct.{w} C) where
  obj U := U.cech
  map f := { app _ := powerMap f _ }
  map_comp _ _ := by ext : 1; simp

end CategoryTheory.Limits.FormalCoproduct
