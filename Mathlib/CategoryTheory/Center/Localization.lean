/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Localization of the center of a category

Given a localization functor `L : C ⥤ D` with respect to `W : MorphismProperty C`,
we define a localization map `CatCenter C → CatCenter D` for the centers
of these categories. In case `L` is an additive functor between preadditive
categories, we promote this to a ring morphism `CatCenter C →+* CatCenter D`.

-/

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (r s : CatCenter C) (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace CatCenter

/-- Given `r : CatCenter C` and `L : C ⥤ D` a localization functor with respect
to `W : MorphismProperty D`, this is the induced element in `CatCenter D`
obtained by localization. -/
noncomputable def localization : CatCenter D :=
  Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (Functor.whiskerRight r L)

@[simp]
lemma localization_app (X : C) :
    (r.localization L W).app (L.obj X) = L.map (r.app X) := by
  dsimp [localization]
  simp only [Localization.liftNatTrans_app, Functor.id_obj, Functor.whiskerRight_app,
    NatTrans.naturality, Functor.comp_map, Functor.id_map, Iso.hom_inv_id_app_assoc]

include W

lemma ext_of_localization (r s : CatCenter D)
    (h : ∀ (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s :=
  Localization.natTrans_ext L W h

lemma localization_one :
    (1 : CatCenter C).localization L W = 1 :=
  ext_of_localization L W _ _ (fun X ↦ by simp)

lemma localization_mul :
    (r * s).localization L W = r.localization L W * s.localization L W :=
  ext_of_localization L W _ _ (fun X ↦ by simp)

section Preadditive

variable [Preadditive C] [Preadditive D] [L.Additive]

lemma localization_zero :
    (0 : CatCenter C).localization L W = 0 :=
  ext_of_localization L W _ _ (fun X ↦ by simp)

lemma localization_add :
    (r + s).localization L W = r.localization L W + s.localization L W :=
  ext_of_localization L W _ _ (fun X ↦ by
    rw [localization_app, NatTrans.app_add, NatTrans.app_add, L.map_add,
      localization_app, localization_app])

/-- The morphism of rings `CatCenter C →+* CatCenter D` when `L : C ⥤ D`
is an additive localization functor between preadditive categories. -/
noncomputable def localizationRingHom : CatCenter C →+* CatCenter D where
  toFun r := r.localization L W
  map_zero' := localization_zero L W
  map_one' := localization_one L W
  map_add' _ _ := localization_add _ _ _ _
  map_mul' _ _ := localization_mul _ _ _ _

end Preadditive

end CatCenter

end CategoryTheory
