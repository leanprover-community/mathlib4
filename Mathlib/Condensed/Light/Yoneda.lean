/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module
/-!

# The Yoneda embedding `LightProfinite ⥤ LightCondSet`


-/

universe u

open CategoryTheory Opposite LightCondensed

namespace LightCondSet

abbrev yonedaEquiv {S : LightProfinite.{u}} {X : LightCondSet.{u}} :
    (S.toCondensed ⟶ X) ≃ X.val.obj (op S) :=
  (coherentTopology LightProfinite).yonedaEquiv

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

noncomputable def yonedaEquiv {S : LightProfinite.{u}} {M : LightCondMod R} :
    ((free R).obj S.toCondensed ⟶ M) ≃ M.val.obj ⟨S⟩ :=
  ((freeForgetAdjunction R).homEquiv _ _).trans LightCondSet.yonedaEquiv

lemma yonedaEquiv_symm_naturality_left {S S' : LightProfinite.{u}} (f : S' ⟶ S)
    (M : LightCondMod R) (x : M.val.obj ⟨S⟩) :
    (lightProfiniteToLightCondSet ⋙ free R).map f ≫ (yonedaEquiv R).symm x =
      (yonedaEquiv R).symm ((M.val.map f.op) x) := by
  simp only [Functor.comp_obj, Functor.comp_map, yonedaEquiv, Equiv.symm_trans_apply,
    Adjunction.homEquiv_counit, Functor.id_obj]
  simp only [← Category.assoc, ← Functor.map_comp]
  erw [GrothendieckTopology.yonedaEquiv_symm_naturality_left]
  rfl

lemma yonedaEquiv_symm_naturality_right (S : LightProfinite.{u}) {M M' : LightCondMod R}
    (f : M ⟶ M') (x : M.val.obj ⟨S⟩) :
      (yonedaEquiv R).symm x ≫ f = (yonedaEquiv R).symm (f.val.app ⟨S⟩ x) := by
  simp only [yonedaEquiv, Equiv.symm_trans_apply]
  erw [← GrothendieckTopology.yonedaEquiv_symm_naturality_right
    (X := S) (F' := (forget R).obj M') (f := (forget R).map f)]
  simp only [Adjunction.homEquiv_counit, Functor.id_obj, Category.assoc, Functor.map_comp,
    Adjunction.counit_naturality, Functor.comp_obj]
  rfl

end LightCondMod
