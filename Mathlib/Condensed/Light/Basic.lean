/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
/-!

# Light condensed objects

This file defines the category of light condensed objects in a category `C`, following the work
of Clausen-Scholze (see https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).

-/

@[expose] public section

universe u v w

open CategoryTheory Limits

/--
`LightCondensed.{u} C` is the category of light condensed objects in a category `C`, which are
defined as sheaves on `LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
def LightCondensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology LightProfinite.{u}) C

instance {C : Type w} [Category.{v} C] : Category (LightCondensed.{u} C) :=
  show Category (Sheaf _ _) from inferInstance

/--
Light condensed sets. Because `LightProfinite` is an essentially small category, we don't need the
same universe bump as in `CondensedSet`.
-/
abbrev LightCondSet := LightCondensed.{u} Type u

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

@[simp]
lemma id_hom (X : LightCondensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

@[simp]
lemma comp_hom {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom


@[ext]
lemma hom_ext {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.hom.app S = g.hom.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _

end LightCondensed

namespace LightCondSet

-- Note: `simp` can prove this when stated for `LightCondensed C` for a concrete category `C`.
-- However, it doesn't seem to see through the abbreviation `LightCondSet`
@[simp]
lemma hom_naturality_apply {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) :=
  NatTrans.naturality_apply f.hom g x

end LightCondSet
