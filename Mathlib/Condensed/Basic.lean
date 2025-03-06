/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

/-!

# Condensed Objects

This file defines the category of condensed objects in a category `C`, following the work
of Clausen-Scholze and Barwick-Haine.

## Implementation Details

We use the coherent Grothendieck topology on `CompHaus`, and define condensed objects in `C` to
be `C`-valued sheaves, with respect to this Grothendieck topology.

Note: Our definition more closely resembles "Pyknotic objects" in the sense of Barwick-Haine,
as we do not impose cardinality bounds, and manage universes carefully instead.

## References

- [barwickhaine2019]: *Pyknotic objects, I. Basic notions*, 2019.
- [scholze2019condensed]: *Lectures on Condensed Mathematics*, 2019.

-/

open CategoryTheory Limits

open CategoryTheory

universe u v w

/--
`Condensed.{u} C` is the category of condensed objects in a category `C`, which are
defined as sheaves on `CompHaus.{u}` with respect to the coherent Grothendieck topology.
-/
def Condensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology CompHaus.{u}) C

instance {C : Type w} [Category.{v} C] : Category (Condensed.{u} C) :=
  show Category (Sheaf _ _) from inferInstance

/--
Condensed sets (types) with the appropriate universe levels, i.e. `Type (u+1)`-valued
sheaves on `CompHaus.{u}`.
-/
abbrev CondensedSet := Condensed.{u} (Type (u+1))

namespace Condensed

variable {C : Type w} [Category.{v} C]

@[simp]
lemma id_val (X : Condensed.{u} C) : (𝟙 X : X ⟶ X).val = 𝟙 _ := rfl

@[simp]
lemma comp_val {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[ext]
lemma hom_ext {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.val.app S = g.val.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _

end Condensed

namespace CondensedSet

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
-- Note: `simp` can prove this when stated for `Condensed C` for a concrete category `C`.
-- However, it doesn't seem to see through the abbreviation `CondensedSet`
@[simp]
lemma hom_naturality_apply {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x

end CondensedSet
