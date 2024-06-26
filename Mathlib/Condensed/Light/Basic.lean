/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
/-!

# Light condensed objects

This file defines the category of light condensed objects in a category `C`, following the work
of Clausen-Scholze (see https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).

-/

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
abbrev LightCondSet := LightCondensed.{u} (Type u)
