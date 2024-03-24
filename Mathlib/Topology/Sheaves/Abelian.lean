/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Jujian Zhang
-/
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Sites.LeftExact

#align_import topology.sheaves.abelian from "leanprover-community/mathlib"@"ac3ae212f394f508df43e37aa093722fa9b65d31"

/-!
# Category of sheaves is abelian
Let `C, D` be categories and `J` be a grothendieck topology on `C`, when `D` is abelian and
sheafification is possible in `C`, `Sheaf J D` is abelian as well (`sheafIsAbelian`).

Hence, `presheafToSheaf` is an additive functor (`presheafToSheaf_additive`).

TODO: This file should be moved to `CategoryTheory/Sites`.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

section Abelian

universe w v u

-- Porting note: `C` was `Type (max v u)`, but making it more universe polymorphic
--   solves some problems
variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{max v u} D] [Abelian D]
variable {J : GrothendieckTopology C}

-- Porting note: this `Abelian` instance is no longer necessary,
-- maybe because I have made `C` more universe polymorphic
--
-- This needs to be specified manually because of universe level.
--instance : Abelian (Cᵒᵖ ⥤ D) :=
--  @Abelian.functorCategoryAbelian Cᵒᵖ _ D _ _

-- This also needs to be specified manually, but I don't know why.
instance hasFiniteProductsSheaf : HasFiniteProducts (Sheaf J D) where
  out j := { has_limit := fun F => by infer_instance }

-- sheafification assumptions
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [ReflectsIsomorphisms (forget D)]

instance sheafIsAbelian [HasFiniteLimits D] : Abelian (Sheaf J D) :=
  let adj := sheafificationAdjunction J D
  abelianOfAdjunction _ _ (asIso adj.counit) adj
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_is_abelian CategoryTheory.sheafIsAbelian

attribute [local instance] preservesBinaryBiproductsOfPreservesBinaryProducts

instance presheafToSheaf_additive : (presheafToSheaf J D).Additive :=
  (presheafToSheaf J D).additive_of_preservesBinaryBiproducts
set_option linter.uppercaseLean3 false in
#align category_theory.presheaf_to_Sheaf_additive CategoryTheory.presheafToSheaf_additive

end Abelian

end CategoryTheory
