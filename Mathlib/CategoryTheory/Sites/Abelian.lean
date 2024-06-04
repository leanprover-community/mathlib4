/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Jujian Zhang
-/
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Sites.Limits

#align_import topology.sheaves.abelian from "leanprover-community/mathlib"@"ac3ae212f394f508df43e37aa093722fa9b65d31"

/-!
# Category of sheaves is abelian
Let `C, D` be categories and `J` be a grothendieck topology on `C`, when `D` is abelian and
sheafification is possible in `C`, `Sheaf J D` is abelian as well (`sheafIsAbelian`).

Hence, `presheafToSheaf` is an additive functor (`presheafToSheaf_additive`).

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

section Abelian

universe w' w v u

variable {C : Type u} [Category.{v} C]
variable {D : Type w} [Category.{w'} D] [Abelian D]
variable {J : GrothendieckTopology C}
variable [HasSheafify J D]

instance sheafIsAbelian : Abelian (Sheaf J D) :=
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
