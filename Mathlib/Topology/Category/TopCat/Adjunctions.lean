/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

#align_import topology.category.Top.adjunctions from "leanprover-community/mathlib"@"f7baecbb54bd0f24f228576f97b1752fc3c9b318"

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `TopCat.discrete`, resp. `TopCat.trivial`, the functors which equip a type with
the discrete, resp. trivial, topology.
-/


universe u

open CategoryTheory

open TopCat

namespace TopCat

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
def adj₁ : discrete ⊣ forget TopCat.{u} :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun X => id }
      counit := { app := fun X => ⟨id, continuous_bot⟩ } }
set_option linter.uppercaseLean3 false in
#align Top.adj₁ TopCat.adj₁

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
def adj₂ : forget TopCat.{u} ⊣ trivial :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun X => ⟨id, continuous_top⟩ }
      counit := { app := fun X => id } }
set_option linter.uppercaseLean3 false in
#align Top.adj₂ TopCat.adj₂

instance : (forget TopCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj₁⟩⟩

instance : (forget TopCat.{u}).IsLeftAdjoint :=
  ⟨_, ⟨adj₂⟩⟩

end TopCat
