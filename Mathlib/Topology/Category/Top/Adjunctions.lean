/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro

! This file was ported from Lean 3 source module topology.category.Top.adjunctions
! leanprover-community/mathlib commit f7baecbb54bd0f24f228576f97b1752fc3c9b318
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Top.Basic
import Mathbin.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `Top.discrete`, resp. `Top.trivial`, the functors which equip a type with the
discrete, resp. trivial, topology.
-/


universe u

open CategoryTheory

open TopCat

namespace TopCat

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₁ : discrete ⊣ forget TopCat.{u} :=
  Adjunction.mkOfUnitCounit
    { Unit := { app := fun X => id }
      counit := { app := fun X => ⟨id, continuous_bot⟩ } }
#align Top.adj₁ TopCat.adj₁

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₂ : forget TopCat.{u} ⊣ trivial :=
  Adjunction.mkOfUnitCounit
    { Unit := { app := fun X => ⟨id, continuous_top⟩ }
      counit := { app := fun X => id } }
#align Top.adj₂ TopCat.adj₂

instance : IsRightAdjoint (forget TopCat.{u}) :=
  ⟨_, adj₁⟩

instance : IsLeftAdjoint (forget TopCat.{u}) :=
  ⟨_, adj₂⟩

end TopCat

