/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

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
def adj₁ : discrete ⊣ forget TopCat.{u} where
  unit := { app := fun _ => id }
  counit := { app := fun X => TopCat.ofHom (X := discrete.obj X) ⟨id, continuous_bot⟩ }

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
def adj₂ : forget TopCat.{u} ⊣ trivial where
  unit := { app := fun X => TopCat.ofHom (Y := trivial.obj X) ⟨id, continuous_top⟩ }
  counit := { app := fun _ => id }

instance : (forget TopCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj₁⟩⟩

instance : (forget TopCat.{u}).IsLeftAdjoint :=
  ⟨_, ⟨adj₂⟩⟩

end TopCat
