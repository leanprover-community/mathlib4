/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Monoidal.Closed.Transport
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Condensed.Light.Module
import Mathlib.Condensed.Light.Small

/-!

# Closed symmetric monoidal structure on light condensed modules

We define a symmetric monoidal structure on a category of sheaves on a small site that is equivalent
to light condensed modules, by localizing the symmetric monoidal structure on the presheaf category.

By Day's reflection theorem, we obtain a closed structure.

Finally, we transfer all this structure along the equivalence of categories, to obtain the closed
symmetric monoidal structure on light condensed modules.
-/

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

namespace LightCondensed

attribute [local instance] monoidalCategory symmetricCategory

variable (R : Type (u + 1)) [CommRing R]

variable (R : Type u) [CommRing R]

instance : MonoidalCategory (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Transported (equivSmall (ModuleCat R)).symm))

instance : SymmetricCategory (LightCondMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Transported (equivSmall (ModuleCat R)).symm))

/--
The category of sheaves on a small site that is equivalent to light condensed modules is monoidal
closed.
-/
local instance : MonoidalClosed
    (Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Transported (equivSmall (ModuleCat R)).symm))

end LightCondensed
