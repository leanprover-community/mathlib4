/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.Light.Instances
public import Mathlib.Condensed.Light.Module

/-!

# Closed symmetric monoidal structure on light condensed modules

We define a symmetric monoidal structure on light condensed modules by localizing the symmetric
monoidal structure on the presheaf category. By Day's reflection theorem, we obtain a closed
structure.
-/

public section

universe u

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

namespace LightCondensed

variable (R : Type u) [CommRing R]

instance : (coherentTopology LightProfinite.{u}).W (A := ModuleCat.{u} R) |>.IsMonoidal :=
  GrothendieckTopology.W.transport_isMonoidal _ _
    ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u}))
    (equivSmallModel.{u} LightProfinite.{u}).inverse

noncomputable instance : MonoidalCategory (LightCondMod.{u} R) :=
  monoidalCategory _ _

noncomputable
instance : MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  inferInstanceAs (MonoidalCategory (LightCondMod _))

noncomputable instance : SymmetricCategory (LightCondMod.{u} R) :=
  symmetricCategory _ _

noncomputable instance : MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) :=
  .ofEquiv _ (equivSmallModel LightProfinite).op.congrLeft.toAdjunction

noncomputable
instance : MonoidalClosed (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

noncomputable instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Sheaf _ _))

noncomputable
instance : (presheafToSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Monoidal :=
  inferInstance

noncomputable instance : (free R).Monoidal := inferInstanceAs (composeAndSheafify _ _).Monoidal

end LightCondensed
