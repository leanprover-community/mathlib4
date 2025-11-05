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
import Mathlib.Condensed.Light.CartesianClosed
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
  Functor

section -- TODO: move

variable {C D : Type*} (E : Type*) [Category C] [Category D] [Category E] [MonoidalCategory E]
    (F : C ⥤ D)

def whiskeringLeftCoreMonoidal : ((whiskeringLeft _ _ E).obj F).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _

instance : ((whiskeringLeft _ _ E).obj F).Monoidal := (whiskeringLeftCoreMonoidal E F).toMonoidal

end

namespace LightCondensed

variable (R : Type u) [CommRing R]

attribute [local instance] monoidalCategory in
instance : MonoidalCategory (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Transported (equivSmall (ModuleCat R)).symm))

attribute [local instance] monoidalCategory symmetricCategory in
instance : SymmetricCategory (LightCondMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Transported (equivSmall (ModuleCat R)).symm))

instance : MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  inferInstanceAs (MonoidalCategory (LightCondMod _))

instance : HasWeakSheafify (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R) :=
  inferInstance

attribute [local instance] monoidalCategory symmetricCategory in
/--
The category of sheaves on a small site that is equivalent to light condensed modules is monoidal
closed.
-/
local instance : MonoidalClosed
    (Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

attribute [local instance] monoidalCategory in
instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Transported (equivSmall (ModuleCat R)).symm))

attribute [local instance] monoidalCategory in
instance : (equivSmall (ModuleCat R)).functor.Monoidal :=
  inferInstanceAs (equivalenceTransported (equivSmall (ModuleCat R)).symm).inverse.Monoidal

attribute [local instance] monoidalCategory in
instance : (equivSmall (ModuleCat R)).inverse.Monoidal :=
  inferInstanceAs (equivalenceTransported (equivSmall (ModuleCat R)).symm).functor.Monoidal

instance : (equivSmall (Type u)).functor.Monoidal :=
  ((Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance).some

instance : (equivSmall (Type u)).inverse.Monoidal :=
  ((Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance).some

instance : (presheafToSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Monoidal := by
  letI : MonoidalCategory (Sheaf ((equivSmallModel LightProfinite).inverse.inducedTopology
      (coherentTopology LightProfinite)) (ModuleCat R)) := monoidalCategory _ _
  apply (config := {allowSynthFailures := true}) (equivSmall _).symm.monoidalOfPostcompInverse
  apply (config := {allowSynthFailures := true})
    (equivSmallModel LightProfinite.{u}).symm.op.congrLeft.monoidalOfPrecompFunctor
  · dsimp [Equivalence.congrLeft]
    infer_instance
  · exact Monoidal.transport (equivSmallSheafificationIso (C := ModuleCat.{u} R)).symm

instance : (free R).Monoidal := by
  letI : MonoidalCategory (Sheaf ((equivSmallModel LightProfinite).inverse.inducedTopology
      (coherentTopology LightProfinite)) (ModuleCat R)) := monoidalCategory _ _
  apply (config := {allowSynthFailures := true}) (equivSmall _).symm.monoidalOfPostcompInverse
  apply (config := {allowSynthFailures := true}) (equivSmall _).symm.monoidalOfPrecompFunctor
  exact Monoidal.transport (equivSmallFreeIso R).symm

end LightCondensed
