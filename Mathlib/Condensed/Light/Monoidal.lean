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

namespace LightCondensed

attribute [local instance] monoidalCategory symmetricCategory

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

section

variable {C D E : Type*} [Category C] [Category D] [Category E] (e : C ≌ D)
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) (G : E ⥤ D) [e.functor.Monoidal] [e.inverse.Monoidal]
    (H : C ⥤ E) (I : E ⥤ C)

def _root_.CategoryTheory.Equivalence.monoidalOfPrecompFunctor
    [(e.functor ⋙ F).Monoidal] : F.Monoidal :=
  Monoidal.transport (e.invFunIdAssoc F)

def _root_.CategoryTheory.Equivalence.monoidalOfPrecompInverse
    [(e.inverse ⋙ H).Monoidal] : H.Monoidal :=
  letI : (e.symm.functor ⋙ H).Monoidal := inferInstanceAs (e.inverse ⋙ H).Monoidal
  e.symm.monoidalOfPrecompFunctor _

def _root_.CategoryTheory.Equivalence.monoidalOfPostcompInverse [(G ⋙ e.inverse).Monoidal] :
    G.Monoidal :=
  letI : (G ⋙ e.inverse ⋙ e.functor).Monoidal :=
    inferInstanceAs ((G ⋙ e.inverse) ⋙ e.functor).Monoidal
  Monoidal.transport (isoWhiskerLeft G e.counitIso ≪≫ G.rightUnitor)

def _root_.CategoryTheory.Equivalence.monoidalOfPostcompFunctor
    [(I ⋙ e.functor).Monoidal] : I.Monoidal :=
  letI : (I ⋙ e.symm.inverse).Monoidal := inferInstanceAs (I ⋙ e.functor).Monoidal
  e.symm.monoidalOfPostcompInverse _

end

instance : (equivSmall (ModuleCat R)).functor.Monoidal :=
  inferInstanceAs (equivalenceTransported (equivSmall (ModuleCat R)).symm).inverse.Monoidal

instance : (equivSmall (ModuleCat R)).inverse.Monoidal :=
  inferInstanceAs (equivalenceTransported (equivSmall (ModuleCat R)).symm).functor.Monoidal

instance : (equivSmall (Type u)).functor.Monoidal :=
  ((Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance).some

instance : (equivSmall (Type u)).inverse.Monoidal :=
  ((Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance).some

instance : (free R).Monoidal := by
  apply (config := {allowSynthFailures := true}) (equivSmall _).symm.monoidalOfPostcompInverse
  apply (config := {allowSynthFailures := true}) (equivSmall _).symm.monoidalOfPrecompFunctor
  exact Monoidal.transport (equivSmallFreeIso R).symm

end LightCondensed
