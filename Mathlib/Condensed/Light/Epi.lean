/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic
/-!

# Epimorphisms of light condensed objects

-/

universe v u w u' v'

open CategoryTheory Sheaf Limits ConcreteCategory

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

namespace LightCondensed

variable (A : Type u') [Category.{v'} A] [ConcreteCategory.{w} A]
  [PreservesFiniteProducts (forget A)]

variable {X Y : LightCondensed.{u} A} (f : X ⟶ Y)

lemma isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurjective f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

end LightCondensed

namespace LightCondSet

variable {X Y : LightCondSet.{u}} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi_of_site_essentiallySmall]
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

end LightCondSet
