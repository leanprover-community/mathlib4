/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Coherent.SequentialLimit
import Mathlib.Condensed.Light.Module
/-!

# Epimorphisms of light condensed objects

This file characterises epimorphisms in light condensed sets and modules as the locally surjective
morphisms. Here, the condition of locally surjective is phrased in terms of continuous surjections
of light profinite sets.
-/

universe v u w u' v'

open CategoryTheory Sheaf Limits ConcreteCategory GrothendieckTopology

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

namespace LightCondensed

variable (A : Type u') [Category.{v'} A] [ConcreteCategory.{w} A]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

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
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R] {X Y : LightCondMod.{u} R} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

instance : (LightCondensed.forget R).ReflectsEpimorphisms where
  reflects f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.val).mpr hf

instance : (LightCondensed.forget R).PreservesEpimorphisms where
  preserves f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.val).mp hf

end LightCondMod

namespace LightCondensed

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

include hc hF in
lemma epi_π_app_zero_of_epi : Epi (c.π.app ⟨0⟩) := by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun _ h ↦ Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) h
  · have := (freeForgetAdjunction R).isRightAdjoint
    exact isLimitOfPreserves _ hc
  · exact fun _ ↦ (forget R).map_epi _

end LightCondensed
