/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.Condensed.Equivalence
import Mathlib.Condensed.Module
/-!

# Epimorphisms of condensed objects

This file characterises epimorphisms of condensed sets and condensed `R`-modules for any ring `R`,
as those morphisms which are objectwise surjective on `Stonean` (see
`CondensedSet.epi_iff_surjective_on_stonean` and `CondensedMod.epi_iff_surjective_on_stonean`).
-/

universe v u w

open CategoryTheory Sheaf Opposite Limits Condensed

attribute [local instance] ConcreteCategory.instFunLike

namespace CondensedSet

variable {X Y : CondensedSet.{u}} (f : X ⟶ Y)

lemma isLocallySurjective_iff_epi : IsLocallySurjective f ↔ Epi f :=
  Sheaf.isLocallySurjective_iff_epi f

lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  simp_rw [← isLocallySurjective_iff_epi, coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff, ((CompHaus.effectiveEpi_tfae _).out 0 2 :)]
  rfl

lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.val.app (op S.compHaus)) := by
  rw [← (StoneanCompHaus.equivalence (Type (u+1))).inverse.epi_map_iff_epi,
    ← Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi,
    ← Sheaf.isLocallySurjective_iff_epi]
  exact extensiveTopology.isLocallySurjective_iff (D := Type (u+1)) _

end CondensedSet

namespace CondensedMod

variable (R : Type (u+1)) [Ring R] {X Y : CondensedMod.{u} R} (f : X ⟶ Y)

lemma isLocallySurjective_iff_epi : IsLocallySurjective f ↔ Epi f :=
  Sheaf.isLocallySurjective_iff_epi' _ f

lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  simp_rw [← isLocallySurjective_iff_epi, coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff, ((CompHaus.effectiveEpi_tfae _).out 0 2 :)]
  rfl

lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.val.app (op S.compHaus)) := by
  have : HasLimitsOfSize.{u, u+1} (ModuleCat R) := hasLimitsOfSizeShrink.{u, u+1, u+1, u+1} _
  rw [← (StoneanCompHaus.equivalence (ModuleCat R)).inverse.epi_map_iff_epi,
    ← (Presheaf.coherentExtensiveEquivalence
      (C := Stonean.{u}) (A := ModuleCat R)).functor.epi_map_iff_epi,
    ← Sheaf.isLocallySurjective_iff_epi']
  exact extensiveTopology.isLocallySurjective_iff (D := ModuleCat R) _

end CondensedMod
