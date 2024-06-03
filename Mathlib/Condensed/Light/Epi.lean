/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic
/-!

# Epimorphisms of condensed objects

This file characterises epimorphisms of condensed sets and condensed `R`-modules for any ring `R`,
as those morphisms which are objectwise surjective on `Stonean` (see
`CondensedSet.epi_iff_surjective_on_stonean` and `CondensedMod.epi_iff_surjective_on_stonean`).
-/

universe v u w u' v'

open CategoryTheory Sheaf Opposite Limits ConcreteCategory

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike


namespace LightCondensed

variable (A : Type u') [Category.{v'} A] [ConcreteCategory.{v'} A]
  [HasFunctorialSurjectiveInjectiveFactorization A]
  [(coherentTopology LightProfinite).WEqualsLocallyBijective A]
  [HasSheafify (coherentTopology LightProfinite) A]
  [(coherentTopology LightProfinite.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (coherentTopology LightProfinite) A)]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

variable {X Y : LightCondensed.{u} A} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi', coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

end LightCondensed

namespace LightCondSet

variable {X Y : LightCondSet.{u}} (f : X ⟶ Y)

-- instance : ConcreteCategory.{u+1} (Type u) := sorry

instance : HasSheafify (coherentTopology LightProfinite.{u}) (Type u) := inferInstance

instance : (coherentTopology LightProfinite.{u}).HasSheafCompose
    (CategoryTheory.forget (Type u)) := inferInstance

instance (P : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    Presheaf.IsLocallyInjective (coherentTopology LightProfinite)
      (toSheafify (coherentTopology LightProfinite) P) := sorry

instance (P : LightProfinite.{u}ᵒᵖ ⥤ Type u) :
    Presheaf.IsLocallySurjective (coherentTopology LightProfinite)
      (toSheafify (coherentTopology LightProfinite) P) := sorry

instance : GrothendieckTopology.WEqualsLocallyBijective
    (coherentTopology LightProfinite.{u}) (Type u) := by
  apply GrothendieckTopology.WEqualsLocallyBijective.mk'

lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.val.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.val.obj ⟨S'⟩),
        f.val.app ⟨S'⟩ x = Y.val.map ⟨φ⟩ y) :=
  LightCondensed.epi_iff_locallySurjective_on_compHaus _ f

end LightCondSet
