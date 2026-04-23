/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Module
public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Category.CompHaus.EffectiveEpi
public import Mathlib.Topology.Category.CompHaus.Limits
public import Mathlib.Topology.Category.Stonean.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Condensed.Equivalence
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!

# Epimorphisms of condensed objects

This file characterises epimorphisms of condensed sets and condensed `R`-modules for any ring `R`,
as those morphisms which are objectwise surjective on `Stonean` (see
`CondensedSet.epi_iff_surjective_on_stonean` and `CondensedMod.epi_iff_surjective_on_stonean`).
-/

public section

universe v u w u' v'

open CategoryTheory Sheaf Opposite Limits Condensed ConcreteCategory

namespace Condensed

variable (A : Type u') [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type v'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v'} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]

variable {X Y : Condensed.{u} A} (f : X ⟶ Y)

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
variable
  [(coherentTopology CompHaus).WEqualsLocallyBijective A]
  [HasSheafify (coherentTopology CompHaus) A]
  [(coherentTopology CompHaus.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (coherentTopology CompHaus) A)]
  [PreservesFiniteProducts (CategoryTheory.forget A)] in
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : ToType (Y.obj.obj ⟨S⟩)),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : ToType (X.obj.obj ⟨S'⟩)),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi', coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
variable
  [PreservesFiniteProducts (CategoryTheory.forget A)]
  [∀ (X : CompHausᵒᵖ), HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [(extensiveTopology Stonean).WEqualsLocallyBijective A]
  [HasSheafify (extensiveTopology Stonean) A]
  [(extensiveTopology Stonean.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (extensiveTopology Stonean) A)] in
lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) := by
  rw [← (StoneanCompHaus.equivalence A).inverse.epi_map_iff_epi,
    ← Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi,
    ← isLocallySurjective_iff_epi']
  exact extensiveTopology.isLocallySurjective_iff (D := A) _

end Condensed

namespace CondensedSet

variable {X Y : CondensedSet.{u}} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : Y.obj.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) :=
  Condensed.epi_iff_locallySurjective_on_compHaus _ f

lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) :=
  Condensed.epi_iff_surjective_on_stonean _ f

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R] {X Y : CondensedMod.{u} R} (f : X ⟶ Y)

lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : Y.obj.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) :=
  Condensed.epi_iff_locallySurjective_on_compHaus _ f

lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) :=
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.epi_iff_surjective_on_stonean _ f

end CondensedMod
