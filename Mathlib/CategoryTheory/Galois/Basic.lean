/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.SingleObj

/-!
# Definition and basic properties of Galois categories

We define the notion of a Galois category and a fibre functor as in SGA1, following
the definitions in Lenstras notes (see below for a reference).

## Main definitions

* `PreGaloisCategory` : defining properties of Galois categories not involving a fibre functor
* `FibreFunctor`      : a fibre functor from any category to `FintypeCat`
* `ConnectedObject`   : an object of a category that is not initial and has no non-trivial
                        subobjects

## Implementation details

We mostly follow Def 3.1 in Lenstras notes. In axiom (G3)
we omit the factorisation of morphisms in epimorphisms and monomorphisms
as this is not needed for the proof of the fundamental theorem on Galois categories
(and then follows from it).

## References

* H. W. Lenstra. Galois theory for schemes
  <https://websites.math.leidenuniv.nl/algebra/GSchemes.pdf>

-/

universe u₁ u₂ v₁ v₂ w

open CategoryTheory Limits Functor

namespace Galois

section Def

/- Lenstra, Def 3.1, (G1)-(G3) -/
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  -- (G1)
  hasTerminalObject : HasTerminal C
  hasPullbacks : HasPullbacks C
  -- (G2)
  hasFiniteCoproducts : HasFiniteCoproducts C
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C
  -- (G3)
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

/- Lenstra, Def 3.1, (G4)-(G6) -/
class FibreFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  -- (G4)
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F
  -- (G5)
  preservesFiniteCoproducts : PreservesFiniteCoproducts F
  preservesEpis : Functor.PreservesEpimorphisms F
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F
  -- (G6)
  reflectsIsos : ReflectsIsomorphisms F

/- Lenstra, 3.12. An object of a category `C` is connected if it is not initial
and has no non-trivial subobjects. -/
class ConnectedObject {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  notInitial : IsInitial X → False
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

/- A functor between categories is said to preserves connected objects if it sends
connected objects to connected objects. -/
class PreservesConnectedObjects {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
    [Category.{v₂, v₁} D] (F : C ⥤ D) : Prop where
  preserves : ∀ {X : C} [ConnectedObject X], ConnectedObject (F.obj X)

end Def

section Instances

variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

instance : HasTerminal C := PreGaloisCategory.hasTerminalObject

instance : HasPullbacks C := PreGaloisCategory.hasPullbacks

instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks

instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C

instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

instance : HasFiniteCoproducts C := PreGaloisCategory.hasFiniteCoproducts

instance (ι : Type*) [Finite ι] : HasColimitsOfShape (Discrete ι) C :=
  hasColimitsOfShape_discrete C ι

instance : HasInitial C := inferInstance

instance (G : Type u₂) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C :=
  PreGaloisCategory.hasQuotientsByFiniteGroups G 

variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FibreFunctor F]

instance : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F :=
  FibreFunctor.preservesTerminalObjects

instance : PreservesLimitsOfShape WalkingCospan F :=
  FibreFunctor.preservesPullbacks

instance : PreservesEpimorphisms F :=
  FibreFunctor.preservesEpis

instance : PreservesFiniteCoproducts F :=
  FibreFunctor.preservesFiniteCoproducts

instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) F :=
  FibreFunctor.preservesFiniteCoproducts.preserves PEmpty

instance : ReflectsIsomorphisms F :=
  FibreFunctor.reflectsIsos

noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms

instance (G : Type u₂) [Group G] [Finite G] : PreservesColimitsOfShape (SingleObj G) F :=
  FibreFunctor.preservesQuotientsByFiniteGroups G

noncomputable instance : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

end Instances

end Galois
