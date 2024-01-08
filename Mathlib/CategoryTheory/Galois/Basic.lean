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

/-- Definition of a Galois category. Lenstra, Def 3.1, (G1)-(G3) -/
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  /-- `C` has a terminal object (G1). -/
  hasTerminalObject : HasTerminal C
  /-- `C` has pullbacks (G1). -/
  hasPullbacks : HasPullbacks C
  /-- `C` has finite coproducts (G2). -/
  hasFiniteCoproducts : HasFiniteCoproducts C
  /-- `C` has quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C
  /-- Every monomorphism in `C` induces an isomorphism on a direct summand (G3). -/
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

/-- Definition of a fibre functor from a Galois category. Lenstra, Def 3.1, (G4)-(G6) -/
class FibreFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  /-- `F` preserves terminal objects (G4). -/
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F
  /-- `F` preserves pullbacks (G4). -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F
  /-- `F` preserves finite coproducts (G5). -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F
  /-- `F` preserves epimorphisms (G5). -/
  preservesEpis : Functor.PreservesEpimorphisms F
  /-- `F` preserves quotients by finite groups (G5). -/
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F
  /-- `F` reflects isomorphisms (G6). -/
  reflectsIsos : ReflectsIsomorphisms F

/-- An object of a category `C` is connected if it is not initial
and has no non-trivial subobjects. Lenstra, 3.12. -/
class ConnectedObject {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  /-- `X` is not an initial object. -/
  notInitial : IsInitial X → False
  /-- `X` has no non-trivial subobjects. -/
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

/-- A functor is said to preserve connected objects if it sends
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
