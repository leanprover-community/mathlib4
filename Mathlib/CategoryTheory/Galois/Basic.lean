/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.SingleObj

/-!
# Definition and basic properties of Galois categories

We define the notion of a Galois category and a fibre functor as in SGA1, following
the definitions in Lenstras notes (see below for a reference).

## Main definitions

* `PreGaloisCategory` : defining properties of Galois categories not involving a fibre functor
* `FibreFunctor`      : a fibre functor from a PreGaloisCategory to `FintypeCat`
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

namespace CategoryTheory

open Limits Functor

/-!
A category `C` is a PreGalois category if it satisfies all properties
of a Galois category in the sense of SGA1 that do not involve a fibre functor.
A Galois category should furthermore admit a fibre functor.

We do not provide a typeclass `GaloisCategory`; users should
assume `[PreGaloisCategory C] (F : C ⥤ FintypeCat) [FibreFunctor F]` instead.
-/

/-- Definition of a (Pre)Galois category. Lenstra, Def 3.1, (G1)-(G3) -/
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  /-- `C` has a terminal object (G1). -/
  hasTerminal : HasTerminal C := by infer_instance
  /-- `C` has pullbacks (G1). -/
  hasPullbacks : HasPullbacks C := by infer_instance
  /-- `C` has finite coproducts (G2). -/
  hasFiniteCoproducts : HasFiniteCoproducts C := by infer_instance
  /-- `C` has quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C := by infer_instance
  /-- Every monomorphism in `C` induces an isomorphism on a direct summand (G3). -/
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

namespace PreGaloisCategory

/-- Definition of a fibre functor from a Galois category. Lenstra, Def 3.1, (G4)-(G6) -/
class FibreFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  /-- `F` preserves terminal objects (G4). -/
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F :=
    by infer_instance
  /-- `F` preserves pullbacks (G4). -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F := by infer_instance
  /-- `F` preserves finite coproducts (G5). -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F := by infer_instance
  /-- `F` preserves epimorphisms (G5). -/
  preservesEpis : Functor.PreservesEpimorphisms F := by infer_instance
  /-- `F` preserves quotients by finite groups (G5). -/
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by infer_instance
  /-- `F` reflects isomorphisms (G6). -/
  reflectsIsos : ReflectsIsomorphisms F := by infer_instance

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
  /-- `F.obj X` is connected if `X` is connected. -/
  preserves : ∀ {X : C} [ConnectedObject X], ConnectedObject (F.obj X)

variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups

instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks

instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C

instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

namespace FibreFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FibreFunctor F]

attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis
  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups

noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms

noncomputable instance : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

/-- Fibre functors reflect monomorphisms. -/
instance : ReflectsMonomorphisms F := ReflectsMonomorphisms.mk <| by
  intro X Y f _
  haveI : IsIso (pullback.fst : pullback (F.map f) (F.map f) ⟶ F.obj X) :=
    fst_iso_of_mono_eq (F.map f)
  haveI : IsIso (F.map (pullback.fst : pullback f f ⟶ X)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  haveI : IsIso (pullback.fst : pullback f f ⟶ X) := isIso_of_reflects_iso pullback.fst F
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst

/-- Fibre functors are faithful. -/
instance : Faithful F where
  map_injective {X Y} f g h := by
    haveI : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    haveI : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    haveI : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

end FibreFunctor

variable (F : C ⥤ FintypeCat.{w}) [FibreFunctor F]

/-- An object is initial if and only if its fibre is empty. -/
lemma initial_iff_fibre_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  haveI : PreservesFiniteColimits (forget FintypeCat) := by
    show PreservesFiniteColimits FintypeCat.incl
    infer_instance
  haveI : ReflectsColimit (Functor.empty.{0} _) (forget FintypeCat) := by
    show ReflectsColimit (Functor.empty.{0} _) FintypeCat.incl
    infer_instance
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

/-- An object whose fibre is inhabited is not initial. -/
lemma not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False :=
  ((initial_iff_fibre_empty F X).mp ⟨h⟩).false x

/-- The fibre of a connected object is nonempty. -/
lemma nonempty_fibre_of_connected (X : C) [ConnectedObject X] : Nonempty (F.obj X) := by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fibre_empty F X).mpr (not_nonempty_iff.mp h)
  exact ConnectedObject.notInitial hin

/-- The fibre of the equalizer of `f g : X ⟶ Y` is equivalent to the set of agreement of `f`
and `g`. -/
private noncomputable def fibreEqualizerEquiv {X Y : C} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃ { x : F.obj X // F.map f x = F.map g x } := by
  apply Iso.toEquiv
  trans
  · exact PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g
  · exact Types.equalizerIso (F.map f) (F.map g)

/-- The evaluation map is injective for connected objects. -/
lemma evaluationInjective_of_connected (A X : C) [ConnectedObject A] (a : F.obj A) :
    Function.Injective (fun (f : A ⟶ X) ↦ F.map f a) := by
  intro f g (h : F.map f a = F.map g a)
  haveI : IsIso (equalizer.ι f g) := by
    apply ConnectedObject.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fibreEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer

/-- The evaluation map on automorphisms is injective for connected objects. -/
lemma evaluation_aut_injective_of_connected (A : C) [ConnectedObject A] (a : F.obj A) :
    Function.Injective (fun f : Aut A ↦ F.map (f.hom) a) := by
  show Function.Injective ((fun f : A ⟶ A ↦ F.map f a) ∘ (fun f : Aut A ↦ f.hom))
  apply Function.Injective.comp
  · exact evaluationInjective_of_connected F A A a
  · exact @Aut.ext _ _ A

end PreGaloisCategory

end CategoryTheory
