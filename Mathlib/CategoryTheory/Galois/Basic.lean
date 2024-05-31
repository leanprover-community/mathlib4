/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Finite.Card

/-!
# Definition and basic properties of Galois categories

We define the notion of a Galois category and a fiber functor as in SGA1, following
the definitions in Lenstras notes (see below for a reference).

## Main definitions

* `PreGaloisCategory` : defining properties of Galois categories not involving a fiber functor
* `FiberFunctor`      : a fiber functor from a `PreGaloisCategory` to `FintypeCat`
* `GaloisCategory`    : a `PreGaloisCategory` that admits a `FiberFunctor`
* `IsConnected`       : an object of a category is connected if it is not initial
                        and does not have non-trivial subobjects

## Implementation details

We mostly follow Def 3.1 in Lenstras notes. In axiom (G3)
we omit the factorisation of morphisms in epimorphisms and monomorphisms
as this is not needed for the proof of the fundamental theorem on Galois categories
(and then follows from it).

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open Limits Functor

/-!
A category `C` is a PreGalois category if it satisfies all properties
of a Galois category in the sense of SGA1 that do not involve a fiber functor.
A Galois category should furthermore admit a fiber functor.

The only difference between `[PreGaloisCategory C] (F : C ⥤ FintypeCat) [FiberFunctor F]` and
`[GaloisCategory C]` is that the former fixes one fiber functor `F`.
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

/-- Definition of a fiber functor from a Galois category. Lenstra, Def 3.1, (G4)-(G6) -/
class FiberFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  /-- `F` preserves terminal objects (G4). -/
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F := by
    infer_instance
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
  reflectsIsos : F.ReflectsIsomorphisms := by infer_instance

/-- An object of a category `C` is connected if it is not initial
and has no non-trivial subobjects. Lenstra, 3.12. -/
class IsConnected {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  /-- `X` is not an initial object. -/
  notInitial : IsInitial X → False
  /-- `X` has no non-trivial subobjects. -/
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

/-- A functor is said to preserve connectedness if whenever `X : C` is connected,
also `F.obj X` is connected. -/
class PreservesIsConnected {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
    [Category.{v₂, v₁} D] (F : C ⥤ D) : Prop where
  /-- `F.obj X` is connected if `X` is connected. -/
  preserves : ∀ {X : C} [IsConnected X], IsConnected (F.obj X)

variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups

instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks

instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C

instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

namespace FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FiberFunctor F]

attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis
  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups

noncomputable instance : ReflectsLimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsLimitsOfShapeOfReflectsIsomorphisms

noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShapeOfReflectsIsomorphisms

noncomputable instance : PreservesFiniteLimits F :=
  preservesFiniteLimitsOfPreservesTerminalAndPullbacks F

/-- Fiber functors reflect monomorphisms. -/
instance : ReflectsMonomorphisms F := ReflectsMonomorphisms.mk <| by
  intro X Y f _
  haveI : IsIso (pullback.fst : pullback (F.map f) (F.map f) ⟶ F.obj X) :=
    fst_iso_of_mono_eq (F.map f)
  haveI : IsIso (F.map (pullback.fst : pullback f f ⟶ X)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  haveI : IsIso (pullback.fst : pullback f f ⟶ X) := isIso_of_reflects_iso pullback.fst F
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst

/-- Fiber functors are faithful. -/
instance : F.Faithful where
  map_injective {X Y} f g h := by
    haveI : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    haveI : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    haveI : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

end FiberFunctor

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- An object is initial if and only if its fiber is empty. -/
lemma initial_iff_fiber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  haveI : PreservesFiniteColimits (forget FintypeCat) := by
    show PreservesFiniteColimits FintypeCat.incl
    infer_instance
  haveI : ReflectsColimit (Functor.empty.{0} _) (forget FintypeCat) := by
    show ReflectsColimit (Functor.empty.{0} _) FintypeCat.incl
    infer_instance
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

/-- An object is not initial if and only if its fiber is nonempty. -/
lemma not_initial_iff_fiber_nonempty (X : C) : (IsInitial X → False) ↔ Nonempty (F.obj X) := by
  rw [← not_isEmpty_iff]
  refine ⟨fun h he ↦ ?_, fun h hin ↦ h <| (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h

/-- An object whose fiber is inhabited is not initial. -/
lemma not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False :=
  ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x

/-- An object that is neither initial or connected has a non-trivial subobject. -/
lemma has_non_trivial_subobject_of_not_isConnected_of_not_initial (X : C) (hc : ¬ IsConnected X)
    (hi : IsInitial X → False) :
    ∃ (Y : C) (v : Y ⟶ X), (IsInitial Y → False) ∧ Mono v ∧ (¬ IsIso v) := by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni ↦ hc Y i hni hm⟩

/-- The fiber of a connected object is nonempty. -/
instance nonempty_fiber_of_isConnected (X : C) [IsConnected X] : Nonempty (F.obj X) := by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fiber_empty F X).mpr (not_nonempty_iff.mp h)
  exact IsConnected.notInitial hin

/-- The fiber of the equalizer of `f g : X ⟶ Y` is equivalent to the set of agreement of `f`
and `g`. -/
noncomputable def fiberEqualizerEquiv {X Y : C} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃ { x : F.obj X // F.map f x = F.map g x } :=
  (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
  Types.equalizerIso (F.map f) (F.map g)).toEquiv

@[simp]
lemma fiberEqualizerEquiv_symm_ι_apply {X Y : C} {f g : X ⟶ Y} (x : F.obj X)
    (h : F.map f x = F.map g x) :
    F.map (equalizer.ι f g) ((fiberEqualizerEquiv F f g).symm ⟨x, h⟩) = x := by
  simp [fiberEqualizerEquiv]
  change ((Types.equalizerIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map (equalizer.ι f g)) _ = _
  erw [PreservesEqualizer.iso_inv_ι, Types.equalizerIso_inv_comp_ι]

/-- The fiber of the pullback is the fiber product of the fibers. -/
noncomputable def fiberPullbackEquiv {X A B : C} (f : A ⟶ X) (g : B ⟶ X) :
    F.obj (pullback f g) ≃ { p : F.obj A × F.obj B // F.map f p.1 = F.map g p.2 } :=
  (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
  Types.pullbackIsoPullback (F.map f) (F.map g)).toEquiv

@[simp]
lemma fiberPullbackEquiv_symm_fst_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map pullback.fst ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = a := by
  simp [fiberPullbackEquiv]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map pullback.fst) _ = _
  erw [PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst]

@[simp]
lemma fiberPullbackEquiv_symm_snd_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map pullback.snd ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = b := by
  simp [fiberPullbackEquiv]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map pullback.snd) _ = _
  erw [PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd]

/-- The fiber of the binary product is the binary product of the fibers. -/
noncomputable def fiberBinaryProductEquiv (X Y : C) :
    F.obj (X ⨯ Y) ≃ F.obj X × F.obj Y :=
  (PreservesLimitPair.iso (F ⋙ FintypeCat.incl) X Y ≪≫
  Types.binaryProductIso (F.obj X) (F.obj Y)).toEquiv

@[simp]
lemma fiberBinaryProductEquiv_symm_fst_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.fst ((fiberBinaryProductEquiv F X Y).symm (x, y)) = x := by
  simp only [fiberBinaryProductEquiv, comp_obj, FintypeCat.incl_obj, Iso.toEquiv_comp,
    Equiv.symm_trans_apply, Iso.toEquiv_symm_fun]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.fst) _ = _
  erw [PreservesLimitPair.iso_inv_fst, Types.binaryProductIso_inv_comp_fst]

@[simp]
lemma fiberBinaryProductEquiv_symm_snd_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.snd ((fiberBinaryProductEquiv F X Y).symm (x, y)) = y := by
  simp only [fiberBinaryProductEquiv, comp_obj, FintypeCat.incl_obj, Iso.toEquiv_comp,
    Equiv.symm_trans_apply, Iso.toEquiv_symm_fun]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.snd) _ = _
  erw [PreservesLimitPair.iso_inv_snd, Types.binaryProductIso_inv_comp_snd]

/-- The evaluation map is injective for connected objects. -/
lemma evaluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun (f : A ⟶ X) ↦ F.map f a) := by
  intro f g (h : F.map f a = F.map g a)
  haveI : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fiberEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer

/-- The evaluation map on automorphisms is injective for connected objects. -/
lemma evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun f : Aut A ↦ F.map (f.hom) a) := by
  show Function.Injective ((fun f : A ⟶ A ↦ F.map f a) ∘ (fun f : Aut A ↦ f.hom))
  apply Function.Injective.comp
  · exact evaluation_injective_of_isConnected F A A a
  · exact @Aut.ext _ _ A

/-- A morphism from an object `X` with non-empty fiber to a connected object `A` is an
epimorphism. -/
lemma epi_of_nonempty_of_isConnected {X A : C} [IsConnected A] [h : Nonempty (F.obj X)]
    (f : X ⟶ A) : Epi f := Epi.mk <| fun {Z} u v huv ↦ by
  apply evaluation_injective_of_isConnected F A Z (F.map f (Classical.arbitrary _))
  simpa using congr_fun (F.congr_map huv) _

/-- An epimorphism induces a surjective map on fibers. -/
lemma surjective_on_fiber_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjective (F.map f) :=
  surjective_of_epi (FintypeCat.incl.map (F.map f))

/- A morphism from an object with non-empty fiber to a connected object is surjective on fibers. -/
lemma surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
    [IsConnected A] (f : X ⟶ A) :
    Function.Surjective (F.map f) := by
  have : Epi f := epi_of_nonempty_of_isConnected F f
  exact surjective_on_fiber_of_epi F f

section CardFiber

open ConcreteCategory

/-- A mono between objects with equally sized fibers is an iso. -/
lemma isIso_of_mono_of_eq_card_fiber {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : Nat.card (F.obj X) = Nat.card (F.obj Y)) : IsIso f := by
  have : IsIso (F.map f) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    refine ⟨injective_of_mono_of_preservesPullback (F.map f), ?_⟩
    simp only [← Nat.card_eq_fintype_card, h]
  exact isIso_of_reflects_iso f F

/-- Along a mono that is not an iso, the cardinality of the fiber strictly increases. -/
lemma lt_card_fiber_of_mono_of_notIso {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : ¬ IsIso f) : Nat.card (F.obj X) < Nat.card (F.obj Y) := by
  by_contra hlt
  apply h
  apply isIso_of_mono_of_eq_card_fiber F f
  simp only [gt_iff_lt, not_lt] at hlt
  exact Nat.le_antisymm
    (Finite.card_le_of_injective (F.map f) (injective_of_mono_of_preservesPullback (F.map f))) hlt

/-- The cardinality of the fiber of a not-initial object is non-zero. -/
lemma non_zero_card_fiber_of_not_initial (X : C) (h : IsInitial X → False) :
    Nat.card (F.obj X) ≠ 0 := by
  intro hzero
  refine Nonempty.elim ?_ h
  rw [initial_iff_fiber_empty F]
  exact Finite.card_eq_zero_iff.mp hzero

/-- The cardinality of the fiber of a coproduct is the sum of the cardinalities of the fibers. -/
lemma card_fiber_coprod_eq_sum (X Y : C) :
    Nat.card (F.obj (X ⨿ Y)) = Nat.card (F.obj X) + Nat.card (F.obj Y) := by
  let e : F.obj (X ⨿ Y) ≃ F.obj X ⊕ F.obj Y := Iso.toEquiv
    <| (PreservesColimitPair.iso (F ⋙ FintypeCat.incl) X Y).symm.trans
    <| Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [← Nat.card_sum]
  exact Nat.card_eq_of_bijective e.toFun (Equiv.bijective e)

/-- The cardinality of the fiber is preserved under isomorphisms. -/
lemma card_fiber_eq_of_iso {X Y : C} (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

/-- The cardinality of morphisms `A ⟶ X` is smaller than the cardinality of
the fiber of the target if the source is connected. -/
lemma card_hom_le_card_fiber_of_connected (A X : C) [IsConnected A] :
    Nat.card (A ⟶ X) ≤ Nat.card (F.obj X) := by
  apply Nat.card_le_card_of_injective
  exact evaluation_injective_of_isConnected F A X (Classical.arbitrary _)

/-- If `A` is connected, the cardinality of `Aut A` is smaller than the cardinality of the
fiber of `A`. -/
lemma card_aut_le_card_fiber_of_connected (A : C) [IsConnected A] :
    Nat.card (Aut A) ≤ Nat.card (F.obj A) := by
  have h : Nonempty (F.obj A) := inferInstance
  obtain ⟨a⟩ := h
  apply Nat.card_le_card_of_injective
  exact evaluation_aut_injective_of_isConnected _ _ a

end CardFiber

end PreGaloisCategory

/-- A `PreGaloisCategory` is a `GaloisCategory` if it admits a fiber functor. -/
class GaloisCategory (C : Type u₁) [Category.{u₂, u₁} C]
    extends PreGaloisCategory C : Prop where
  hasFiberFunctor : ∃ F : C ⥤ FintypeCat.{u₂}, Nonempty (PreGaloisCategory.FiberFunctor F)

namespace PreGaloisCategory

variable (C : Type u₁) [Category.{u₂, u₁} C] [GaloisCategory C]

/-- Arbitrarily choose a fiber functor for a Galois category using choice. -/
noncomputable def GaloisCategory.getFiberFunctor : C ⥤ FintypeCat.{u₂} :=
  Classical.choose <| @GaloisCategory.hasFiberFunctor C _ _

/-- The arbitrarily chosen fiber functor `GaloisCategory.getFiberFunctor` is a fiber functor. -/
noncomputable instance : FiberFunctor (GaloisCategory.getFiberFunctor C) :=
  Classical.choice <| Classical.choose_spec (@GaloisCategory.hasFiberFunctor C _ _)

variable {C}

/-- In a `GaloisCategory` the set of morphisms out of a connected object is finite. -/
instance (A X : C) [IsConnected A] : Finite (A ⟶ X) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f ↦ F.map f a)
  exact evaluation_injective_of_isConnected F A X a

/-- In a `GaloisCategory` the set of automorphism of a connected object is finite. -/
instance (A : C) [IsConnected A] : Finite (Aut A) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f ↦ F.map f.hom a)
  exact evaluation_aut_injective_of_isConnected F A a

/-- Coproduct inclusions are monic in Galois categories. -/
instance : MonoCoprod C := by
  let F := GaloisCategory.getFiberFunctor C
  exact MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono F

end PreGaloisCategory

end CategoryTheory
