/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RepresentationTheory.Action.Basic
import Mathlib.RepresentationTheory.Action.Concrete
import Mathlib.RepresentationTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Examples of Galois categories and fiber functors

We show that for a group `G` the category of finite `G`-sets is a `PreGaloisCategory` and that the
forgetful functor to `FintypeCat` is a `FiberFunctor`.

The connected finite `G`-sets are precisely the ones with transitive `G`-action.

-/

universe u v w

namespace CategoryTheory

namespace FintypeCat

open Limits Functor PreGaloisCategory

/-- Complement of the image of a morphism `f : X ⟶ Y` in `FintypeCat`. -/
noncomputable def imageComplement {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    FintypeCat.{u} := by
  haveI : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact FintypeCat.of (↑(Set.range f)ᶜ)

/-- The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`. -/
def imageComplementIncl {X Y : FintypeCat.{u}}
    (f : X ⟶ Y) : imageComplement f ⟶ Y :=
  Subtype.val

variable (G : Type u) [Group G]

/-- Given `f : X ⟶ Y` for `X Y : Action FintypeCat (MonCat.of G)`, the complement of the image
of `f` has a natural `G`-action. -/
noncomputable def Action.imageComplement {X Y : Action FintypeCat (MonCat.of G)}
    (f : X ⟶ Y) : Action FintypeCat (MonCat.of G) where
  V := FintypeCat.imageComplement f.hom
  ρ := MonCat.ofHom <| {
    toFun := fun g y ↦ Subtype.mk (Y.ρ g y.val) <| by
      intro ⟨x, h⟩
      apply y.property
      use X.ρ g⁻¹ x
      calc (X.ρ g⁻¹ ≫ f.hom) x
          = (Y.ρ g⁻¹ * Y.ρ g) y.val := by rw [f.comm, FintypeCat.comp_apply, h]; rfl
        _ = y.val := by rw [← map_mul, mul_left_inv, Action.ρ_one, FintypeCat.id_apply]
    map_one' := by simp only [Action.ρ_one]; rfl
    map_mul' := fun g h ↦ FintypeCat.hom_ext _ _ <| fun y ↦ Subtype.ext <| by
      exact congrFun (MonoidHom.map_mul Y.ρ g h) y.val
  }

/-- The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`. -/
def Action.imageComplementIncl {X Y : Action FintypeCat (MonCat.of G)} (f : X ⟶ Y) :
    Action.imageComplement G f ⟶ Y where
  hom := FintypeCat.imageComplementIncl f.hom
  comm _ := rfl

instance {X Y : Action FintypeCat (MonCat.of G)} (f : X ⟶ Y) :
    Mono (Action.imageComplementIncl G f) := by
  apply Functor.mono_of_mono_map (forget _)
  apply ConcreteCategory.mono_of_injective
  exact Subtype.val_injective

/-- The category of finite sets has quotients by finite groups in arbitrary universes. -/
instance [Finite G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w} := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_zero_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

noncomputable instance : PreservesFiniteLimits (forget (Action FintypeCat (MonCat.of G))) := by
  show PreservesFiniteLimits (Action.forget FintypeCat _ ⋙ FintypeCat.incl)
  apply compPreservesFiniteLimits

/-- The category of finite `G`-sets is a `PreGaloisCategory`. -/
instance : PreGaloisCategory (Action FintypeCat (MonCat.of G)) where
  hasQuotientsByFiniteGroups G _ _ := inferInstance
  monoInducesIsoOnDirectSummand {X Y} i h :=
    ⟨Action.imageComplement G i, Action.imageComplementIncl G i,
     ⟨isColimitOfReflects (Action.forget _ _ ⋙ FintypeCat.incl) <|
      (isColimitMapCoconeBinaryCofanEquiv (forget _) i _).symm
      (Types.isCoprodOfMono ((forget _).map i))⟩⟩

/-- The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`. -/
noncomputable instance : FiberFunctor (Action.forget FintypeCat (MonCat.of G)) where
  preservesFiniteCoproducts := ⟨fun _ _ ↦ inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (h : IsIso f.hom) => inferInstance⟩

/-- The category of finite `G`-sets is a `GaloisCategory`. -/
instance : GaloisCategory (Action FintypeCat (MonCat.of G)) where
  hasFiberFunctor := ⟨Action.forget FintypeCat (MonCat.of G), ⟨inferInstance⟩⟩

/-- The `G`-action on a connected finite `G`-set is transitive. -/
theorem Action.pretransitive_of_isConnected (X : Action FintypeCat (MonCat.of G))
    [IsConnected X] : MulAction.IsPretransitive G X.V where
  exists_smul_eq x y := by
    /- We show that the `G`-orbit of `x` is a non-initial subobject of `X` and hence by
    connectedness, the orbit equals `X.V`. -/
    let T : Set X.V := MulAction.orbit G x
    have : Fintype T := Fintype.ofFinite T
    letI : MulAction G (FintypeCat.of T) := inferInstanceAs <| MulAction G ↑(MulAction.orbit G x)
    let T' : Action FintypeCat (MonCat.of G) := Action.FintypeCat.ofMulAction G (FintypeCat.of T)
    let i : T' ⟶ X := ⟨Subtype.val, fun _ ↦ rfl⟩
    have : Mono i := ConcreteCategory.mono_of_injective _ (Subtype.val_injective)
    have : IsIso i := by
      apply IsConnected.noTrivialComponent T' i
      apply (not_initial_iff_fiber_nonempty (Action.forget _ _) T').mpr
      exact Set.Nonempty.coe_sort (MulAction.orbit_nonempty x)
    have hb : Function.Bijective i.hom := by
      apply (ConcreteCategory.isIso_iff_bijective i.hom).mp
      exact map_isIso (forget₂ _ FintypeCat) i
    obtain ⟨⟨y', ⟨g, (hg : g • x = y')⟩⟩, (hy' : y' = y)⟩ := hb.surjective y
    use g
    exact hg.trans hy'

/-- A nonempty `G`-set with transitive `G`-action is connected. -/
theorem Action.isConnected_of_transitive (X : FintypeCat) [MulAction G X]
    [MulAction.IsPretransitive G X] [h : Nonempty X] :
    IsConnected (Action.FintypeCat.ofMulAction G X) where
  notInitial := not_initial_of_inhabited (Action.forget _ _) h.some
  noTrivialComponent Y i hm hni := by
    /- We show that the induced inclusion `i.hom` of finite sets is surjective, using the
    transitivity of the `G`-action. -/
    obtain ⟨(y : Y.V)⟩ := (not_initial_iff_fiber_nonempty (Action.forget _ _) Y).mp hni
    have : IsIso i.hom := by
      refine (ConcreteCategory.isIso_iff_bijective i.hom).mpr ⟨?_, fun x' ↦ ?_⟩
      · haveI : Mono i.hom := map_mono (forget₂ _ _) i
        exact ConcreteCategory.injective_of_mono_of_preservesPullback i.hom
      · letI x : X := i.hom y
        obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G x x'
        use σ • y
        show (Y.ρ σ ≫ i.hom) y = x'
        rw [i.comm, FintypeCat.comp_apply]
        exact hσ
    apply isIso_of_reflects_iso i (Action.forget _ _)

/-- A nonempty finite `G`-set is connected if and only if the `G`-action is transitive. -/
theorem Action.isConnected_iff_transitive (X : Action FintypeCat (MonCat.of G)) [Nonempty X.V] :
    IsConnected X ↔ MulAction.IsPretransitive G X.V :=
  ⟨fun _ ↦ pretransitive_of_isConnected G X, fun _ ↦ isConnected_of_transitive G X.V⟩

end FintypeCat

end CategoryTheory
