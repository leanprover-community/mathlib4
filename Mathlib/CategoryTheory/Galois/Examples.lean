/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Limits

/-!
# Examples of Galois categories and fiber functors

We show that for a group `G` the category of finite `G`-sets is a `PreGaloisCategory` and that the
forgetful functor to `FintypeCat` is a `FiberFunctor`.

The connected finite `G`-sets are precisely the ones with transitive `G`-action.

-/

universe u v w

namespace CategoryTheory

open Limits Functor PreGaloisCategory

namespace FintypeCat

/-- Complement of the image of a morphism `f : X ⟶ Y` in `FintypeCat`. -/
noncomputable def imageComplement {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    FintypeCat.{u} := by
  haveI : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact FintypeCat.of (↑(Set.range f)ᶜ)

/-- The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`. -/
noncomputable def imageComplementIncl {X Y : FintypeCat.{u}}
    (f : X ⟶ Y) : imageComplement f ⟶ Y :=
  FintypeCat.homMk Subtype.val

variable (G : Type u) [Group G]

/-- Given `f : X ⟶ Y` for `X Y : Action FintypeCat G`, the complement of the image
of `f` has a natural `G`-action. -/
noncomputable def Action.imageComplement {X Y : Action FintypeCat G}
    (f : X ⟶ Y) : Action FintypeCat G where
  V := FintypeCat.imageComplement f.hom
  ρ := {
    toFun g := FintypeCat.homMk (fun y ↦ Subtype.mk ((Y.ρ g).hom y.val) <| by
      intro ⟨x, h⟩
      apply y.property
      use (X.ρ g⁻¹).hom x
      calc (X.ρ g⁻¹ ≫ f.hom) x
          = ((Y.ρ g⁻¹ * Y.ρ g)).hom y.val := by rw [f.comm, FintypeCat.comp_apply, h]; rfl
        _ = y.val := by
          rw [← map_mul, inv_mul_cancel, Action.ρ_one, FintypeCat.id_hom, id_eq])
    map_one' := by aesop
    map_mul' := by aesop
  }

/-- The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`. -/
noncomputable def Action.imageComplementIncl {X Y : Action FintypeCat G} (f : X ⟶ Y) :
    Action.imageComplement G f ⟶ Y where
  hom := FintypeCat.imageComplementIncl f.hom
  comm _ := rfl

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance {X Y : Action FintypeCat G} (f : X ⟶ Y) :
    Mono (Action.imageComplementIncl G f) := by
  apply Functor.mono_of_mono_map (forget _)
  apply ConcreteCategory.mono_of_injective
  exact Subtype.val_injective

/-- The category of finite sets has quotients by finite groups in arbitrary universes. -/
instance [Finite G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w} := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

noncomputable instance : PreservesFiniteLimits (forget (Action FintypeCat G)) := by
  change PreservesFiniteLimits (Action.forget FintypeCat _ ⋙ FintypeCat.incl)
  apply comp_preservesFiniteLimits

/-- The category of finite `G`-sets is a `PreGaloisCategory`. -/
instance : PreGaloisCategory (Action FintypeCat G) where
  hasQuotientsByFiniteGroups _ _ _ := inferInstance
  monoInducesIsoOnDirectSummand {_ _} i _ :=
    ⟨Action.imageComplement G i, Action.imageComplementIncl G i,
     ⟨isColimitOfReflects (Action.forget _ _ ⋙ FintypeCat.incl) <|
      (isColimitMapCoconeBinaryCofanEquiv (forget _) i _).symm
      (Types.isCoprodOfMono ((forget _).map i))⟩⟩

/-- The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`. -/
noncomputable instance : FiberFunctor (Action.forget FintypeCat G) where
  preservesFiniteCoproducts := ⟨fun _ ↦ inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (_ : IsIso f.hom) => inferInstance⟩

/-- The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`. -/
noncomputable instance : FiberFunctor (forget₂ (Action FintypeCat G) FintypeCat) :=
  inferInstanceAs <| FiberFunctor (Action.forget FintypeCat G)

/-- The category of finite `G`-sets is a `GaloisCategory`. -/
instance : GaloisCategory (Action FintypeCat G) where
  hasFiberFunctor := ⟨Action.forget FintypeCat G, ⟨inferInstance⟩⟩

/-- The `G`-action on a connected finite `G`-set is transitive. -/
theorem Action.pretransitive_of_isConnected (X : Action FintypeCat G)
    [IsConnected X] : MulAction.IsPretransitive G X.V where
  exists_smul_eq x y := by
    /- We show that the `G`-orbit of `x` is a non-initial subobject of `X` and hence by
    connectedness, the orbit equals `X.V`. -/
    let T : Set X.V := MulAction.orbit G x
    have : Fintype T := Fintype.ofFinite T
    letI : MulAction G (FintypeCat.of T) := inferInstanceAs <| MulAction G ↑(MulAction.orbit G x)
    let T' : Action FintypeCat G := Action.FintypeCat.ofMulAction G (FintypeCat.of T)
    let i : T' ⟶ X := ⟨FintypeCat.homMk Subtype.val, fun _ ↦ rfl⟩
    have : Mono i := ConcreteCategory.mono_of_injective _ (Subtype.val_injective)
    have : IsIso i := by
      apply IsConnected.noTrivialComponent T' i
      apply (not_initial_iff_fiber_nonempty (Action.forget _ _) T').mpr
      exact Set.Nonempty.coe_sort (MulAction.nonempty_orbit x)
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
        change (Y.ρ σ ≫ i.hom) y = x'
        rw [i.comm, FintypeCat.comp_apply]
        exact hσ
    apply isIso_of_reflects_iso i (Action.forget _ _)

/-- A nonempty finite `G`-set is connected if and only if the `G`-action is transitive. -/
theorem Action.isConnected_iff_transitive (X : Action FintypeCat G) [Nonempty X.V] :
    IsConnected X ↔ MulAction.IsPretransitive G X.V :=
  ⟨fun _ ↦ pretransitive_of_isConnected G X, fun _ ↦ isConnected_of_transitive G X.V⟩

variable {G}

/-- If `X` is a connected `G`-set and `x` is an element of `X`, `X` is isomorphic
to the quotient of `G` by the stabilizer of `x` as `G`-sets. -/
noncomputable def isoQuotientStabilizerOfIsConnected (X : Action FintypeCat G)
    [IsConnected X] (x : X.V) [Fintype (G ⧸ (MulAction.stabilizer G x))] :
    X ≅ G ⧸ₐ MulAction.stabilizer G x :=
  haveI : MulAction.IsPretransitive G X.V := Action.pretransitive_of_isConnected G X
  let e : X.V ≃ G ⧸ MulAction.stabilizer G x :=
    (Equiv.Set.univ X.V).symm.trans <|
      (Equiv.setCongr ((MulAction.orbit_eq_univ G x).symm)).trans <|
      MulAction.orbitEquivQuotientStabilizer G x
  Iso.symm <| Action.mkIso (FintypeCat.equivEquivIso e.symm) <| fun σ : G ↦ by
    ext (a : G ⧸ MulAction.stabilizer G x)
    obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
    exact mul_smul σ τ x

end FintypeCat

end CategoryTheory
