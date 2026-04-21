/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Profinite

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `TopCat`. The fully faithful functor
is called `Profinite.toTop`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

The category `Profinite` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

## TODO

* Define procategories and prove that `Profinite` is equivalent to `Pro (FintypeCat)`.

## Tags

profinite

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v u

open CategoryTheory Topology CompHausLike

/-- The type of profinite topological spaces. -/
@[to_additive_do_translate] -- This is required
abbrev Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)

namespace Profinite

instance (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : HasProp (fun Y ↦ TotallyDisconnectedSpace Y) X :=
  ⟨(inferInstance : TotallyDisconnectedSpace X)⟩

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] : Profinite :=
  CompHausLike.of _ X

instance : Inhabited Profinite :=
  ⟨Profinite.of PEmpty⟩

instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.prop

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
abbrev profiniteToCompHaus : Profinite ⥤ CompHaus :=
  compHausLikeToCompHaus _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance {X : Profinite} : TotallyDisconnectedSpace (profiniteToCompHaus.obj X) :=
  X.prop

/-- The fully faithful embedding of `Profinite` in `TopCat`.
This is definitionally the same as the obvious composite. -/
abbrev Profinite.toTopCat : Profinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

section Profinite

-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
/--
(Implementation) The object part of the `connectedComponents` functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components. -/
@[stacks 0900]
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toTop := TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := ofHom _ (f.hom.hom.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩)
  invFun g := ConcreteCategory.ofHom
    { toFun := Continuous.connectedComponentsLift g.hom.hom.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.hom.hom.2 }
  left_inv f :=
    InducedCategory.hom_ext (TopCat.ext (fun y ↦ by
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
      rfl))

/-- The `connectedComponents` functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl

theorem CompHaus.toProfinite_obj' (X : CompHaus) :
    ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl

/-- Finite types are given the discrete topology. -/
@[instance_reducible]
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A := ⊥

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩

attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps! -isSimp map_hom_hom_apply obj]
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite where
  obj A := Profinite.of A
  map f := ofHom _ ⟨f, by fun_prop⟩

/-- `FintypeCat.toLightProfinite` is fully faithful. -/
def FintypeCat.toProfiniteFullyFaithful : toProfinite.FullyFaithful where
  preimage f := InducedCategory.homMk <| TypeCat.ofHom (f : _ → _)
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : FintypeCat.toProfinite.Faithful := FintypeCat.toProfiniteFullyFaithful.faithful

instance : FintypeCat.toProfinite.Full := FintypeCat.toProfiniteFullyFaithful.full

instance (X : FintypeCat) : Finite (FintypeCat.toProfinite.obj X) := inferInstanceAs (Finite X)

instance (X : FintypeCat) : Finite (Profinite.of X) := inferInstanceAs (Finite X)

end DiscreteTopology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app j := InducedCategory.homMk
        (((CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).π.app j).hom)
    -- Porting note: was `by tidy`:
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/-- The limit cone `Profinite.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    InducedCategory.homMk
      ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
        (profiniteToCompHaus.mapCone S)).hom
  uniq S _ h :=
    profiniteToCompHaus.map_injective
      ((CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _
        (fun j ↦ by
          simp [← h]
          rfl))

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The category of profinite sets is reflective in the category of compact Hausdorff spaces -/
instance toCompHaus.reflective : Reflective profiniteToCompHaus where
  L := CompHaus.toProfinite
  adj := Profinite.toProfiniteAdjToCompHaus

noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _

noncomputable instance toTopCat.reflective : Reflective Profinite.toTopCat :=
  Reflective.comp profiniteToCompHaus compHausToTop

noncomputable instance toTopCat.createsLimits : CreatesLimits Profinite.toTopCat :=
  monadicCreatesLimits _

instance hasLimits : Limits.HasLimits Profinite :=
  hasLimits_of_hasLimits_createsLimits Profinite.toTopCat

instance hasColimits : Limits.HasColimits Profinite :=
  hasColimits_of_reflective profiniteToCompHaus

instance forget_preservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply Limits.comp_preservesLimits Profinite.toTopCat (forget TopCat)

set_option backward.isDefEq.respectTransparency false in
theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := ofHom _
        ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ofHom _ ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        dsimp [g, LocallyConstant.ofIsClopen]
        rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, ConcreteCategory.hom_ofHom,
          ContinuousMap.coe_mk, Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp [U, C]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map

/-- The pi-type of profinite spaces is profinite. -/
def pi {α : Type u} (β : α → Profinite) : Profinite := .of (Π (a : α), β a)

end Profinite
