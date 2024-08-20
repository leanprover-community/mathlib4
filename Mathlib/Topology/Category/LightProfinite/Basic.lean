/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.ClopenBox
/-!

# Light profinite spaces

We construct the category `LightProfinite` of light profinite topological spaces. These are
implemented as totally disconnected second countable compact Hausdorff spaces.

This file also defines the category `LightDiagram`, which consists of those spaces that can be
written as a sequential limit (in `Profinite`) of finite sets.

We define an equivalence of categories `LightProfinite ≌ LightDiagram` and prove that these are
essentially small categories.

## Implementation

The category `LightProfinite` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

/- The basic API for `LightProfinite` is largely copied from the API of `Profinite`;
where possible, try to keep them in sync -/

universe v u

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits Opposite FintypeCat Topology TopologicalSpace CompHausLike

/-- `LightProfinite` is the category of second countable profinite spaces. -/
abbrev LightProfinite := CompHausLike
  (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)

namespace LightProfinite

instance (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] : HasProp (fun Y ↦
      TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) X :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace X), (inferInstance : SecondCountableTopology X)⟩⟩

/--
Construct a term of `LightProfinite` from a type endowed with the structure of a compact,
Hausdorff, totally disconnected and second countable topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] : LightProfinite :=
  CompHausLike.of _ X

instance : Inhabited LightProfinite :=
  ⟨LightProfinite.of PEmpty⟩

instance {X : LightProfinite} : TotallyDisconnectedSpace X :=
  X.prop.1

instance {X : LightProfinite} : SecondCountableTopology X :=
  X.prop.2

instance {X : LightProfinite} : TotallyDisconnectedSpace ((forget LightProfinite).obj X) :=
  X.prop.1

instance {X : LightProfinite} : SecondCountableTopology ((forget LightProfinite).obj X) :=
  X.prop.2

end LightProfinite

/-- The fully faithful embedding of `LightProfinite` in `Profinite`. -/
abbrev lightToProfinite : LightProfinite ⥤ Profinite :=
  CompHausLike.toCompHausLike (fun _ ↦ inferInstance)

/-- `lightToProfinite` is fully faithful. -/
abbrev lightToProfiniteFullyFaithful : lightToProfinite.FullyFaithful :=
  fullyFaithfulToCompHausLike _

/-- The fully faithful embedding of `LightProfinite` in `CompHaus`. -/
abbrev lightProfiniteToCompHaus : LightProfinite ⥤ CompHaus :=
  compHausLikeToCompHaus _

/-- The fully faithful embedding of `LightProfinite` in `TopCat`.
This is definitionally the same as the obvious composite. -/
abbrev LightProfinite.toTopCat : LightProfinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology
attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `LightProfinite`, endowing a finite type with the
discrete topology. -/
@[simps!]
def FintypeCat.toLightProfinite : FintypeCat ⥤ LightProfinite where
  obj A := LightProfinite.of A
  map f := ⟨f, by continuity⟩

attribute [nolint simpNF] FintypeCat.toLightProfinite_map_apply

/-- `FintypeCat.toLightProfinite` is fully faithful. -/
def FintypeCat.toLightProfiniteFullyFaithful : toLightProfinite.FullyFaithful where
  preimage f := (f : _ → _)
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : FintypeCat.toLightProfinite.Faithful :=
  FintypeCat.toLightProfiniteFullyFaithful.faithful

instance : FintypeCat.toLightProfinite.Full :=
  FintypeCat.toLightProfiniteFullyFaithful.full

instance (X : FintypeCat.{u}) : Fintype (FintypeCat.toLightProfinite.obj X) :=
  inferInstanceAs (Fintype X)

instance (X : FintypeCat.{u}) : Fintype (LightProfinite.of X) :=  inferInstanceAs (Fintype X)

end DiscreteTopology

namespace LightProfinite

instance {J : Type v} [SmallCategory J] (F : J ⥤ LightProfinite.{max u v}) :
    TotallyDisconnectedSpace
      (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop := by
  change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
  exact Subtype.totallyDisconnectedSpace

/-- An explicit limit cone for a functor `F : J ⥤ LightProfinite`, for a countable category `J`
  defined in terms of `CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightProfinite.{max u v}) :
    Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop
      prop := by
        constructor
        · infer_instance
        · change SecondCountableTopology ({ u : ∀ j : J, F.obj j | _ } : Type _)
          apply IsInducing.subtypeVal.secondCountableTopology }
  π :=
  { app := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).π.app
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/-- The limit cone `LightProfinite.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightProfinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    (CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightProfiniteToCompHaus)).lift
      (lightProfiniteToCompHaus.mapCone S)
  uniq S _ h := (CompHaus.limitConeIsLimit.{v, u} _).uniq (lightProfiniteToCompHaus.mapCone S) _ h

noncomputable instance createsCountableLimits {J : Type v} [SmallCategory J] [CountableCategory J] :
    CreatesLimitsOfShape J lightToProfinite.{max v u} where
  CreatesLimit {F} :=
    have : HasLimitsOfSize Profinite := hasLimitsOfSizeShrink _
    createsLimitOfFullyFaithfulOfIso (limitCone.{v, u} F).pt <|
      (Profinite.limitConeIsLimit.{v, u} (F ⋙ lightToProfinite)).conePointUniqueUpToIso
        (limit.isLimit _)

instance : HasCountableLimits LightProfinite where
  out _ := { has_limit := fun F ↦ ⟨limitCone F, limitConeIsLimit F⟩ }

noncomputable instance : PreservesLimitsOfShape ℕᵒᵖ (forget LightProfinite.{u}) :=
  have : PreservesLimitsOfSize.{0, 0} (forget Profinite.{u}) := preservesLimitsOfSizeShrink _
  inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (lightToProfinite ⋙ forget Profinite))

variable {X Y : LightProfinite.{u}} (f : X ⟶ Y)

/-- Any morphism of light profinite spaces is a closed map. -/
theorem isClosedMap : IsClosedMap f :=
  CompHausLike.isClosedMap _

/-- Any continuous bijection of light profinite spaces induces an isomorphism. -/
theorem isIso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHausLike.isIso_of_bijective (lightProfiniteToCompHaus.map f) bij
  isIso_of_fully_faithful lightProfiniteToCompHaus _

/-- Any continuous bijection of light profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := LightProfinite.isIso_of_bijective f bij
  asIso f

instance forget_reflectsIsomorphisms : (forget LightProfinite).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  exact LightProfinite.isIso_of_bijective _ ((isIso_iff_bijective f).mp hf)

theorem epi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · -- Note: in mathlib3 `contrapose` saw through `Function.Surjective`.
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [g, LocallyConstant.ofIsClopen]
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [CategoryTheory.comp_apply, ContinuousMap.coe_mk,
          CategoryTheory.comp_apply, ContinuousMap.coe_mk, Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp only [U, C, Set.mem_range_self, not_true, not_false_iff, Set.mem_compl_iff]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

instance : lightToProfinite.PreservesEpimorphisms where
  preserves f _ := (Profinite.epi_iff_surjective _).mpr ((epi_iff_surjective f).mp inferInstance)

end LightProfinite

/-- A structure containing the data of sequential limit in `Profinite` of finite sets. -/
structure LightDiagram : Type (u+1) where
  /-- The indexing diagram. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat
  /-- The limit cone. -/
  cone : Cone (diagram ⋙ FintypeCat.toProfinite.{u})
  /-- The limit cone is limiting. -/
  isLimit : IsLimit cone

namespace LightDiagram

/-- The underlying `Profinite` of a `LightDiagram`. -/
def toProfinite (S : LightDiagram) : Profinite := S.cone.pt

@[simps!]
instance : Category LightDiagram := InducedCategory.category toProfinite

instance concreteCategory : ConcreteCategory LightDiagram := InducedCategory.concreteCategory _

end LightDiagram

/-- The fully faithful embedding `LightDiagram ⥤ Profinite` -/
@[simps!]
def lightDiagramToProfinite : LightDiagram ⥤ Profinite := inducedFunctor _

instance : lightDiagramToProfinite.Faithful := show (inducedFunctor _).Faithful from inferInstance

instance : lightDiagramToProfinite.Full := show (inducedFunctor _).Full from inferInstance

instance {X : LightDiagram} : TopologicalSpace ((forget LightDiagram).obj X) :=
  (inferInstance : TopologicalSpace X.cone.pt)

instance {X : LightDiagram} : TotallyDisconnectedSpace ((forget LightDiagram).obj X) :=
  (inferInstance : TotallyDisconnectedSpace X.cone.pt)

instance {X : LightDiagram} : CompactSpace ((forget LightDiagram).obj X) :=
  (inferInstance : CompactSpace X.cone.pt )

instance {X : LightDiagram} : T2Space ((forget LightDiagram).obj X) :=
  (inferInstance : T2Space X.cone.pt )

namespace LightProfinite

instance (S : LightProfinite) : Countable (Clopens S) := by
  rw [TopologicalSpace.Clopens.countable_iff_second_countable]
  infer_instance

instance instCountableDiscreteQuotient (S : LightProfinite)  :
    Countable (DiscreteQuotient ((lightToProfinite.obj S))) :=
  (DiscreteQuotient.finsetClopens_inj S).countable

/-- A profinite space which is light gives rise to a light profinite space. -/
noncomputable def toLightDiagram (S : LightProfinite.{u}) : LightDiagram.{u} where
  diagram := sequentialFunctor _ ⋙ (lightToProfinite.obj S).fintypeDiagram
  cone := (Functor.Initial.limitConeComp (sequentialFunctor _) (lightToProfinite.obj S).lim).cone
  isLimit :=
    (Functor.Initial.limitConeComp (sequentialFunctor _) (lightToProfinite.obj S).lim).isLimit

end LightProfinite

/-- The functor part of the equivalence `LightProfinite ≌ LightDiagram` -/
@[simps]
noncomputable def lightProfiniteToLightDiagram : LightProfinite.{u} ⥤ LightDiagram.{u} where
  obj X := X.toLightDiagram
  map f := f

open scoped Classical in
instance (S : LightDiagram.{u}) : SecondCountableTopology S.cone.pt := by
  rw [← TopologicalSpace.Clopens.countable_iff_second_countable]
  refine @Countable.of_equiv _ _ ?_ (LocallyConstant.equivClopens (X := S.cone.pt))
  refine @Function.Surjective.countable
    (Σ (n : ℕ), LocallyConstant ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩) (Fin 2)) _ ?_ ?_ ?_
  · apply @instCountableSigma _ _ _ ?_
    intro n
    refine @Finite.to_countable _ ?_
    refine @Finite.of_injective _ ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩ → (Fin 2)) ?_ _
      LocallyConstant.coe_injective
    refine @Pi.finite _ _ ?_ _
    simp only [Functor.comp_obj]
    exact show (Finite (S.diagram.obj _)) from inferInstance
  · exact fun a ↦ a.snd.comap (S.cone.π.app ⟨a.fst⟩)
  · intro a
    obtain ⟨n, g, h⟩ := Profinite.exists_locallyConstant S.cone S.isLimit a
    exact ⟨⟨unop n, g⟩, h.symm⟩

/-- The inverse part of the equivalence `LightProfinite ≌ LightDiagram` -/
@[simps]
def lightDiagramToLightProfinite : LightDiagram.{u} ⥤ LightProfinite.{u} where
  obj X := LightProfinite.of X.cone.pt
  map f := f

/-- The equivalence of categories `LightProfinite ≌ LightDiagram` -/
noncomputable def LightProfinite.equivDiagram : LightProfinite.{u} ≌ LightDiagram.{u} where
  functor := lightProfiniteToLightDiagram
  inverse := lightDiagramToLightProfinite
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun _ ↦ lightDiagramToProfinite.preimageIso (Iso.refl _)) (by
      intro _ _ f
      simp only [Functor.comp_obj, lightDiagramToLightProfinite_obj,
        lightProfiniteToLightDiagram_obj, Functor.id_obj, Functor.comp_map,
        lightDiagramToLightProfinite_map, lightProfiniteToLightDiagram_map,
        lightDiagramToProfinite_obj, Functor.preimageIso_hom, Iso.refl_hom, Functor.id_map]
      erw [lightDiagramToProfinite.preimage_id, lightDiagramToProfinite.preimage_id,
        Category.comp_id f])
  functor_unitIso_comp _ := by simpa using lightDiagramToProfinite.preimage_id

instance : lightProfiniteToLightDiagram.IsEquivalence :=
  show LightProfinite.equivDiagram.functor.IsEquivalence from inferInstance

instance : lightDiagramToLightProfinite.IsEquivalence :=
  show LightProfinite.equivDiagram.inverse.IsEquivalence from inferInstance

noncomputable section EssentiallySmall

open LightDiagram

/--
This is an auxiliary definition used to show that `LightDiagram` is essentially small.

Note that below we put a category instance on this structure which is completely different from the
category instance on `ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}`. Neither the morphisms nor the objects are the
same.
-/
structure LightDiagram' : Type u where
  /-- The diagram takes values in a small category equivalent to `FintypeCat`. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}

/-- A `LightDiagram'` yields a `Profinite`. -/
def LightDiagram'.toProfinite (S : LightDiagram') : Profinite :=
  limit (S.diagram  ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

instance : Category LightDiagram' := InducedCategory.category LightDiagram'.toProfinite

/-- The functor part of the equivalence of categories `LightDiagram' ≌ LightDiagram`. -/
def LightDiagram'.toLightFunctor : LightDiagram'.{u} ⥤ LightDiagram.{u} where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

instance : LightDiagram'.toLightFunctor.{u}.Faithful := ⟨id⟩

instance : LightDiagram'.toLightFunctor.{u}.Full where
  map_surjective f := ⟨f, rfl⟩

instance : LightDiagram'.toLightFunctor.{u}.EssSurj where
  mem_essImage Y :=
    ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨lightDiagramToProfinite.preimageIso (
      (Limits.lim.mapIso (isoWhiskerRight ((isoWhiskerLeft Y.diagram
      Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso Y.isLimit)⟩⟩

instance : LightDiagram'.toLightFunctor.IsEquivalence where

/-- The equivalence between `LightDiagram` and a small category. -/
def LightDiagram.equivSmall : LightDiagram.{u} ≌ LightDiagram'.{u} :=
  LightDiagram'.toLightFunctor.asEquivalence.symm

instance : EssentiallySmall.{u} LightDiagram.{u} where
  equiv_smallCategory := ⟨LightDiagram', inferInstance, ⟨LightDiagram.equivSmall⟩⟩

instance : EssentiallySmall.{u} LightProfinite.{u} where
  equiv_smallCategory := ⟨LightDiagram', inferInstance,
    ⟨LightProfinite.equivDiagram.trans LightDiagram.equivSmall⟩⟩

end EssentiallySmall
