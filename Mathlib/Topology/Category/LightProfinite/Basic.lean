/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory
/-!

# Light profinite sets

This file contains the basic definitions related to light profinite sets.

## Main definitions

* `LightProfinite` is a structure containing the data of a sequential limit (in `Profinite`) of
  finite sets.

* `lightToProfinite` is the fully faithful embedding of `LightProfinite` in `Profinite`.

* `LightProfinite.equivSmall` is an equivalence from `LightProfinite` to a small category. In other
  words, `LightProfinite` is *essentially small*.
-/

universe u

open CategoryTheory Limits Opposite FintypeCat

-- This was a global instance prior to #13170. We may experiment with removing it.
attribute [local instance] ConcreteCategory.instFunLike

/-- A light profinite set is one which can be written as a sequential limit of finite sets. -/
structure LightProfinite : Type (u+1) where
  /-- The indexing diagram. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat
  /-- The limit cone. -/
  cone : Cone (diagram ⋙ FintypeCat.toProfinite.{u})
  /-- The limit cone is limiting. -/
  isLimit : IsLimit cone

/-- A finite set can be regarded as a light profinite set as the limit of the constant diagram. -/
@[simps]
def FintypeCat.toLightProfinite (X : FintypeCat) : LightProfinite where
  diagram := (Functor.const _).obj X
  cone := {
    pt := toProfinite.obj X
    π := (Iso.refl _).hom }
  isLimit := {
    lift := fun s ↦ s.π.app ⟨0⟩
    fac := fun s j ↦ (s.π.naturality (homOfLE (zero_le (unop j))).op)
    uniq := fun _ _ h ↦ h ⟨0⟩ }

namespace LightProfinite

@[ext]
theorem ext {Y : LightProfinite} {a b : Y.cone.pt}
    (h : ∀ n, Y.cone.π.app n a = Y.cone.π.app n b) : a = b := by
  have : PreservesLimitsOfSize.{0, 0} (forget Profinite) := preservesLimitsOfSizeShrink _
  exact Concrete.isLimit_ext _ Y.isLimit _ _ h

/--
Given a functor from `ℕᵒᵖ` to finite sets we can take its limit in `Profinite` and obtain a light
profinite set. 
-/
@[simps]
noncomputable def of (F : ℕᵒᵖ ⥤ FintypeCat) : LightProfinite.{u} where
  diagram := F
  isLimit := limit.isLimit (F ⋙ FintypeCat.toProfinite)

/-- The underlying `Profinite` of a `LightProfinite`. -/
def toProfinite (S : LightProfinite) : Profinite := S.cone.pt

@[simps!]
instance : Category LightProfinite := InducedCategory.category toProfinite

instance concreteCategory : ConcreteCategory LightProfinite := InducedCategory.concreteCategory _

/-- The fully faithful embedding `LightProfinite ⥤ Profinite` -/
@[simps!]
def lightToProfinite : LightProfinite ⥤ Profinite := inducedFunctor _

instance : lightToProfinite.Faithful := show (inducedFunctor _).Faithful from inferInstance

instance : lightToProfinite.Full := show (inducedFunctor _).Full from inferInstance

instance {X : LightProfinite} : TopologicalSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TopologicalSpace X.cone.pt)

instance {X : LightProfinite} : TotallyDisconnectedSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TotallyDisconnectedSpace X.cone.pt)

instance {X : LightProfinite} : CompactSpace ((forget LightProfinite).obj X) :=
  (inferInstance : CompactSpace X.cone.pt )

instance {X : LightProfinite} : T2Space ((forget LightProfinite).obj X) :=
  (inferInstance : T2Space X.cone.pt )

/-- The explicit functor `FintypeCat ⥤ LightProfinite`.  -/
@[simps]
def fintypeCatToLightProfinite : FintypeCat ⥤ LightProfinite.{u} where
  obj X := X.toLightProfinite
  map f := FintypeCat.toProfinite.map f

instance : fintypeCatToLightProfinite.Faithful where
  map_injective h := funext fun _ ↦ (DFunLike.ext_iff.mp h) _

instance : fintypeCatToLightProfinite.Full where
  map_surjective f := ⟨fun x ↦ f x, rfl⟩

/-- The fully faithful embedding of `LightProfinite` in `TopCat`. -/
@[simps!]
def toTopCat : LightProfinite ⥤ TopCat :=
  lightToProfinite ⋙ Profinite.toTopCat

instance : toTopCat.Faithful := Functor.Faithful.comp _ _

instance : toTopCat.Full := Functor.Full.comp _ _

end LightProfinite

noncomputable section EssentiallySmall

open LightProfinite

/-- This is an auxiliary definition used to show that `LightProfinite` is essentially small. -/
structure LightProfinite' : Type u where
  /-- The diagram takes values in a small category equivalent to `FintypeCat`. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat.Skeleton.{u}

/-- A `LightProfinite'` yields a `Profinite`. -/
def LightProfinite'.toProfinite (S : LightProfinite') : Profinite :=
  limit (S.diagram  ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

instance : Category LightProfinite' := InducedCategory.category LightProfinite'.toProfinite

/-- The functor part of the equivalence of categories `LightProfinite' ≌ LightProfinite`. -/
def LightProfinite'.toLightFunctor : LightProfinite'.{u} ⥤ LightProfinite.{u} where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

instance : LightProfinite'.toLightFunctor.{u}.Faithful := ⟨id⟩

instance : LightProfinite'.toLightFunctor.{u}.Full where
  map_surjective f := ⟨f, rfl⟩

instance : LightProfinite'.toLightFunctor.{u}.EssSurj where
  mem_essImage Y :=
    ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨lightToProfinite.preimageIso (
      (Limits.lim.mapIso (isoWhiskerRight ((isoWhiskerLeft Y.diagram
      Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso Y.isLimit)⟩⟩

instance : LightProfinite'.toLightFunctor.IsEquivalence where

/-- The equivalence beween `LightProfinite` and a small category. -/
def LightProfinite.equivSmall : LightProfinite.{u} ≌ LightProfinite'.{u} :=
  LightProfinite'.toLightFunctor.asEquivalence.symm

instance : EssentiallySmall LightProfinite.{u} where
  equiv_smallCategory := ⟨LightProfinite', inferInstance, ⟨LightProfinite.equivSmall⟩⟩

end EssentiallySmall
