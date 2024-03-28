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

/-- A light profinite set is one which can be written as a sequential limit of finite sets. -/
structure LightProfinite : Type (u+1) where
  /-- The indexing diagram. -/
  diagram : ℕᵒᵖ ⥤ FintypeCat
  /-- The limit cone. -/
  cone : Cone (diagram ⋙ FintypeCat.toProfinite.{u})
  /-- The limit cone is limiting. -/
  isLimit : IsLimit cone

/-- A finite set can be regarded as a light profinite set as the limit of the constant diagram. -/
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
noncomputable def of (F : ℕᵒᵖ ⥤ FintypeCat) : LightProfinite where
  diagram := F
  isLimit := limit.isLimit (F ⋙ FintypeCat.toProfinite)

/-- The underlying `Profinite` of a `LightProfinite`. -/
def toProfinite (S : LightProfinite) : Profinite := S.cone.pt

@[simps!]
instance : Category LightProfinite := InducedCategory.category toProfinite

@[simps!]
instance concreteCategory : ConcreteCategory LightProfinite := InducedCategory.concreteCategory _

instance hasForget₂ : HasForget₂ LightProfinite TopCat :=
  InducedCategory.hasForget₂ _

instance : CoeSort LightProfinite (Type*) :=
  ⟨fun X => X.toProfinite⟩

@[simp]
lemma forget_ContinuousMap_mk {X Y : LightProfinite} (f : X → Y) (hf : Continuous f) :
    (forget Profinite).map (ContinuousMap.mk f hf) = f :=
  rfl

instance {X : LightProfinite} : TotallyDisconnectedSpace X :=
  X.toProfinite.isTotallyDisconnected

example {X : LightProfinite} : CompactSpace X :=
  inferInstance

example {X : LightProfinite} : T2Space X :=
  inferInstance

@[simp]
theorem coe_id (X : LightProfinite) : (𝟙 ((forget LightProfinite).obj X)) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget LightProfinite).map f ≫ (forget LightProfinite).map g) = g ∘ f :=
  rfl

@[simp]
theorem coe_comp_apply {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ x, (f ≫ g) x = g (f x) := by
  intros; rfl

/-- The fully faithful embedding `LightProfinite ⥤ Profinite` -/
@[simps!]
def lightToProfinite : LightProfinite ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite := show Full <| inducedFunctor _ from inferInstance

instance : lightToProfinite.ReflectsEpimorphisms := inferInstance

instance {X : LightProfinite} : TopologicalSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TopologicalSpace X.cone.pt)

instance {X : LightProfinite} : TotallyDisconnectedSpace ((forget LightProfinite).obj X) :=
  (inferInstance : TotallyDisconnectedSpace X.cone.pt)

instance {X : LightProfinite} : CompactSpace ((forget LightProfinite).obj X) :=
  (inferInstance : CompactSpace X.cone.pt )

instance {X : LightProfinite} : T2Space ((forget LightProfinite).obj X) :=
  (inferInstance : T2Space X.cone.pt )

/-- The explicit functor `FintypeCat ⥤ LightProfinite`.  -/
def fintypeCatToLightProfinite : FintypeCat ⥤ LightProfinite.{u} where
  obj X := X.toLightProfinite
  map f := FintypeCat.toProfinite.map f

/-- The fully faithful embedding of `LightProfinite` in `TopCat`. -/
@[simps!]
def toTopCat : LightProfinite ⥤ TopCat :=
  lightToProfinite ⋙ Profinite.toTopCat

end LightProfinite

noncomputable section EssentiallySmall

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

instance : Faithful LightProfinite'.toLightFunctor.{u} := ⟨id⟩

instance : Full LightProfinite'.toLightFunctor.{u} := ⟨id, fun _ ↦ rfl⟩

instance : EssSurj LightProfinite'.toLightFunctor.{u} where
  mem_essImage Y := by
    let i : limit (((Y.diagram ⋙ Skeleton.equivalence.inverse) ⋙ Skeleton.equivalence.functor) ⋙
      toProfinite) ≅ Y.cone.pt := (Limits.lim.mapIso (isoWhiskerRight ((Functor.associator _ _ _) ≪≫
      (isoWhiskerLeft Y.diagram Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      IsLimit.conePointUniqueUpToIso (limit.isLimit _) Y.isLimit
    exact ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨⟨i.hom, i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩⟩
    -- why can't I just write `i` instead of `⟨i.hom, i.inv, i.hom_inv_id, i.inv_hom_id⟩`?

instance : IsEquivalence LightProfinite'.toLightFunctor := Equivalence.ofFullyFaithfullyEssSurj _

/-- The equivalence beween `LightProfinite` and a small category. -/
def LightProfinite.equivSmall : LightProfinite.{u} ≌ LightProfinite'.{u} :=
  LightProfinite'.toLightFunctor.asEquivalence.symm

instance : EssentiallySmall LightProfinite.{u} where
  equiv_smallCategory := ⟨LightProfinite', inferInstance, ⟨LightProfinite.equivSmall⟩⟩

end EssentiallySmall
