/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib
public import Mathlib.CategoryTheory.Galois.FullSubcategory
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology

/-!
# ...

-/

public section

universe w v u

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]
  {ι : Type*} [Finite ι] (U : ι → OpenSubgroup G)

lemma mem_iff {x : G} {H : OpenSubgroup G} :
    x ∈ H ↔ x ∈ H.carrier := Iff.rfl

abbrev iInfOfFinite : OpenSubgroup G :=
  ⟨⨅ i, U i, by
    convert isOpen_iInter_of_finite (fun i ↦ (U i).isOpen)
    aesop⟩

lemma iInfOfFinite_le (i : ι) :
    iInfOfFinite U ≤ U i := by
  intro x hx
  rw [mem_iff] at hx
  simp at hx
  tauto

end OpenSubgroup

namespace Action

variable {V : Type*} {FV : V → V → Type*} {CV : V → Type*}
  [∀ {X Y : V}, FunLike (FV X Y) (CV X) (CV Y)]
  [Category* V] [ConcreteCategory V FV]

section Monoid

variable {G : Type*} [Monoid G]

variable (V) in
def trivialOnSet (S : Set G) : ObjectProperty (Action V G) :=
  fun X ↦ ∀ s ∈ S, X.ρ s = 1

variable (G) in
lemma trivialOnSet_antitone {S T : Set G} (h : S ≤ T) :
    trivialOnSet V T ≤ trivialOnSet V S :=
  fun _ h' g hg ↦ h' g (h hg)

set_option backward.isDefEq.respectTransparency false in
instance (J : Type*) [Category* J] [HasLimitsOfShape J V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    intro g hg
    exact (isLimitOfPreserves (Action.forget _ _) p.isLimit).hom_ext
      (fun j ↦ by simp [dsimp% (p.π.app j).comm g, dsimp% p.prop_diag_obj j g hg])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (J : Type*) [Category* J] [HasColimitsOfShape J V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    intro g hg
    exact (isColimitOfPreserves (Action.forget _ _) p.isColimit).hom_ext (fun j ↦ by
      simp [← dsimp% (p.ι.app j).comm g, dsimp% p.prop_diag_obj j g hg])

instance (S : Set G) [HasPullbacks V] :
    (trivialOnSet V S).IsClosedUnderSubobjects where
  prop_of_mono f _ h g hg := by
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget V G).map f))
    simp [← cancel_mono f.hom, f.comm, h g hg]

instance (S : Set G) : (trivialOnSet FintypeCat.{w} S).IsGaloisSubcategory where

end Monoid

section Group

variable {G : Type*} [Group G] [HasForget₂ V TopCat] [TopologicalSpace G]
variable (V G) in
abbrev isContinuous : ObjectProperty (Action V G) := IsContinuous

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G]

lemma trivialOnSet_le_isContinuous (H : OpenSubgroup G) :
    trivialOnSet _ H ≤ isContinuous FintypeCat.{w} G := sorry

lemma isContinuous_eq_iSup :
    isContinuous FintypeCat.{w} G = ⨆ (H : OpenSubgroup G), trivialOnSet _ H := by
  have : IsTopologicalGroup G := inferInstance
  have : CompactSpace G := inferInstance
  have : T2Space G := inferInstance
  have : TotallyDisconnectedSpace G := inferInstance
  sorry

instance : (isContinuous FintypeCat.{w} G).IsClosedUnderSubobjects := by
  rw [isContinuous_eq_iSup]
  infer_instance

lemma exists_openSubgroup_of_finite
    {J : Type*} [Finite J] (obj : J → Action FintypeCat.{w} G)
    (property : ∀ j, isContinuous _ _ (obj j)) :
    ∃ (H : OpenSubgroup G), ∀ j, trivialOnSet _ H (obj j) := by
  rw [isContinuous_eq_iSup] at property
  simp only [ObjectProperty.prop_iSup_iff] at property
  choose H h using property
  exact ⟨OpenSubgroup.iInfOfFinite H,
    fun j ↦ trivialOnSet_antitone _ (OpenSubgroup.iInfOfFinite_le _ _) _ (h j)⟩

instance (J : Type*) [Category* J] [HasColimitsOfShape J FintypeCat.{w}] [Finite J] :
    (isContinuous FintypeCat.{w} G).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨H, h⟩ := exists_openSubgroup_of_finite _ p.prop_diag_obj
    exact trivialOnSet_le_isContinuous H _
      (ObjectProperty.prop_of_isColimit _ p.isColimit h)

instance (J : Type*) [Category* J] [HasLimitsOfShape J FintypeCat.{w}] [Finite J] :
    (isContinuous FintypeCat.{w} G).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨H, h⟩ := exists_openSubgroup_of_finite _ p.prop_diag_obj
    exact trivialOnSet_le_isContinuous H _
      (ObjectProperty.prop_of_isLimit _ p.isLimit h)

instance : (isContinuous FintypeCat.{w} G).IsGaloisSubcategory where

example : GaloisCategory (ContAction FintypeCat.{w} G) := inferInstance

end Group

end Action

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
abbrev PreGaloisCategory.isConnected : ObjectProperty C :=
  IsConnected

open PreGaloisCategory

namespace PreGaloisCategory

variable (F : C ⥤ FintypeCat.{w}) [GaloisCategory C] [FiberFunctor F]

end PreGaloisCategory

namespace GaloisCategory

instance : Preregular (isConnected C).FullSubcategory where
  exists_fac := sorry

abbrev grothendieckTopologyConnected :
    GrothendieckTopology (isConnected C).FullSubcategory :=
  regularTopology _

end GaloisCategory

end CategoryTheory
