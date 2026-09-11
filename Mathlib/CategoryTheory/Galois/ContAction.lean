/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.FullSubcategory
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Category.FinTopCat

/-!
# The Galois category of finite sets with a continuous action of a topological group

Let `G` be a topological group. In this file, we show
that the category `ContAction FintypeCat G` is a Galois category.
In order to do this, we show that the corresponding property
`isContinuous FintypeCat G` of objects in `Action FintypeCat G`
consists of the union over all open subgroups `H` of `G` of the properties
`trivialOnSet FintypeCat H` (which are satisfied by the representations
that are trivial on `H`).

-/

@[expose] public section

universe w

open CategoryTheory Limits FintypeCatDiscrete

namespace Action

variable {V : Type*} {FV : V → V → Type*} {CV : V → Type*}
  [∀ {X Y : V}, FunLike (FV X Y) (CV X) (CV Y)]
  [Category* V] [ConcreteCategory V FV]

section Monoid

variable {G : Type*} [Monoid G]

variable (V) in
/-- The property of objects in `Action V G` for which the action of the
elements of a subset `S : Set G` is trivial. -/
def trivialOnSet (S : Set G) : ObjectProperty (Action V G) :=
  fun X ↦ ∀ s ∈ S, X.ρ s = 1

variable (G) in
lemma trivialOnSet_antitone : Antitone (trivialOnSet V (G := G)) :=
  fun _ _ h _ h' g hg ↦ h' g (h hg)

instance (J : Type*) [Category* J] [HasLimitsOfShape J V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    intro g hg
    exact (isLimitOfPreserves (Action.forget _ _) p.isLimit).hom_ext
      (fun j ↦ by simp [dsimp% (p.π.app j).comm g, dsimp% p.prop_diag_obj j g hg])

instance (J : Type*) [Category* J] [HasColimitsOfShape J V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    intro g hg
    exact (isColimitOfPreserves (Action.forget _ _) p.isColimit).hom_ext (fun j ↦ by
      simp [← dsimp% (p.ι.app j).comm g, dsimp% p.prop_diag_obj j g hg])

instance [HasFiniteLimits V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderFiniteLimits where

instance [HasFiniteColimits V] (S : Set G) :
    (trivialOnSet V S).IsClosedUnderFiniteColimits where

instance (S : Set G) [HasPullbacks V] :
    (trivialOnSet V S).IsClosedUnderSubobjects where
  prop_of_mono f _ h g hg := by
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget V G).map f))
    simp [← cancel_mono f.hom, f.comm, h g hg]

instance (S : Set G) : (trivialOnSet FintypeCat.{w} S).IsGaloisSubcategory where

end Monoid

section Group

variable {G : Type*} [Group G] [HasForget₂ V TopCat] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- If an action of a topological group on a finite set is trivial on an open subgroup,
then it is continuous. -/
lemma trivialOnSet_le_isContinuous (H : OpenSubgroup G) :
    trivialOnSet FintypeCat.{w} H ≤ isContinuous FintypeCat.{w} G := by
  intro R h
  constructor
  let s : G ⧸ H.toSubgroup → G := Function.surjInv Quotient.mk_surjective
  have hs (g : G) : ∃ (x : H), s g = g * x :=
    ⟨⟨g⁻¹ * s g, QuotientGroup.eq.mp (Function.rightInverse_surjInv _ _).symm⟩, by simp⟩
  let φ (x : (G ⧸ H.toSubgroup) × R.V) : R.V := s x.1 • x.2
  have : (fun (x : G × ((forget₂ _ TopCat).obj R)) ↦ x.1 • x.2) = fun x ↦ φ ⟨x.1, x.2⟩ := by
    ext ⟨g, v⟩
    obtain ⟨x, eq⟩ := hs g
    simp [φ, eq, ← R.ρ_apply_eq_smul, h _ x.prop]
  rw [this]
  fun_prop

/-- An action of a topological group on a finite set is continuous if and only if it is trivial
when restricted to some open subgroup. -/
lemma isContinuous_eq_iSup :
    isContinuous FintypeCat.{w} G = ⨆ (H : OpenSubgroup G), trivialOnSet _ H := by
  refine le_antisymm (fun R (h : _) ↦ ?_) (by simpa using trivialOnSet_le_isContinuous)
  change ContinuousSMul G R.V.obj at h
  simp only [ObjectProperty.prop_iSup_iff]
  exact ⟨OpenSubgroup.iInfOfFinite (fun (v : R.V) ↦ ⟨_, stabilizer_isOpen G v⟩),
    fun g hg ↦ ConcreteCategory.hom_ext _ _ fun v ↦ OpenSubgroup.iInfOfFinite_le _ v hg⟩

instance : (isContinuous FintypeCat.{w} G).IsClosedUnderSubobjects := by
  rw [isContinuous_eq_iSup]
  infer_instance

/-- An action of a topological group on a finite set is continuous if and only if it is trivial
when restricted to some open subgroup. -/
lemma exists_openSubgroup_of_isContinuous_of_finite
    {J : Type*} [Finite J] (obj : J → Action FintypeCat.{w} G)
    (property : ∀ j, isContinuous _ _ (obj j)) :
    ∃ (H : OpenSubgroup G), ∀ j, trivialOnSet _ H (obj j) := by
  rw [isContinuous_eq_iSup] at property
  simp only [ObjectProperty.prop_iSup_iff] at property
  choose H h using property
  exact ⟨OpenSubgroup.iInfOfFinite H,
    fun j ↦ trivialOnSet_antitone _ (OpenSubgroup.iInfOfFinite_le _ _) _ (h j)⟩

instance : (isContinuous FintypeCat.{w} G).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ := ⟨by
    rintro X ⟨p⟩
    obtain ⟨H, h⟩ := exists_openSubgroup_of_isContinuous_of_finite _ p.prop_diag_obj
    exact trivialOnSet_le_isContinuous H _
      (ObjectProperty.prop_of_isLimit _ p.isLimit h)⟩

instance : (isContinuous FintypeCat.{w} G).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ := ⟨by
    rintro X ⟨p⟩
    obtain ⟨H, h⟩ := exists_openSubgroup_of_isContinuous_of_finite _ p.prop_diag_obj
    exact trivialOnSet_le_isContinuous H _
      (ObjectProperty.prop_of_isColimit _ p.isColimit h)⟩

instance : (isContinuous FintypeCat.{w} G).IsGaloisSubcategory where

example : GaloisCategory (ContAction FintypeCat.{w} G) := inferInstance

end Group

end Action
