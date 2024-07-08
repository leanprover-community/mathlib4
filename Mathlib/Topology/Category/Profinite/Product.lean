/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.Basic

/-!
# Compact subsets of products as limits in `Profinite`

This file exhibits a compact subset `C` of a product `(i : ι) → X i` of totally disconnected
Hausdorff spaces as a cofiltered limit in `Profinite` indexed by `Finset ι`.

## Main definitions

- `Profinite.indexFunctor` is the functor `(Finset ι)ᵒᵖ ⥤ Profinite` indexing the limit. It maps
  `J` to the restriction of `C` to `J`
- `Profinite.indexCone` is a cone on `Profinite.indexFunctor` with cone point `C`

## Main results

- `Profinite.isIso_indexCone_lift` says that the natural map from the cone point of the explicit
  limit cone in `Profinite` on `indexFunctor` to the cone point of `indexCone` is an
  isomorphism
- `Profinite.asLimitindexConeIso` is the induced isomorphism of cones.
- `Profinite.indexCone_isLimit` says that `indexCone` is a limit cone.

-/

universe u

namespace Profinite

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] (C : Set ((i : ι) → X i))
    (J K : ι → Prop)

namespace IndexFunctor

open ContinuousMap

/-- The object part of the functor `indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite`. -/
def obj : Set ((i : {i : ι // J i}) → X i) := ContinuousMap.precomp (Subtype.val (p := J)) '' C

/-- The projection maps in the limit cone `indexCone`. -/
def π_app : C(C, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

variable {J K}

/-- The morphism part of the functor `indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite`. -/
def map (h : ∀ i, J i → K i) : C(obj C K, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx ↦ by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    exact ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩

theorem surjective_π_app :
    Function.Surjective (π_app C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  exact ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩

theorem map_comp_π_app (h : ∀ i, J i → K i) : map C h ∘ π_app C K = π_app C J := rfl

variable {C}

theorem eq_of_forall_π_app_eq (a b : C)
    (h : ∀ (J : Finset ι), π_app C (· ∈ J) a = π_app C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, ContinuousMap.precomp, ContinuousMap.coe_mk,
    Set.MapsTo.val_restrict_apply] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

end IndexFunctor

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
variable {C}
variable (hC : IsCompact C)

open CategoryTheory Limits Opposite IndexFunctor

/-- The functor from the poset of finsets of `ι` to  `Profinite`, indexing the limit. -/
noncomputable
def indexFunctor : (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (obj C (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := map C (leOfHom h.unop)

/-- The limit cone on `indexFunctor` -/
noncomputable
def indexCone : Cone (indexFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J ↦ π_app C (· ∈ unop J) }

instance isIso_indexCone_lift :
    IsIso ((limitConeIsLimit.{u, u} (indexFunctor hC)).lift (indexCone hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_π_app_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone.{u, u} (indexFunctor hC)).pt => f.val (op J) at h
        exact h
      · rsuffices ⟨b, hb⟩ : ∃ (x : C), ∀ (J : Finset ι), π_app C (· ∈ J) x = a.val (op J)
        · use b
          apply Subtype.ext
          apply funext
          intro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((π_app C (· ∈ J)) ⁻¹' {s}) := by
          intro J s
          refine IsClosed.preimage (π_app C (· ∈ J)).continuous ?_
          exact T1Space.t1 s
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            π_app C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            π_app C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)} := by
          intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← map_comp_π_app C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), π_app C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
            (fun J : Finset ι => π_app C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_isDirected_le H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_π_app _))
            (fun J => (hc J (a.val (op J))).isCompact) fun J => hc J (a.val (op J))
        exact ⟨x, Set.mem_iInter.1 hx⟩)

/-- The canonical map from `C` to the explicit limit as an isomorphism. -/
noncomputable
def isoindexConeLift :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone.{u, u} (indexFunctor hC)).pt :=
  asIso <| (Profinite.limitConeIsLimit.{u, u} _).lift (indexCone hC)

/-- The isomorphism of cones induced by `isoindexConeLift`. -/
noncomputable
def asLimitindexConeIso : indexCone hC ≅ Profinite.limitCone.{u, u} _ :=
  Limits.Cones.ext (isoindexConeLift hC) fun _ => rfl

/-- `indexCone` is a limit cone. -/
noncomputable
def indexCone_isLimit : CategoryTheory.Limits.IsLimit (indexCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitindexConeIso hC).symm

end Profinite
