/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.Basic

/-!
# Compact subsets of products as limits in `Profinite`

This file exhibits a compact subset `C` of a product `(i : ι) → X i` of totally disconnected
Hausdorff spaces as a limit in `Profinite` indexed by `Finset ι`.

## Main definitions

- `FinsetsToProfinite` is the functor `(Finset ι)ᵒᵖ ⥤ Profinite` indexing the limit. It maps `J` to
  `C.proj J`, the restriction of `C` to `J`
- `FinsetsCone` is a cone on `FinsetsToProfinite` with cone point `C`

## Main results

- `Profinite.isIso_finsetsCone_lift` says that the natural map from the cone point of the explicit
  limit cone in `Profinite` on `FinsetsToProfinite` to the cone point of `FinsetsCone` is an
  isomorphism
- `Profinite.asLimitFinsetsConeIso` is the induced isomorphism of cones.
- `Profinite.finsetsCone_isLimit` says that `FinsetsCone` is a limit cone.

-/

universe u

def precomp {ι ι' : Type*} {π : ι → Type*} [(i : ι) → TopologicalSpace (π i)]
  (φ : ι' → ι) : C((i : ι) → π i, (i : ι') → π (φ i)) := ⟨_, Pi.continuous_precomp' φ⟩

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
  (C : Set ((i : ι) → X i))

variable (J K L : ι → Prop)

def Proj' : ((i : ι) → X i) → ((i : {i // J i}) → X i.val) := precomp (Subtype.val (p := J))

/-- The image of `Proj π J` -/
def Set.proj' : Set ((i : {i : ι // J i}) → X i) := Proj' J '' C

/-- The restriction of `Proj π J` to a subset, mapping to its image. -/
@[simps!]
def ProjRestrict' : C → C.proj' J :=
  Set.MapsTo.restrict (Proj' J) _ _ (Set.mapsTo_image _ _)

@[simp]
theorem continuous_projRestrict' : Continuous (ProjRestrict' C J) :=
  Continuous.restrict _ (Pi.continuous_precomp' _)

theorem surjective_projRestrict' :
    Function.Surjective (ProjRestrict' C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨⟨y, hy.1⟩, ?_⟩
  exact Subtype.ext hy.2

variable {J K L}

def Projs' (h : ∀ i, J i → K i) : ((i : {i // K i}) → X i) → ((i : {i // J i}) → X i.val) :=
  precomp (Set.inclusion h)

def ProjRestricts' (h : ∀ i, J i → K i) : C.proj' K → C.proj' J :=
  Set.MapsTo.restrict (Projs' h) _ _ (fun _ hx ↦ by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    refine ⟨y, hy.1, rfl⟩)

@[simp]
theorem continuous_projRestricts' (h : ∀ i, J i → K i) : Continuous (ProjRestricts' C h) :=
  Continuous.restrict _ (Pi.continuous_precomp' _)

theorem projRestricts_comp_projRestrict' (h : ∀ i, J i → K i) :
    ProjRestricts' C h ∘ ProjRestrict' C K = ProjRestrict' C J := rfl

section Profinite

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
  {J K L : Finset ι} [∀ (J : Finset ι) i, Decidable (i ∈ J)]
  {C} (hC : IsCompact C)

open CategoryTheory Limits Opposite

/-- The functor from the poset of finsets of `ι` to  `Profinite`, indexing the limit. -/
noncomputable
def FinsetsToProfinite' :
    (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (C.proj' (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := ⟨(ProjRestricts' C (leOfHom h.unop)), continuous_projRestricts' _ _⟩

/-- The limit cone on `FinsetsToProfinite` -/
noncomputable
def FinsetsCone' : Cone (FinsetsToProfinite' hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J ↦ ⟨ProjRestrict' C (· ∈ (J.unop)), continuous_projRestrict' _ _⟩ }

theorem eq_of_forall_proj_eq' (a b : C) (h : ∀ (J : Finset ι), ProjRestrict' C (· ∈ J) a =
    ProjRestrict' C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [ProjRestrict', Proj', precomp, ContinuousMap.coe_mk,
    Set.MapsTo.val_restrict_apply] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

open Profinite in
instance isIso_finsetsCone_lift' [DecidableEq ι] :
    IsIso ((limitConeIsLimit (FinsetsToProfinite' hC)).lift (FinsetsCone' hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_proj_eq' a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone (FinsetsToProfinite' hC)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset ι), ProjRestrict' C (· ∈ J) x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          intro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((ProjRestrict' C (· ∈ J)) ⁻¹' {s})
        · intro J s
          refine IsClosed.preimage (continuous_projRestrict' C (· ∈ J)) ?_
          exact T1Space.t1 s
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            ProjRestrict' C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            ProjRestrict' C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)}
        · intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← projRestricts_comp_projRestrict' C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), ProjRestrict' C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
            (fun J : Finset ι => ProjRestrict' C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_sup H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_projRestrict' _ _))
            (fun J => (hc J (a.val (op J))).isCompact) fun J => hc J (a.val (op J))
        exact ⟨x, Set.mem_iInter.1 hx⟩)

/-- The canonical map from `C` to the explicit limit as an isomorphism. -/
noncomputable
def isoFinsetsConeLift' [DecidableEq ι] :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone (FinsetsToProfinite' hC)).pt :=
  asIso <| (Profinite.limitConeIsLimit _).lift (FinsetsCone' hC)

/-- The isomorphism of cones induced by `isoFinsetsConeLift`. -/
noncomputable
def asLimitFinsetsConeIso' [DecidableEq ι] : FinsetsCone' hC ≅ Profinite.limitCone _ :=
  Limits.Cones.ext (isoFinsetsConeLift' hC) fun _ => rfl

/-- `FinsetsCone` is a limit cone. -/
noncomputable
def finsetsCone_isLimit' [DecidableEq ι] : CategoryTheory.Limits.IsLimit (FinsetsCone' hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitFinsetsConeIso' hC).symm

end Profinite
