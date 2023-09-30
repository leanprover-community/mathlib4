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
  the restriction of `C` to `J`
- `FinsetsCone` is a cone on `FinsetsToProfinite` with cone point `C`

## Main results

- `Profinite.isIso_finsetsCone_lift` says that the natural map from the cone point of the explicit
  limit cone in `Profinite` on `FinsetsToProfinite` to the cone point of `FinsetsCone` is an
  isomorphism
- `Profinite.asLimitFinsetsConeIso` is the induced isomorphism of cones.
- `Profinite.finsetsCone_isLimit` says that `FinsetsCone` is a limit cone.

-/

universe u

section

/-- "Precomposition" as a continuous map between dependent types. -/
def precomp {ι ι' : Type*} {π : ι → Type*} [(i : ι) → TopologicalSpace (π i)]
    (φ : ι' → ι) : C((i : ι) → π i, (i : ι') → π (φ i)) := ⟨_, Pi.continuous_precomp' φ⟩

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] (C : Set ((i : ι) → X i))
    (J K : ι → Prop)

namespace FinsetFunctor

/-- The object part of the functor `FinsetsToProfinite : (Finset ι)ᵒᵖ ⥤ Profinite`. -/
def obj : Set ((i : {i : ι // J i}) → X i) := precomp (Subtype.val (p := J)) '' C

/-- The projection maps in the limit cone `FinsetsCone`. -/
def π_app : C(C, FinsetFunctor.obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Subtype.val (p := J))) _ _ (Set.mapsTo_image _ _),
    Continuous.restrict _ (Pi.continuous_precomp' _)⟩

variable {J K}

/-- The morphism part of the functor `FinsetsToProfinite : (Finset ι)ᵒᵖ ⥤ Profinite`. -/
def map (h : ∀ i, J i → K i) : C(obj C K, obj C J) :=
  ⟨Set.MapsTo.restrict (precomp (Set.inclusion h)) _ _ (fun _ hx ↦ by
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    refine ⟨y, hy.1, rfl⟩), Continuous.restrict _ (Pi.continuous_precomp' _)⟩

theorem surjective_π_app :
    Function.Surjective (π_app C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨⟨y, hy.1⟩, ?_⟩
  exact Subtype.ext hy.2

theorem map_comp_π_app (h : ∀ i, J i → K i) : map C h ∘ π_app C K = π_app C J := rfl

end FinsetFunctor

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)] {C} (hC : IsCompact C)

open CategoryTheory Limits Opposite FinsetFunctor

/-- The functor from the poset of finsets of `ι` to  `Profinite`, indexing the limit. -/
noncomputable
def FinsetsToProfinite : (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (obj C (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (Pi.continuous_precomp' _)) _ _
  map h := map C (leOfHom h.unop)

/-- The limit cone on `FinsetsToProfinite` -/
noncomputable
def FinsetsCone : Cone (FinsetsToProfinite hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := { app := fun J ↦ π_app C (· ∈ unop J) }

theorem eq_of_forall_π_app_eq (a b : C)
    (h : ∀ (J : Finset ι), π_app C (· ∈ J) a = π_app C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  simp only [π_app, precomp, ContinuousMap.coe_mk,
    Set.MapsTo.val_restrict_apply] at h
  exact congr_fun h ⟨i, Finset.mem_singleton.mpr rfl⟩

open Profinite in
instance isIso_finsetsCone_lift [DecidableEq ι] :
    IsIso ((limitConeIsLimit (FinsetsToProfinite hC)).lift (FinsetsCone hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_π_app_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone (FinsetsToProfinite hC)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset ι), π_app C (· ∈ J) x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          intro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((π_app C (· ∈ J)) ⁻¹' {s})
        · intro J s
          refine IsClosed.preimage (π_app C (· ∈ J)).continuous ?_
          exact T1Space.t1 s
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            π_app C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            π_app C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)}
        · intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← map_comp_π_app C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), π_app C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
            (fun J : Finset ι => π_app C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_sup H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_π_app _))
            (fun J => (hc J (a.val (op J))).isCompact) fun J => hc J (a.val (op J))
        exact ⟨x, Set.mem_iInter.1 hx⟩)

/-- The canonical map from `C` to the explicit limit as an isomorphism. -/
noncomputable
def isoFinsetsConeLift [DecidableEq ι] :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone (FinsetsToProfinite hC)).pt :=
  asIso <| (Profinite.limitConeIsLimit _).lift (FinsetsCone hC)

/-- The isomorphism of cones induced by `isoFinsetsConeLift`. -/
noncomputable
def asLimitFinsetsConeIso [DecidableEq ι] : FinsetsCone hC ≅ Profinite.limitCone _ :=
  Limits.Cones.ext (isoFinsetsConeLift hC) fun _ => rfl

/-- `FinsetsCone` is a limit cone. -/
noncomputable
def finsetsCone_isLimit [DecidableEq ι] : CategoryTheory.Limits.IsLimit (FinsetsCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitFinsetsConeIso hC).symm

end

section Projections

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, Inhabited (X i)]
  (C : Set ((i : ι) → X i))

section General

variable (J K L : ι → Prop) [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

/-- The projection mapping everything that satisfies `J i` to itself, and everything else to
    `default` -/
def Proj : ((i : ι) → X i) → ((i : ι) → X i) :=
  fun c i ↦ if J i then c i else default

@[simp]
theorem continuous_proj :
    Continuous (Proj J : ((i : ι) → X i) → ((i : ι) → X i)) := by
  refine continuous_pi ?_
  intro i
  dsimp [Proj]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- The image of `Proj π J` -/
def Set.proj : Set ((i : ι) → X i) := (Proj J) '' C

/-- The restriction of `Proj π J` to a subset, mapping to its image. -/
@[simps!]
def ProjRestrict : C → C.proj J :=
  Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]
theorem continuous_projRestrict : Continuous (ProjRestrict C J) :=
  Continuous.restrict _ (continuous_proj _)

theorem surjective_projRestrict :
    Function.Surjective (ProjRestrict C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨⟨y, hy.1⟩, ?_⟩
  exact Subtype.ext hy.2

theorem proj_eq_self {x : (i : ι) → X i} (h : ∀ i, x i ≠ default → J i) : Proj J x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff]
  rw [← not_imp_not, not_not, eq_comm, ← ne_eq]
  exact h i

theorem proj_prop_eq_self (hh : ∀ i x, x ∈ C → x i ≠ default → J i) : C.proj J = C := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h
    suffices x = y by rw [this]; exact hy.1
    rw [← hy.2, proj_eq_self]
    exact fun i ↦ hh i y hy.1
  · refine ⟨x, ⟨h, ?_⟩⟩
    rw [proj_eq_self]
    exact fun i ↦ hh i x h

theorem proj_comp_of_subset (h : ∀ i, J i → K i) : (Proj J ∘ Proj K) =
    (Proj J : ((i : ι) → X i) → ((i : ι) → X i)) := by
  ext x i
  dsimp [Proj]
  split_ifs with hh hh'
  · rfl
  · exfalso; exact hh' (h i hh)
  · rfl

theorem proj_eq_of_subset (h : ∀ i, J i → K i) : (C.proj K).proj J = C.proj J := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := hy.1
    rw [← hy.2, ← hz.2]
    suffices Proj J z = (Proj J ∘ Proj K) z by exact ⟨z, ⟨hz.1, this⟩⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy⟩ := h
    dsimp [Set.proj]
    rw [← Set.image_comp]
    refine ⟨y, ⟨hy.1, ?_⟩⟩
    rw [← hy.2, proj_comp_of_subset J K h]

variable {J K L}

/-- A variant of `ProjRestrict` with domain of the form `C.proj K` -/
@[simps!]
def ProjRestricts (h : ∀ i, J i → K i) : C.proj K → C.proj J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (C.proj K) J

@[simp]
theorem continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

theorem surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  Function.Surjective.comp (Homeomorph.surjective _) (surjective_projRestrict _ _)

variable (J) in
theorem projRestricts_eq_id  :
    ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext x i
  simp only [Set.proj, Proj, ProjRestricts_coe, id_eq, ite_eq_left_iff]
  obtain ⟨y, hy⟩ := x.prop
  intro h
  rw [← hy.2, Proj, if_neg h]

theorem projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  simp only [Set.proj, Proj, Function.comp_apply, ProjRestricts_coe]
  split_ifs with h hh
  · rfl
  · exfalso; exact hh (hJK i h)
  · rfl

theorem projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  simp only [Set.proj, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  split_ifs with hh hh'
  · rfl
  · exfalso; exact hh' (h i hh)
  · rfl

variable (J)

def iso_map : C(C.proj J, (FinsetFunctor.obj C J)) :=
  ⟨fun x ↦ ⟨fun i ↦ x.val i.val, by
    obtain ⟨y, hy⟩ := x.prop
    refine ⟨y, hy.1, ?_⟩
    rw [precomp, ContinuousMap.coe_mk, ← hy.2]
    ext i
    exact (if_pos i.prop).symm⟩,
  Continuous.subtype_mk (continuous_pi fun i ↦ Continuous.comp (continuous_apply _)
    continuous_subtype_val) _⟩

lemma iso_map_bijective : Function.Bijective (iso_map C J) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    dsimp [iso_map] at h
    ext i
    rw [Subtype.ext_iff] at h
    dsimp at h
    by_cases hi : J i
    · exact congr_fun h ⟨i, hi⟩
    · obtain ⟨c, hc⟩ := a.prop
      obtain ⟨d, hd⟩ := b.prop
      rw [← hc.2, ← hd.2, Proj, Proj, if_neg hi, if_neg hi]
  · intro a
    refine ⟨⟨fun i ↦ if hi : J i then a.val ⟨i, hi⟩ else default, ?_⟩, ?_⟩
    · obtain ⟨y, hy⟩ := a.prop
      refine ⟨y, hy.1, ?_⟩
      rw [← hy.2]
      rfl
    · ext i
      exact dif_pos i.prop

variable (K)

lemma naturality (h : ∀ i, J i → K i) :
    iso_map C J ∘ ProjRestricts C h = FinsetFunctor.map C h ∘ iso_map C K := by
  ext x i
  simp only [iso_map, ContinuousMap.coe_mk, Function.comp_apply, ProjRestricts_coe,
    Proj._eq_1, precomp._eq_1, Set.coe_inclusion]
  rw [if_pos i.prop]
  rfl

end General

section Profinite

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
  [∀ (J : Finset ι) i, Decidable (i ∈ J)] {C} (hC : IsCompact C)

open CategoryTheory Limits Opposite

/-- The functor from the poset of finsets of `ι` to  `Profinite`, indexing the limit. -/
noncomputable
def FinsetsToProfinite' :
    (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (C.proj (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by dsimp; simp_rw [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by dsimp; congr; dsimp; rw [projRestricts_eq_comp]

noncomputable
def FinsetsToProfiniteIso : FinsetsToProfinite' hC ≅ FinsetsToProfinite hC := NatIso.ofComponents
  (fun J ↦ (Profinite.isoOfBijective (iso_map C (· ∈ unop J)) (iso_map_bijective C (· ∈ unop J))))
  (by
    intro ⟨J⟩ ⟨K⟩ ⟨⟨⟨f⟩⟩⟩
    ext x
    exact congr_fun (naturality C (· ∈ K) (· ∈ J) f) x)

/-- The limit cone on `FinsetsToProfinite` -/
noncomputable
def FinsetsCone' : Cone (FinsetsToProfinite' hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := {
    app := fun J ↦ ⟨ProjRestrict C (· ∈ unop J), continuous_projRestrict _ _⟩
    naturality := by
      intro _ _ h
      simp only [Functor.const_obj_obj, FinsetsToProfinite', ProjRestricts, Homeomorph.setCongr,
        Homeomorph.homeomorph_mk_coe, ProjRestrict, Functor.const_obj_map, Category.id_comp]
      congr
      ext x i
      dsimp [Proj]
      split_ifs with h₁ h₂
      · rfl
      · simp only [(leOfHom h.unop h₁), not_true] at h₂
      · rfl
  }

theorem eq_of_forall_proj_eq (a b : C) (h : ∀ (J : Finset ι), ProjRestrict C (· ∈ J) a =
    ProjRestrict C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  have hh := congr_fun h i
  simp only [ProjRestrict_coe, Proj, Finset.mem_singleton, ite_true] at hh
  exact hh

open Profinite in
instance isIso_finsetsCone_lift' [DecidableEq ι] :
    IsIso ((limitConeIsLimit (FinsetsToProfinite' hC)).lift (FinsetsCone' hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_proj_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone (FinsetsToProfinite' hC)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset ι), ProjRestrict C (· ∈ J) x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          intro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((ProjRestrict C (· ∈ J)) ⁻¹' {s})
        · intro J s
          refine IsClosed.preimage (continuous_projRestrict C (· ∈ J)) ?_
          exact T1Space.t1 s
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            ProjRestrict C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            ProjRestrict C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)}
        · intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← projRestricts_comp_projRestrict C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), ProjRestrict C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
            (fun J : Finset ι => ProjRestrict C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_sup H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_projRestrict _ _))
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
end Projections
