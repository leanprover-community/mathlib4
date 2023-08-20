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

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, Inhabited (X i)]
  (C : Set ((i : ι) → X i))

section General

variable {J K L : ι → Prop} [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

/-- A variant of `ProjRestrict` with domain of the form `C.proj K` -/
@[simps!]
def ProjRestricts (h : ∀ i, J i → K i) : C.proj K → C.proj J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (C.proj K) J

lemma projRestricts_eq_self (x : C.proj K) (i : ι) (hJK : ∀ i, J i → K i) (h : J i) :
    (ProjRestricts C hJK x).val i = x.val i := by
  simp only [Set.proj, Proj, ProjRestricts_coe, ite_eq_left_iff]
  exact fun hJ ↦ (by exfalso; exact hJ h)

lemma projRestricts_ne_default_iff (x : C.proj K) (i : ι) (hJK : ∀ i, J i → K i) :
    (ProjRestricts C hJK x).val i ≠ default ↔ J i ∧ x.val i ≠ default := by
  simp only [Set.proj, Proj, ProjRestricts_coe, ne_eq, ite_eq_right_iff, not_forall, exists_prop]

lemma projRestricts_eq_default_iff (x : C.proj K) (i : ι) (hJK : ∀ i, J i → K i) :
    (ProjRestricts C hJK x).val i = default ↔ ¬ J i ∨ x.val i = default := by
  rw [← not_iff_not]
  simp only [projRestricts_ne_default_iff, ne_eq]
  rw [not_or, not_not]

@[simp]
lemma continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

lemma surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  Function.Surjective.comp (Homeomorph.surjective _) (surjective_projRestrict _ _)

variable (J) in
lemma projRestricts_eq_id  :
    ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext x i
  simp only [Set.proj, Proj, ProjRestricts_coe, id_eq, ite_eq_left_iff]
  obtain ⟨y, hy⟩ := x.prop
  rw [← hy.2]
  intro hijn
  apply Eq.symm
  simp only [Proj, Bool.default_bool, ite_eq_right_iff]
  intro hij
  exfalso
  exact hijn hij

lemma projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  simp only [Set.proj, Proj, Function.comp_apply, ProjRestricts_coe]
  split_ifs with h hh
  · rfl
  · exfalso; exact hh (hJK i h)
  · rfl

lemma projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  simp only [Set.proj, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  split_ifs with hh hh'
  · rfl
  · exfalso; exact hh' (h i hh)
  · rfl


end General

section Finsets

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
  {J K L : Finset ι} [∀ (J : Finset ι) i, Decidable (i ∈ J)]
  {C} (hC : IsCompact C)

open CategoryTheory Limits Opposite

lemma mem_projRestrict (h : J ⊆ K) (x : C.proj (· ∈ K)) :
    Proj X (· ∈ J) x.val ∈ C.proj (· ∈ J) := by
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨y, ⟨hy.1, ?_⟩⟩
  dsimp [Proj]
  ext i
  split_ifs with hh
  · rw [← hy.2, eq_comm]
    simp only [Proj, ite_eq_left_iff]
    exact fun hK ↦ by simp only [h hh, not_true] at hK
  · rfl

/-- The functor from the poset of finsets of `ι` to  `Profinite`, indexing the limit. -/
noncomputable
def FinsetsToProfinite :
    (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (C.proj (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by dsimp; simp_rw [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by dsimp; congr; dsimp; rw [projRestricts_eq_comp]

/-- The limit cone on `FinsetsToProfinite` -/
noncomputable
def FinsetsCone : Cone (FinsetsToProfinite hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := {
    app := fun J ↦ ⟨ProjRestrict C (· ∈ (J.unop)), continuous_projRestrict _ _⟩
    naturality := by
      intro _ _ h
      simp only [Functor.const_obj_obj, FinsetsToProfinite, ProjRestricts, Homeomorph.setCongr,
        Homeomorph.homeomorph_mk_coe, ProjRestrict, Functor.const_obj_map, Category.id_comp]
      congr
      ext x i
      dsimp [Proj]
      split_ifs with h₁ h₂
      · rfl
      · simp only [(leOfHom h.unop h₁), not_true] at h₂
      · rfl
  }

lemma eq_of_forall_proj_eq (a b : C) (h : ∀ (J : Finset ι), ProjRestrict C (· ∈ J) a =
    ProjRestrict C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  rw [Subtype.ext_iff] at h
  have hh := congr_fun h i
  simp only [ProjRestrict_coe, Proj, Finset.mem_singleton, ite_true] at hh
  exact hh

namespace Profinite

/-- The canonical map from `C` to the explicit limit is an isomorphism. -/
instance isIso_finsetsCone_lift [DecidableEq ι] :
    IsIso ((limitConeIsLimit (FinsetsToProfinite hC)).lift (FinsetsCone hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_proj_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone (FinsetsToProfinite hC)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset ι), ProjRestrict C (· ∈ J) x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          rintro J
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
def isoFinsetsConeLift [DecidableEq ι] :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone (FinsetsToProfinite hC)).pt :=
  asIso <| (Profinite.limitConeIsLimit _).lift (FinsetsCone hC)

/-- The isomorphism of cones induced by `isoFinsetsConeLift`. -/
noncomputable
def asLimitFinsetsConeIso [DecidableEq ι] : FinsetsCone hC ≅ Profinite.limitCone _ :=
  Limits.Cones.ext (isoFinsetsConeLift hC) fun _ => rfl

/-- `FinsetsCone` is a limit cone. -/
noncomputable
def finsetsCone_isLimit [DecidableEq ι] : CategoryTheory.Limits.IsLimit (FinsetsCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitFinsetsConeIso hC).symm

end Profinite

end Finsets
