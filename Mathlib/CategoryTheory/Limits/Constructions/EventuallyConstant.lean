/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits of eventually constant functors

If `F : J ⥤ C` is a functor from a cofiltered category, and `j : J`,
we introduce a property `F.IsEventuallyConstantTo j` which says
that for any `f : i ⟶ j`, the induced morphism `F.map f` is an isomorphism.
Under this assumption, it is shown that `F` admits `F.obj j` as a limit
(`Functor.IsEventuallyConstantTo.isLimitCone`).

A typeclass `Cofiltered.IsEventuallyConstant` is also introduced, and
the dual results for filtered categories and colimits are also obtained.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {J C : Type*} [Category* J] [Category* C] (F : J ⥤ C)

namespace Functor

/-- A functor `F : J ⥤ C` is eventually constant to `j : J` if
for any map `f : i ⟶ j`, the induced morphism `F.map f` is an isomorphism.
If `J` is cofiltered, this implies `F` has a limit. -/
def IsEventuallyConstantTo (j : J) : Prop :=
  ∀ ⦃i : J⦄ (f : i ⟶ j), IsIso (F.map f)

/-- A functor `F : J ⥤ C` is eventually constant from `i : J` if
for any map `f : i ⟶ j`, the induced morphism `F.map f` is an isomorphism.
If `J` is filtered, this implies `F` has a colimit. -/
def IsEventuallyConstantFrom (i : J) : Prop :=
  ∀ ⦃j : J⦄ (f : i ⟶ j), IsIso (F.map f)

namespace IsEventuallyConstantTo

variable {F} {i₀ : J} (h : F.IsEventuallyConstantTo i₀)

include h

lemma isIso_map {i j : J} (φ : i ⟶ j) (π : j ⟶ i₀) : IsIso (F.map φ) := by
  have := h π
  have := h (φ ≫ π)
  exact IsIso.of_isIso_fac_right (F.map_comp φ π).symm

lemma precomp {j : J} (f : j ⟶ i₀) : F.IsEventuallyConstantTo j :=
  fun _ φ ↦ h.isIso_map φ f

section

variable {i j : J} (φ : i ⟶ j) (hφ : Nonempty (j ⟶ i₀))

/-- The isomorphism `F.obj i ≅ F.obj j` induced by `φ : i ⟶ j`,
when `h : F.IsEventuallyConstantTo i₀` and there exists a map `j ⟶ i₀`. -/
@[simps! hom]
noncomputable def isoMap : F.obj i ≅ F.obj j :=
  have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]
lemma isoMap_hom_inv_id : F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _ :=
  (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]
lemma isoMap_inv_hom_id : (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _ :=
  (h.isoMap φ hφ).inv_hom_id

end

variable [IsCofiltered J]
open IsCofiltered

/-- Auxiliary definition for `IsEventuallyConstantTo.cone`. -/
noncomputable def coneπApp (j : J) : F.obj i₀ ⟶ F.obj j :=
  (h.isoMap (minToLeft i₀ j) ⟨𝟙 _⟩).inv ≫ F.map (minToRight i₀ j)

lemma coneπApp_eq (j j' : J) (α : j' ⟶ i₀) (β : j' ⟶ j) :
    h.coneπApp j = (h.isoMap α ⟨𝟙 _⟩).inv ≫ F.map β := by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsCofiltered.bowtie
    (IsCofiltered.minToRight i₀ j) β (IsCofiltered.minToLeft i₀ j) α
  dsimp [coneπApp]
  rw [← cancel_epi ((h.isoMap α ⟨𝟙 _⟩).hom), isoMap_hom, isoMap_hom_inv_id_assoc,
    ← cancel_epi (h.isoMap δ ⟨α⟩).hom, isoMap_hom,
    ← F.map_comp δ β, ← h₁, F.map_comp, ← F.map_comp_assoc, ← h₂, F.map_comp_assoc,
    isoMap_hom_inv_id_assoc]

@[simp]
lemma coneπApp_eq_id : h.coneπApp i₀ = 𝟙 _ := by
  rw [h.coneπApp_eq i₀ i₀ (𝟙 _) (𝟙 _), h.isoMap_inv_hom_id]

/-- Given `h : F.IsEventuallyConstantTo i₀`, this is the (limit) cone for `F` whose
point is `F.obj i₀`. -/
@[simps]
noncomputable def cone : Cone F where
  pt := F.obj i₀
  π :=
    { app := h.coneπApp
      naturality := fun j j' φ ↦ by
        dsimp
        rw [id_comp]
        let i := IsCofiltered.min i₀ j
        let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
        let β : i ⟶ j := IsCofiltered.minToRight _ _
        rw [h.coneπApp_eq j _ α β, assoc, h.coneπApp_eq j' _ α (β ≫ φ), map_comp] }

/-- When `h : F.IsEventuallyConstantTo i₀`, the limit of `F` exists and is `F.obj i₀`. -/
noncomputable def isLimitCone : IsLimit h.cone where
  lift s := s.π.app i₀
  fac s j := by
    dsimp [coneπApp]
    rw [← s.w (IsCofiltered.minToLeft i₀ j), ← s.w (IsCofiltered.minToRight i₀ j), assoc,
      isoMap_hom_inv_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cone_π_app, coneπApp_eq_id, cone_pt, comp_id]

lemma hasLimit : HasLimit F := ⟨_, h.isLimitCone⟩

lemma isIso_π_of_isLimit {c : Cone F} (hc : IsLimit c) :
    IsIso (c.π.app i₀) := by
  simp only [← IsLimit.conePointUniqueUpToIso_hom_comp hc h.isLimitCone i₀,
    cone_π_app, coneπApp_eq_id, cone_pt, comp_id]
  infer_instance

/-- More general version of `isIso_π_of_isLimit`. -/
lemma isIso_π_of_isLimit' {c : Cone F} (hc : IsLimit c) (j : J) (π : j ⟶ i₀) :
    IsIso (c.π.app j) :=
  (h.precomp π).isIso_π_of_isLimit hc

/-- Given a cone `c` on a cofiltered diagram `F` which `IsEventuallyConstantTo i₀`, such that
`c.π.app i₀` is an isomorphism, `c` a limit cone. -/
noncomputable def isLimitOfIsIso (c : Cone F) [IsIso (c.π.app i₀)] : IsLimit c :=
  IsLimit.ofIsoLimit h.isLimitCone (by
    refine Cone.ext (asIso (c.π.app i₀)).symm (fun j ↦ ?_)
    let i := IsCofiltered.min i₀ j
    let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
    let β : i ⟶ j := IsCofiltered.minToRight _ _
    dsimp
    rw [IsIso.eq_inv_comp, ← c.w α, ← c.w β, h.coneπApp_eq j _ α β, assoc, isoMap_hom_inv_id_assoc])

end IsEventuallyConstantTo

namespace IsEventuallyConstantFrom

variable {F} {i₀ : J} (h : F.IsEventuallyConstantFrom i₀)

include h

lemma isIso_map {i j : J} (φ : i ⟶ j) (ι : i₀ ⟶ i) : IsIso (F.map φ) := by
  have := h ι
  have := h (ι ≫ φ)
  exact IsIso.of_isIso_fac_left (F.map_comp ι φ).symm

lemma postcomp {j : J} (f : i₀ ⟶ j) : F.IsEventuallyConstantFrom j :=
  fun _ φ ↦ h.isIso_map φ f

section

variable {i j : J} (φ : i ⟶ j) (hφ : Nonempty (i₀ ⟶ i))

/-- The isomorphism `F.obj i ≅ F.obj j` induced by `φ : i ⟶ j`,
when `h : F.IsEventuallyConstantFrom i₀` and there exists a map `i₀ ⟶ i`. -/
@[simps! hom]
noncomputable def isoMap : F.obj i ≅ F.obj j :=
  have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]
lemma isoMap_hom_inv_id : F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _ :=
  (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]
lemma isoMap_inv_hom_id : (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _ :=
  (h.isoMap φ hφ).inv_hom_id

end

variable [IsFiltered J]
open IsFiltered

/-- Auxiliary definition for `IsEventuallyConstantFrom.cocone`. -/
noncomputable def coconeιApp (j : J) : F.obj j ⟶ F.obj i₀ :=
  F.map (rightToMax i₀ j) ≫ (h.isoMap (leftToMax i₀ j) ⟨𝟙 _⟩).inv

lemma coconeιApp_eq (j j' : J) (α : j ⟶ j') (β : i₀ ⟶ j') :
    h.coconeιApp j = F.map α ≫ (h.isoMap β ⟨𝟙 _⟩).inv := by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsFiltered.bowtie
    (IsFiltered.leftToMax i₀ j) β (IsFiltered.rightToMax i₀ j) α
  dsimp [coconeιApp]
  rw [← cancel_mono ((h.isoMap β ⟨𝟙 _⟩).hom), assoc, assoc, isoMap_hom, isoMap_inv_hom_id,
    comp_id, ← cancel_mono (h.isoMap δ ⟨β⟩).hom, isoMap_hom, assoc, assoc, ← F.map_comp α δ,
    ← h₂, F.map_comp, ← F.map_comp β δ, ← h₁, F.map_comp, isoMap_inv_hom_id_assoc]

@[simp]
lemma coconeιApp_eq_id : h.coconeιApp i₀ = 𝟙 _ := by
  rw [h.coconeιApp_eq i₀ i₀ (𝟙 _) (𝟙 _), h.isoMap_hom_inv_id]

/-- Given `h : F.IsEventuallyConstantFrom i₀`, this is the (limit) cocone for `F` whose
point is `F.obj i₀`. -/
@[simps]
noncomputable def cocone : Cocone F where
  pt := F.obj i₀
  ι :=
    { app := h.coconeιApp
      naturality := fun j j' φ ↦ by
        dsimp
        rw [comp_id]
        let i := IsFiltered.max i₀ j'
        let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
        let β : j' ⟶ i := IsFiltered.rightToMax _ _
        rw [h.coconeιApp_eq j' _ β α, h.coconeιApp_eq j _ (φ ≫ β) α, map_comp, assoc] }

set_option backward.isDefEq.respectTransparency false in
/-- When `h : F.IsEventuallyConstantFrom i₀`, the colimit of `F` exists and is `F.obj i₀`. -/
noncomputable def isColimitCocone : IsColimit h.cocone where
  desc s := s.ι.app i₀
  fac s j := by
    dsimp [coconeιApp]
    rw [← s.w (IsFiltered.rightToMax i₀ j), ← s.w (IsFiltered.leftToMax i₀ j), assoc,
      isoMap_inv_hom_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cocone_ι_app, coconeιApp_eq_id, id_comp]

lemma hasColimit : HasColimit F := ⟨_, h.isColimitCocone⟩

set_option backward.isDefEq.respectTransparency false in
lemma isIso_ι_of_isColimit {c : Cocone F} (hc : IsColimit c) :
    IsIso (c.ι.app i₀) := by
  simp only [← IsColimit.comp_coconePointUniqueUpToIso_inv hc h.isColimitCocone i₀,
    cocone_ι_app, coconeιApp_eq_id, id_comp]
  infer_instance

/-- More general version of `isIso_ι_of_isColimit`. -/
lemma isIso_ι_of_isColimit' {c : Cocone F} (hc : IsColimit c) (j : J) (ι : i₀ ⟶ j) :
    IsIso (c.ι.app j) :=
  (h.postcomp ι).isIso_ι_of_isColimit hc

set_option backward.isDefEq.respectTransparency false in
/-- Given a cocone `c` on a filtered diagram `F` which `IsEventuallyConstantFrom i₀`, such that
`c.π.app i₀` is an isomorphism, `c` a colimit cocone. -/
noncomputable def isColimitOfIsIso (c : Cocone F) [IsIso (c.ι.app i₀)] : IsColimit c :=
  IsColimit.ofIsoColimit h.isColimitCocone (by
    refine Cocone.ext (asIso (c.ι.app i₀)) (fun j ↦ ?_)
    let i := IsFiltered.max i₀ j
    let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
    let β : j ⟶ i := IsFiltered.rightToMax _ _
    dsimp
    rw [← c.w α, ← c.w β, h.coconeιApp_eq j _ β α, assoc, isoMap_inv_hom_id_assoc])

end IsEventuallyConstantFrom

end Functor

namespace IsCofiltered

/-- A functor `F : J ⥤ C` from a cofiltered category is eventually constant if there
exists `j : J`, such that for any `f : i ⟶ j`, the induced map `F.map f` is an isomorphism. -/
class IsEventuallyConstant : Prop where
  exists_isEventuallyConstantTo : ∃ (j : J), F.IsEventuallyConstantTo j

instance [hF : IsEventuallyConstant F] [IsCofiltered J] : HasLimit F := by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantTo
  exact h.hasLimit

end IsCofiltered

namespace IsFiltered

/-- A functor `F : J ⥤ C` from a filtered category is eventually constant if there
exists `i : J`, such that for any `f : i ⟶ j`, the induced map `F.map f` is an isomorphism. -/
class IsEventuallyConstant : Prop where
  exists_isEventuallyConstantFrom : ∃ (i : J), F.IsEventuallyConstantFrom i

instance [hF : IsEventuallyConstant F] [IsFiltered J] : HasColimit F := by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantFrom
  exact h.hasColimit

end IsFiltered

end CategoryTheory
