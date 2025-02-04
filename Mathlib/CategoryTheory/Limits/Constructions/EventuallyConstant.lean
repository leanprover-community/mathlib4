/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

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

namespace CategoryTheory

open Category Limits

section

variable {J C : Type*} [Category J] [Category C] (F : J ⥤ C)

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

@[reassoc (attr := simp)]
lemma coneπApp_naturality {j j' : J} (φ : j ⟶ j') :
    h.coneπApp j ≫ F.map φ = h.coneπApp j' := by
  let i := IsCofiltered.min i₀ j
  let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
  let β : i ⟶ j := IsCofiltered.minToRight _ _
  rw [h.coneπApp_eq j _ α β, assoc, h.coneπApp_eq j' _ α (β ≫ φ), map_comp]

/-- Given `h : F.IsEventuallyConstantTo i₀`, this is the (limit) cone for `F` whose
point is `F.obj i₀`. -/
@[simps]
noncomputable def cone : Cone F where
  pt := F.obj i₀
  π := { app := h.coneπApp }

/-- When `h : F.IsEventuallyConstantTo i₀`, the limit of `F` exists and is `F.obj i₀`. -/
def isLimitCone : IsLimit h.cone where
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
    h.coconeιApp j = F.map α ≫ (h.isoMap β ⟨𝟙 _⟩).inv  := by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsFiltered.bowtie
    (IsFiltered.leftToMax i₀ j) β (IsFiltered.rightToMax i₀ j) α
  dsimp [coconeιApp]
  rw [← cancel_mono ((h.isoMap β ⟨𝟙 _⟩).hom), assoc, assoc, isoMap_hom, isoMap_inv_hom_id,
    comp_id, ← cancel_mono (h.isoMap δ ⟨β⟩).hom, isoMap_hom, assoc, assoc, ← F.map_comp α δ,
    ← h₂, F.map_comp, ← F.map_comp β δ, ← h₁, F.map_comp, isoMap_inv_hom_id_assoc]

@[simp]
lemma coconeιApp_eq_id : h.coconeιApp i₀ = 𝟙 _ := by
  rw [h.coconeιApp_eq i₀ i₀ (𝟙 _) (𝟙 _), h.isoMap_hom_inv_id]

@[reassoc (attr := simp)]
lemma coconeιApp_naturality {j j' : J} (φ : j ⟶ j') :
    F.map φ ≫ h.coconeιApp j' = h.coconeιApp j := by
  let i := IsFiltered.max i₀ j'
  let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
  let β : j' ⟶ i := IsFiltered.rightToMax _ _
  rw [h.coconeιApp_eq j' _ β α, h.coconeιApp_eq j _ (φ ≫ β) α, map_comp, assoc]

/-- Given `h : F.IsEventuallyConstantFrom i₀`, this is the (limit) cocone for `F` whose
point is `F.obj i₀`. -/
@[simps]
noncomputable def cocone : Cocone F where
  pt := F.obj i₀
  ι := { app := h.coconeιApp }

/-- When `h : F.IsEventuallyConstantFrom i₀`, the colimit of `F` exists and is `F.obj i₀`. -/
def isColimitCocone : IsColimit h.cocone where
  desc s := s.ι.app i₀
  fac s j := by
    dsimp [coconeιApp]
    rw [← s.w (IsFiltered.rightToMax i₀ j), ← s.w (IsFiltered.leftToMax i₀ j), assoc,
      isoMap_inv_hom_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cocone_ι_app, coconeιApp_eq_id, id_comp]

lemma hasColimit : HasColimit F := ⟨_, h.isColimitCocone⟩

lemma isIso_ι_of_isColimit {c : Cocone F} (hc : IsColimit c) :
    IsIso (c.ι.app i₀) := by
  simp only [← IsColimit.comp_coconePointUniqueUpToIso_inv hc h.isColimitCocone i₀,
    cocone_ι_app, coconeιApp_eq_id, id_comp]
  infer_instance

/-- More general version of `isIso_ι_of_isColimit`. -/
lemma isIso_ι_of_isColimit' {c : Cocone F} (hc : IsColimit c) (j : J) (ι : i₀ ⟶ j) :
    IsIso (c.ι.app j) :=
  (h.postcomp ι).isIso_ι_of_isColimit hc

end IsEventuallyConstantFrom

end Functor

namespace IsCofiltered

/-- A functor `F : J ⥤ C` from a cofiltered category is eventually constant if there
exists `j : J`, such that for any `f : i ⟶ j`, the induced map `F.map f` is an isomorphism. -/
class IsEventuallyConstant : Prop where
  exists_isEventuallyConstantTo : ∃ (j : J), F.IsEventuallyConstantTo j

lemma exists_of_isEventuallyConstant [hF : IsEventuallyConstant F] :
    ∃ (i : J), F.IsEventuallyConstantTo i :=
  hF.exists_isEventuallyConstantTo

instance [hF : IsEventuallyConstant F] [IsCofiltered J] : HasLimit F := by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantTo
  exact h.hasLimit

instance (X : C) [IsCofiltered J] : IsEventuallyConstant ((Functor.const J).obj X) where
  exists_isEventuallyConstantTo :=
    ⟨Classical.choice IsCofiltered.nonempty, fun _ _ ↦ by dsimp; infer_instance⟩

end IsCofiltered

namespace IsFiltered

/-- A functor `F : J ⥤ C` from a filtered category is eventually constant if there
exists `i : J`, such that for any `f : i ⟶ j`, the induced map `F.map f` is an isomorphism. -/
class IsEventuallyConstant : Prop where
  exists_isEventuallyConstantFrom : ∃ (i : J), F.IsEventuallyConstantFrom i

lemma exists_of_isEventuallyConstant [hF : IsEventuallyConstant F] :
    ∃ (i : J), F.IsEventuallyConstantFrom i :=
  hF.exists_isEventuallyConstantFrom

instance [hF : IsEventuallyConstant F] [IsFiltered J] : HasColimit F := by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantFrom
  exact h.hasColimit

instance (X : C) [IsFiltered J] : IsEventuallyConstant ((Functor.const J).obj X) where
  exists_isEventuallyConstantFrom :=
    ⟨Classical.choice IsFiltered.nonempty, fun _ _ ↦ by dsimp; infer_instance⟩

end IsFiltered

namespace Limits

variable (J) (X : C)

/-- The obvious cocone of a constant functor.  -/
@[simps]
def constCocone : Cocone ((Functor.const J).obj X) where
  pt := X
  ι := 𝟙 _

/-- If `J` is a filtered category, the colimit of the constant functor `J ⥤ C`
with value `X : C` is `X`. -/
noncomputable def constCoconeIsColimit [IsFiltered J] :
    IsColimit (constCocone J X) := Nonempty.some (by
  obtain ⟨j, h⟩ := IsFiltered.exists_of_isEventuallyConstant ((Functor.const J).obj X)
  refine ⟨IsColimit.ofIsoColimit h.isColimitCocone (Cocones.ext (Iso.refl _) (fun i ↦ ?_))⟩
  have h₁ := h.coconeιApp_naturality (IsFiltered.leftToMax i j)
  have h₂ := h.coconeιApp_naturality (IsFiltered.rightToMax i j)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, id_comp] at h₁ h₂
  simp [← h₁, h₂])

/-- The obvious cone of a constant functor.  -/
@[simps]
def constCone : Cone ((Functor.const J).obj X) where
  pt := X
  π := 𝟙 _

/-- If `J` is a cofiltered category, the limit of the constant functor `J ⥤ C`
with value `X : C` is `X`. -/
noncomputable def constConeIsColimit [IsCofiltered J] :
    IsLimit (constCone J X) := Nonempty.some (by
  obtain ⟨j, h⟩ := IsCofiltered.exists_of_isEventuallyConstant ((Functor.const J).obj X)
  refine ⟨IsLimit.ofIsoLimit h.isLimitCone (Cones.ext (Iso.refl _) (fun i ↦ ?_))⟩
  have h₁ := h.coneπApp_naturality (IsCofiltered.minToLeft i j)
  have h₂ := h.coneπApp_naturality (IsCofiltered.minToRight i j)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, comp_id] at h₁ h₂
  simp [← h₁, h₂])

end Limits

end

end CategoryTheory
