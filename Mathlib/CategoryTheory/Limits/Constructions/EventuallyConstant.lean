import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Filtered.Basic

namespace CategoryTheory

open Category Limits

variable {J C : Type*} [Category J] [Category C]

namespace IsCofiltered

theorem bowtie [IsCofilteredOrEmpty J] {j₁ j₂ k₁ k₂ : J} (f₁ : k₁ ⟶ j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂) :
    ∃ (s : J) (α : s ⟶ k₁) (β : s ⟶ k₂), α ≫ f₁ = β ≫ g₁ ∧ α ≫ f₂ = β ≫ g₂ := by
  obtain ⟨t, k₁t, k₂t, ht⟩ := cospan f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsCofilteredOrEmpty.cone_maps (k₁t ≫ f₂) (k₂t ≫ g₂)
  refine' ⟨s, ts ≫ k₁t, ts ≫ k₂t, by simp only [assoc, ht], by simp only [assoc, hs]⟩

end IsCofiltered

namespace Functor

variable (F : J ⥤ C)

def IsEventuallyConstantTo (j : J) : Prop :=
  ∀ ⦃i : J⦄ (f : i ⟶ j), IsIso (F.map f)

class IsEventuallyConstant : Prop where
  isEventuallyConstantTo : ∃ (j : J), F.IsEventuallyConstantTo j

lemma IsEventuallyConstant.mk' (i : J) (hF : F.IsEventuallyConstantTo i) :
    F.IsEventuallyConstant := ⟨⟨i, hF⟩⟩

namespace IsEventuallyConstantTo

variable {F} {i₀ : J} (h : F.IsEventuallyConstantTo i₀)

lemma isIso_map {i j : J} (φ : i ⟶ j) (π : j ⟶ i₀) : IsIso (F.map φ) := by
  have hπ := h π
  have hφπ := h (φ ≫ π)
  rw [F.map_comp] at hφπ
  exact IsIso.of_isIso_comp_right _ (F.map π)

lemma comp {j : J} (f : j ⟶ i₀) : F.IsEventuallyConstantTo j :=
  fun _ φ => h.isIso_map φ f

section

variable {i j : J} (φ : i ⟶ j) (hφ : Nonempty (j ⟶ i₀))

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

noncomputable def coneπApp (j : J) : F.obj i₀ ⟶ F.obj j :=
    (h.isoMap (IsCofiltered.minToLeft i₀ j) ⟨𝟙 _⟩).inv ≫
      F.map (IsCofiltered.minToRight i₀ j)

lemma coneπApp_eq (j j' : J) (α : j' ⟶ i₀) (β : j' ⟶ j) :
    h.coneπApp j = (h.isoMap α ⟨𝟙 _⟩).inv ≫ F.map β := by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsCofiltered.bowtie (IsCofiltered.minToRight i₀ j) β (IsCofiltered.minToLeft i₀ j) α
  dsimp [coneπApp]
  rw [← cancel_epi ((h.isoMap α ⟨𝟙 _⟩).hom), isoMap_hom, isoMap_hom_inv_id_assoc,
    ← cancel_epi (h.isoMap δ ⟨α⟩).hom, isoMap_hom]
  conv_rhs => rw [← F.map_comp, ← h₁, F.map_comp]
  rw [← F.map_comp_assoc, ← h₂, F.map_comp, assoc, isoMap_hom_inv_id_assoc]

@[simp]
lemma coneπApp_i₀ : h.coneπApp i₀ = 𝟙 _ := by
  rw [h.coneπApp_eq i₀ i₀ (𝟙 _) (𝟙 _), map_id, comp_id,
    ← cancel_mono ((h.isoMap (𝟙 i₀) ⟨𝟙 _⟩).hom),
    Iso.inv_hom_id, id_comp, isoMap_hom, F.map_id]

@[simps]
noncomputable def cone : Cone F where
  pt := F.obj i₀
  π :=
    { app := h.coneπApp
      naturality := by
        intro j j' φ
        dsimp
        rw [id_comp]
        let i := IsCofiltered.min i₀ j
        have α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
        have β : i ⟶ j := IsCofiltered.minToRight _ _
        rw [h.coneπApp_eq j _ α β, assoc, h.coneπApp_eq j' _ α (β ≫ φ), F.map_comp] }

def isLimitCone : IsLimit (h.cone) where
  lift s := s.π.app i₀
  fac s j := by
    dsimp [coneπApp]
    have eq₁ := s.π.naturality (IsCofiltered.minToLeft i₀ j)
    have eq₂ := s.π.naturality (IsCofiltered.minToRight i₀ j)
    dsimp at eq₁ eq₂
    rw [id_comp] at eq₁ eq₂
    rw [eq₁, eq₂, assoc, isoMap_hom_inv_id_assoc]
  uniq s m hm := by
    dsimp at m hm ⊢
    rw [← hm i₀, coneπApp_i₀, comp_id]

lemma hasLimit : HasLimit F := ⟨_, h.isLimitCone⟩

lemma isIso_π_ofIsLimit {c : Cone F} (hc : IsLimit c) :
    IsIso (c.π.app i₀) := by
  simp only [← IsLimit.conePointUniqueUpToIso_hom_comp hc h.isLimitCone i₀,
    cone_pt, cone_π_app, coneπApp_i₀, comp_id]
  infer_instance

lemma isIso_π_ofIsLimit' {c : Cone F} (hc : IsLimit c) (j : J) (π : j ⟶ i₀) :
    IsIso (c.π.app j) :=
  (h.comp π).isIso_π_ofIsLimit hc

end IsEventuallyConstantTo

instance [hF : F.IsEventuallyConstant] [IsCofiltered J] : HasLimit F := by
  obtain ⟨j, h⟩ := hF.isEventuallyConstantTo
  exact h.hasLimit

end Functor

end CategoryTheory
