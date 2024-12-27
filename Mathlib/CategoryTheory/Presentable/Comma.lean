/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Comma.LocallySmall

/-!
# Comma categories are accessible

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

namespace Comma

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] (F₁ : C₁ ⥤ D) (F₂ : C₂ ⥤ D)

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

variable {F₁ F₂} in
instance isCardinalPresentable_mk {X₁ : C₁} {X₂ : C₂}
    [IsCardinalPresentable X₁ κ] [IsCardinalPresentable X₂ κ]
    [IsCardinalPresentable X₁ κ] [IsCardinalPresentable X₂ κ]
    (f : F₁.obj X₁ ⟶ F₂.obj X₂) :
    IsCardinalPresentable (Comma.mk _ _ f) κ := by
  -- need that `F₁` (and `F₂` ?) preserve κ-presentable objects
  sorry

section

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [IsCardinalAccessibleCategory D κ]
  [F₁.IsCardinalAccessible κ]

instance hasCardinalFilteredColimits :
    HasCardinalFilteredColimits.{w} (Comma F₁ F₂) κ where
  hasColimitsOfShape J _ _ := by
    have := F₁.preservesColimitsOfShape_of_isCardinalAccessible κ
    infer_instance

instance : (Comma.fst F₁ F₂).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := F₁.preservesColimitsOfShape_of_isCardinalAccessible κ
    infer_instance

instance : (Comma.snd F₁ F₂).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := F₁.preservesColimitsOfShape_of_isCardinalAccessible κ
    infer_instance

end

namespace hasCardinalFilteredGenerators

variable {F₁ F₂ κ} {X₁ : C₁} {X₂ : C₂} (f : F₁.obj X₁ ⟶ F₂.obj X₂)
  (p₁ : CardinalFilteredPresentation.{w} X₁ κ)
  (p₂ : CardinalFilteredPresentation.{w} X₂ κ)

structure Index where
  j₁ : p₁.J
  j₂ : p₂.J
  hom : F₁.obj (p₁.F.obj j₁) ⟶ F₂.obj (p₂.F.obj j₂)
  w : hom ≫ F₂.map (p₂.ι.app j₂) = F₁.map (p₁.ι.app j₁) ≫ f

namespace Index

attribute [reassoc (attr := simp)] w

variable {f p₁ p₂}

@[ext]
structure Hom (S₁ S₂ : Index f p₁ p₂) where
  m₁ : S₁.j₁ ⟶ S₂.j₁
  m₂ : S₁.j₂ ⟶ S₂.j₂
  w : S₁.hom ≫ F₂.map (p₂.F.map m₂) = F₁.map (p₁.F.map m₁) ≫ S₂.hom := by aesop_cat

attribute [reassoc] Hom.w
attribute [local simp] Hom.w_assoc Hom.w

instance : Category (Index f p₁ p₂) where
  Hom := Hom
  id S := { m₁ := 𝟙 _, m₂ := 𝟙 _}
  comp φ φ' := { m₁ := φ.m₁ ≫ φ'.m₁, m₂ := φ.m₂ ≫ φ'.m₂ }

@[simp] lemma id_m₁ (S : Index f p₁ p₂) : Hom.m₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_m₂ (S : Index f p₁ p₂) : Hom.m₂ (𝟙 S) = 𝟙 _ := rfl

section

variable {S₁ S₂ S₃ : Index f p₁ p₂} (φ : S₁ ⟶ S₂) (φ' : S₂ ⟶ S₃)

@[reassoc (attr := simp)] lemma comp_m₁ : (φ ≫ φ').m₁ = φ.m₁ ≫ φ'.m₁ := rfl
@[reassoc (attr := simp)] lemma comp_m₂ : (φ ≫ φ').m₂ = φ.m₂ ≫ φ'.m₂ := rfl

end

variable (f p₁ p₂)

@[simps]
def π₁ : Index f p₁ p₂ ⥤ p₁.J where
  obj S := S.j₁
  map φ := φ.m₁

@[simps]
def π₂ : Index f p₁ p₂ ⥤ p₂.J where
  obj S := S.j₂
  map φ := φ.m₂

end Index

@[simps]
def functor : Index f p₁ p₂ ⥤ Comma F₁ F₂ where
  obj S := Comma.mk _ _ S.hom
  map {S₁ S₂} φ :=
    { left := p₁.F.map φ.m₁
      right := p₂.F.map φ.m₂
      w := φ.w.symm }

@[simps]
def cocone : Cocone (functor f p₁ p₂) where
  pt := Comma.mk _ _ f
  ι :=
    { app S :=
        { left := p₁.ι.app S.j₁
          right := p₂.ι.app S.j₂
          w := S.w.symm } }

instance [LocallySmall.{w} D] : Small.{w} (Index f p₁ p₂) := by
  let T := Σ (j₁ : p₁.J) (j₂ : p₂.J), Shrink.{w} (F₁.obj (p₁.F.obj j₁) ⟶ F₂.obj (p₂.F.obj j₂))
  let φ : Index f p₁ p₂ → T := fun S ↦ ⟨S.j₁, S.j₂, equivShrink _ S.hom⟩
  have hφ : Function.Injective φ := by
    rintro ⟨j₁, j₂, hom, _⟩ ⟨j₁', j₂', hom', _⟩ h
    dsimp [φ] at h
    obtain rfl : j₁ = j₁' := congr_arg Sigma.fst h
    rw [Sigma.ext_iff, heq_eq_eq] at h
    replace h := h.2
    obtain rfl : j₂ = j₂' := congr_arg Sigma.fst h
    simpa using h
  exact small_of_injective hφ

instance [LocallySmall.{w} D] : EssentiallySmall.{w} (Index f p₁ p₂) := by
  apply essentiallySmall_of_small_of_locallySmall

instance : IsCardinalFiltered (Index f p₁ p₂) κ := sorry

instance : IsFiltered (Index f p₁ p₂) := by
  apply isFiltered_of_isCardinalDirected _ κ

instance : (Index.π₁ f p₁ p₂).Final := sorry

instance : (Index.π₂ f p₁ p₂).Final := sorry

section

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [IsCardinalAccessibleCategory D κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]

def isColimitCocone : IsColimit (cocone f p₁ p₂) := by
  sorry

noncomputable def cardinalFilteredPresentation :
    CardinalFilteredPresentation (Comma.mk _ _ f) κ :=
  .ofIsColimitOfEssentiallySmall _ (isColimitCocone f p₁ p₂) κ

end

lemma cardinalFilteredPresentation_exists_f_obj_iso
    [IsCardinalAccessibleCategory D κ]
    (x : (cardinalFilteredPresentation f p₁ p₂).J) :
    ∃ (j : Index f p₁ p₂),
      Nonempty ((cardinalFilteredPresentation f p₁ p₂).F.obj x ≅ (functor f p₁ p₂).obj j) :=
  CardinalFilteredPresentation.ofIsColimitOfEssentiallySmall_exists_f_obj_iso _ _ _ _

end hasCardinalFilteredGenerators

section

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [IsCardinalAccessibleCategory D κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]

open hasCardinalFilteredGenerators in
instance hasCardinalFilteredGenerators :
    HasCardinalFilteredGenerators.{w} (Comma F₁ F₂) κ where
  exists_generators' := by
    obtain ⟨ι₁, G₁, h₁⟩ := HasCardinalFilteredGenerators.exists_generators C₁ κ
    obtain ⟨ι₂, G₂, h₂⟩ := HasCardinalFilteredGenerators.exists_generators C₂ κ
    have := h₁.isCardinalPresentable
    have := h₂.isCardinalPresentable
    refine ⟨Σ (i₁ : ι₁) (i₂ : ι₂), Shrink.{w} (F₁.obj (G₁ i₁) ⟶ F₂.obj (G₂ i₂)),
      fun ⟨i₁, i₂, hom⟩ ↦ Comma.mk _ _ ((equivShrink _).symm hom), ?_⟩
    constructor
    · rintro ⟨i₁, i₂, hom⟩
      infer_instance
    · rintro ⟨X₁, X₂, hom⟩
      refine ⟨cardinalFilteredPresentation hom (h₁.presentation X₁) (h₂.presentation X₂),
        ?_⟩
      intro j
      let Z := (cardinalFilteredPresentation hom (h₁.presentation X₁)
        (h₂.presentation X₂)).F.obj j
      obtain ⟨S, ⟨e : Z ≅ _⟩⟩ := cardinalFilteredPresentation_exists_f_obj_iso _ _ _ j
      obtain ⟨i₁, ⟨e₁⟩⟩ := h₁.exists_presentation_obj_iso X₁ S.j₁
      obtain ⟨i₂, ⟨e₂⟩⟩ := h₂.exists_presentation_obj_iso X₂ S.j₂
      let α : F₁.obj (G₁ i₁) ⟶ F₂.obj (G₂ i₂) :=
        F₁.map (e₁.inv ≫ e.inv.left) ≫ Z.hom ≫ F₂.map (e.hom.right ≫ e₂.hom)
      refine ⟨⟨i₁, i₂, equivShrink _
        (F₁.map (e₁.inv ≫ e.inv.left) ≫ Z.hom ≫ F₂.map (e.hom.right ≫ e₂.hom))⟩,
        ⟨isoMk ((Comma.fst _ _).mapIso e ≪≫ e₁) ((Comma.snd _ _).mapIso e ≪≫ e₂) ?_⟩⟩
      dsimp
      simp only [Functor.map_comp, Category.assoc, CommaMorphism.w_assoc, functor_obj_left,
        functor_obj_right, functor_obj_hom, Equiv.symm_apply_apply, Iso.map_hom_inv_id_assoc]
      have := e.hom.w
      dsimp at this
      rw [reassoc_of% this, ← F₂.map_comp_assoc e.inv.right, ← comp_right,
        e.inv_hom_id]
      dsimp
      rw [F₂.map_id, id_comp]

instance isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Comma F₁ F₂) κ where

end

section

variable [IsCardinalLocallyPresentable C₁ κ] [IsCardinalLocallyPresentable C₂ κ]
  [IsCardinalLocallyPresentable D κ] [PreservesColimitsOfSize.{w, w} F₁]

instance isCardinalLocallyPresentable :
    IsCardinalLocallyPresentable (Comma F₁ F₂) κ where

end

end Comma

end CategoryTheory
