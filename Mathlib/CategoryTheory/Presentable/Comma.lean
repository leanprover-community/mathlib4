/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.LocallyPresentable
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.ObjectProperty.Comma

/-!
# Comma categories are accessible

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

-- to be moved
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open IsFiltered in
lemma IsCardinalPresentable.mk
    {C : Type*} [Category* C] {X : C} {κ : Cardinal.{w}}
    [Fact κ.IsRegular]
    (h : ∀ (J : Type w) (_ : Category.{w} J) (_ : IsCardinalFiltered J κ)
      (F : J ⥤ C) (c : Cocone F) (_ : IsColimit c),
      (∀ (g : X ⟶ c.pt), ∃ (j : J) (f : X ⟶ F.obj j), f ≫ c.ι.app j = g) ∧
      (∀ (j : J) (f₁ f₂ : X ⟶ F.obj j) (_ : f₁ ≫ c.ι.app j = f₂ ≫ c.ι.app j),
        ∃ (j' : J) (a : j ⟶ j'), f₁ ≫ F.map a = f₂ ≫ F.map a)) :
    IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ by
      have := isFiltered_of_isCardinalFiltered J κ
      rw [Types.isColimit_iff_coconeTypesIsColimit]
      refine ⟨fun f₁ f₂ hf ↦ ?_, fun g ↦ ?_⟩
      · obtain ⟨j₁, f₁, rfl⟩ := Functor.ιColimitType_jointly_surjective _ f₁
        obtain ⟨j₂, f₂, rfl⟩ := Functor.ιColimitType_jointly_surjective _ f₂
        dsimp at f₁ f₂ hf
        obtain ⟨j', a, ha⟩ := (h J _ inferInstance F c hc).2 _ (f₁ ≫ F.map (leftToMax j₁ j₂))
          (f₂ ≫ F.map (rightToMax j₁ j₂)) (by simpa)
        simp only [Category.assoc] at ha
        exact Functor.ιColimitType_eq_of_map_eq_map _ _ _
          (leftToMax j₁ j₂ ≫ a) (rightToMax j₁ j₂ ≫ a) (by simpa)
      · obtain ⟨j, f, rfl⟩ := (h J _ inferInstance F c hc).1 g
        exact ⟨Functor.ιColimitType _ j f, rfl⟩⟩⟩

namespace Functor

variable {C D : Type*} [Category* C] [Category* D]

-- to be moved
class PreservesCardinalPresentable
    (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  le_inverseImage_isCardinalPresentable (F κ) :
    isCardinalPresentable C κ ≤ (isCardinalPresentable D κ).inverseImage F

export PreservesCardinalPresentable (le_inverseImage_isCardinalPresentable)

instance (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C)
    [IsCardinalPresentable X κ] [F.PreservesCardinalPresentable κ] :
    IsCardinalPresentable (F.obj X) κ :=
  le_inverseImage_isCardinalPresentable F κ _ (by assumption)

end Functor

namespace Comma

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] (F₁ : C₁ ⥤ D) (F₂ : C₂ ⥤ D)
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

section

variable [F₁.IsCardinalAccessible κ]
  [HasCardinalFilteredColimits C₁ κ] [HasCardinalFilteredColimits C₂ κ]

instance : HasCardinalFilteredColimits (Comma F₁ F₂) κ where
  hasColimitsOfShape J _ _ := by
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    infer_instance

instance : (Comma.fst F₁ F₂).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    infer_instance

instance : (Comma.snd F₁ F₂).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    infer_instance

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open IsFiltered in
variable {F₁ F₂ κ} in
lemma isCardinalPresentable_mk {X₁ : C₁} {X₂ : C₂}
    [HasCardinalFilteredColimits C₁ κ] [HasCardinalFilteredColimits C₂ κ]
    [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
    [IsCardinalPresentable X₁ κ] [IsCardinalPresentable X₂ κ]
    [F₁.PreservesCardinalPresentable κ] (f : F₁.obj X₁ ⟶ F₂.obj X₂) :
    IsCardinalPresentable (Comma.mk _ _ f) κ :=
  .mk (fun J _ _ G c hc ↦ by
    have := isFiltered_of_isCardinalFiltered J κ
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₁ κ J
    have := Functor.preservesColimitsOfShape_of_isCardinalAccessible F₂ κ J
    refine ⟨fun g ↦ ?_, fun j f₁ f₂ hf ↦ ?_⟩
    · obtain ⟨j, f₁, f₂, hf₁, hf₂⟩ :
          ∃ (j : J) (f₁ : X₁ ⟶ (G.obj j).left) (f₂ : X₂ ⟶ (G.obj j).right),
            f₁ ≫ (c.ι.app j).left = g.left ∧ f₂ ≫ (c.ι.app j).right = g.right := by
        obtain ⟨j₁, f₁, hf₁⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
          (isColimitOfPreserves (fst _ _) hc) g.left
        obtain ⟨j₂, f₂, hf₂⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
          (isColimitOfPreserves (snd _ _) hc) g.right
        dsimp at f₁ f₂ hf₁ hf₂
        refine ⟨max j₁ j₂, f₁ ≫ (G.map (leftToMax j₁ j₂)).left,
          f₂ ≫ (G.map (rightToMax j₁ j₂)).right, ?_, ?_⟩
        · rw [Category.assoc, ← hf₁, ← Comma.comp_left, Cocone.w]
        · rw [Category.assoc, ← hf₂, ← Comma.comp_right, Cocone.w]
      obtain ⟨j', a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
        κ (isColimitOfPreserves (snd _ _ ⋙ F₂) hc)
        (F₁.map f₁ ≫ (G.obj j).hom) (f ≫ F₂.map f₂) (by
          dsimp
          simp only [Category.assoc, ← Functor.map_comp, hf₂,
            ← (c.ι.app j).w, Functor.const_obj_obj,
            ← Functor.map_comp_assoc, hf₁, g.w])
      refine ⟨j', { left := f₁ ≫ (G.map a).left, right := f₂ ≫ (G.map a).right }, ?_⟩
      ext
      · dsimp
        rw [Category.assoc, ← hf₁, ← Comma.comp_left, Cocone.w]
      · dsimp
        rw [Category.assoc, ← hf₂, ← Comma.comp_right, Cocone.w]
    · obtain ⟨j₁, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
        κ (isColimitOfPreserves (fst _ _) hc) f₁.left f₂.left
          ((fst _ _).congr_map hf)
      obtain ⟨j₂, b, hb⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
        κ (isColimitOfPreserves (snd _ _) hc) f₁.right f₂.right
          ((snd _ _).congr_map hf)
      dsimp at ha hb
      obtain ⟨j', a', b', h⟩ := IsFiltered.span a b
      refine ⟨j', a ≫ a', ?_⟩
      ext
      · simp [reassoc_of% ha]
      · simp only [h, Functor.map_comp, comp_right, reassoc_of% hb])

protected def isCardinalPresentable : ObjectProperty (Comma F₁ F₂) :=
  ObjectProperty.comma _ _ (isCardinalPresentable C₁ κ) (isCardinalPresentable C₂ κ)

lemma isCardinalPresentable_le
    [HasCardinalFilteredColimits C₁ κ] [HasCardinalFilteredColimits C₂ κ]
    [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
    [F₁.PreservesCardinalPresentable κ] :
    Comma.isCardinalPresentable F₁ F₂ κ ≤ isCardinalPresentable (Comma F₁ F₂) κ := by
  intro f ⟨h₁, h₂⟩
  simp only [ObjectProperty.prop_inverseImage_iff, fst_obj, snd_obj] at h₁ h₂
  exact isCardinalPresentable_mk f.hom

instance [ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C₁ κ)]
    [ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C₂ κ)]
    [LocallySmall.{w} D] :
    ObjectProperty.EssentiallySmall.{w} (Comma.isCardinalPresentable F₁ F₂ κ) := by
  dsimp only [Comma.isCardinalPresentable]
  infer_instance

namespace isCardinalAccessibleCategory

variable {F₁ F₂}
  [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ]
  [F₂.PreservesCardinalPresentable κ] [LocallySmall.{w} D]

variable (f : Comma F₁ F₂)

abbrev J := CostructuredArrow (Comma.isCardinalPresentable F₁ F₂ κ).ι f
abbrev J₁ := CostructuredArrow (isCardinalPresentable C₁ κ).ι f.left
abbrev J₂ := CostructuredArrow (isCardinalPresentable C₂ κ).ι f.right

instance : IsFiltered (J₁ κ f) := isFiltered_of_isCardinalFiltered _ κ

instance : IsFiltered (J₂ κ f) := isFiltered_of_isCardinalFiltered _ κ

attribute [local instance] IsFiltered.nonempty

-- there must be some better way to define these functors
@[simps]
def π₁ : J κ f ⥤ J₁ κ f where
  obj g := CostructuredArrow.mk (Y := ⟨_, g.left.property.1⟩) (by exact g.hom.left)
  map φ := CostructuredArrow.homMk (ObjectProperty.homMk (by exact φ.left.hom.left))
    (by exact congr_arg CommaMorphism.left (CostructuredArrow.w φ))

@[simps]
def π₂ : J κ f ⥤ J₂ κ f where
  obj g := CostructuredArrow.mk (Y := ⟨_, g.left.property.2⟩) (by exact g.hom.right)
  map φ := CostructuredArrow.homMk (ObjectProperty.homMk (by exact φ.left.hom.right))
    (by exact congr_arg CommaMorphism.right (CostructuredArrow.w φ))

instance : PreservesColimitsOfShape (J₁ κ f) F₁ :=
  F₁.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

instance : PreservesColimitsOfShape (J₂ κ f) F₂ :=
  F₂.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

instance : IsCardinalFiltered (J κ f) κ := by
  sorry

instance : PreservesColimitsOfShape (J κ f) F₁ :=
  F₁.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

instance : IsFiltered (J κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

set_option backward.defeqAttrib.useBackward true in
instance : (π₁ κ f).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun d ↦ ?_, ?_⟩
  · obtain ⟨g, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
      (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
      (F₁.map d.hom ≫ f.hom)
    dsimp at a ha
    simp only [Category.id_comp] at ha
    refine ⟨CostructuredArrow.mk (Y := ⟨Comma.mk _ _ a, ?_⟩)
      { left := by exact d.hom
        right := by exact g.hom
        w := ha.symm }, ⟨?_⟩⟩
    · exact CostructuredArrow.homMk (ObjectProperty.homMk (𝟙 _)) (by simp)
    · exact ⟨d.left.property, g.left.property⟩
  · sorry

set_option backward.defeqAttrib.useBackward true in
instance : (π₂ κ f).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun d ↦ ?_, ?_⟩
  · let j₁ : J₁ κ f := Classical.arbitrary _
    obtain ⟨e : J₂ κ f, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
      (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
      (F₁.map j₁.hom ≫ f.hom)
    dsimp at a ha
    simp only [Category.id_comp] at ha
    refine ⟨CostructuredArrow.mk
      (Y := ⟨Comma.mk _ _ (a ≫ F₂.map (IsFiltered.rightToMax d e).left.hom),
        ⟨j₁.left.property, (IsFiltered.max d e).left.property⟩⟩)
        { left := by exact j₁.hom
          right := by exact (IsFiltered.max d e).hom
          w := ?_ },
        ⟨by exact IsFiltered.leftToMax d e⟩⟩
    dsimp
    rw [Category.assoc, ← ha, ← F₂.map_comp,
      ← CostructuredArrow.w (IsFiltered.rightToMax d e)]
    dsimp
  · sorry

abbrev functor : J κ f ⥤ Comma F₁ F₂ :=
  CostructuredArrow.proj (Comma.isCardinalPresentable F₁ F₂ κ).ι f ⋙
    (Comma.isCardinalPresentable F₁ F₂ κ).ι

abbrev cocone : Cocone (functor κ f) :=
  (Functor.LeftExtension.mk (𝟭 (Comma F₁ F₂))
    (Comma.isCardinalPresentable F₁ F₂ κ).ι.rightUnitor.inv).coconeAt f

noncomputable def isColimitCocone : IsColimit (cocone κ f) := by
  refine Comma.fstSndJointlyReflectColimit ?_ ?_
  · exact (Functor.Final.isColimitWhiskerEquiv (π₁ κ f) _).2
      ((isCardinalPresentable C₁ κ).ι.denseAt f.left)
  · exact (Functor.Final.isColimitWhiskerEquiv (π₂ κ f) _).2
      ((isCardinalPresentable C₂ κ).ι.denseAt f.right)

instance [F₁.IsCardinalAccessible κ] :
    (Comma.isCardinalPresentable F₁ F₂ κ).ι.IsDense where
  isDenseAt f := ⟨isColimitCocone κ f⟩

end isCardinalAccessibleCategory

protected lemma isCardinalFilteredGenerator_isCardinalPresentable
    [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
    [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
    [F₁.PreservesCardinalPresentable κ] [LocallySmall.{w} D] :
    (Comma.isCardinalPresentable F₁ F₂ κ).IsCardinalFilteredGenerator κ :=
  .mk' (isCardinalPresentable_le _ _ _)
    (fun f ↦ ⟨(CostructuredArrow (Comma.isCardinalPresentable F₁ F₂ κ).ι f), inferInstance,
      inferInstance, inferInstance,
      ⟨_, _, (Comma.isCardinalPresentable F₁ F₂ κ).ι.denseAt f⟩,
    fun g ↦ g.left.property⟩)

instance [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
    [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
    [F₁.PreservesCardinalPresentable κ] [LocallySmall.{w} D] :
    IsCardinalAccessibleCategory (Comma F₁ F₂) κ where
  exists_generator :=
    ⟨_, inferInstance, Comma.isCardinalFilteredGenerator_isCardinalPresentable.{w} F₁ F₂ κ⟩

end Comma

end CategoryTheory
