/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Comma

/-!
# Comma categories are accessible

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

@[expose] public section

namespace CategoryTheory

open Limits

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
deriving ObjectProperty.IsStableUnderRetracts

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

variable (f : Comma F₁ F₂)

abbrev J := CostructuredArrow (Comma.isCardinalPresentable F₁ F₂ κ).ι f
abbrev J₁ := CostructuredArrow (isCardinalPresentable C₁ κ).ι f.left
abbrev J₂ := CostructuredArrow (isCardinalPresentable C₂ κ).ι f.right

instance [IsCardinalAccessibleCategory C₁ κ] : IsFiltered (J₁ κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

instance [IsCardinalAccessibleCategory C₂ κ] : IsFiltered (J₂ κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

attribute [local instance] IsFiltered.nonempty

abbrev J.fst (g : J κ f) : J₁ κ f :=
  CostructuredArrow.mk (Y := ⟨_, g.left.property.1⟩) (by exact g.hom.left)

abbrev J.snd (g : J κ f) : J₂ κ f :=
  CostructuredArrow.mk (Y := ⟨_, g.left.property.2⟩) (by exact g.hom.right)
-- there must be some better way to define these functors
@[simps]
def π₁ : J κ f ⥤ J₁ κ f where
  obj g := g.fst
  map φ := CostructuredArrow.homMk (ObjectProperty.homMk (by exact φ.left.hom.left))
    (by exact congr_arg CommaMorphism.left (CostructuredArrow.w φ))

@[simps]
def π₂ : J κ f ⥤ J₂ κ f where
  obj g := g.snd
  map φ := CostructuredArrow.homMk (ObjectProperty.homMk (by exact φ.left.hom.right))
    (by exact congr_arg CommaMorphism.right (CostructuredArrow.w φ))

variable {κ f}

abbrev J.mk (j₁ : J₁ κ f) (j₂ : J₂ κ f) (g : F₁.obj j₁.left.obj ⟶ F₂.obj j₂.left.obj)
    (w : F₁.map j₁.hom ≫ f.hom = g ≫ F₂.map j₂.hom := by cat_disch) :
    J κ f :=
  CostructuredArrow.mk (Y := ⟨Comma.mk _ _ g, j₁.left.property, j₂.left.property⟩)
    { left := by exact j₁.hom
      right := by exact j₂.hom }

abbrev J.homMk {j j' : J κ f} (g₁ : j.fst ⟶ j'.fst) (g₂ : j.snd ⟶ j'.snd)
    (h : F₁.map g₁.left.hom ≫ j'.left.obj.hom =
      j.left.obj.hom ≫ F₂.map g₂.left.hom := by cat_disch) :
    j ⟶ j' :=
  CostructuredArrow.homMk (ObjectProperty.homMk
    { left := g₁.left.hom
      right := g₂.left.hom }) (by
        ext
        · simpa using! CostructuredArrow.w g₁
        · simpa using! CostructuredArrow.w g₂)

section

variable [IsCardinalAccessibleCategory C₂ κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ]

set_option backward.defeqAttrib.useBackward true in
lemma J.exists_hom'
    {j j' : J κ f} (g₁ : j.fst ⟶ j'.fst) (g₂ : j.snd ⟶ j'.snd) :
    ∃ (j₂ : J₂ κ f) (a : j'.snd ⟶ j₂),
        F₁.map g₁.left.hom ≫ j'.left.obj.hom ≫ F₂.map a.left.hom =
        j.left.obj.hom ≫ F₂.map g₂.left.hom ≫ F₂.map a.left.hom := by
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    F₂ κ (J₂ κ f)
  obtain ⟨j₂, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
    (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
    (i := j'.snd) (F₁.map g₁.left.hom ≫ j'.left.obj.hom)
    (j.left.obj.hom ≫ F₂.map g₂.left.hom) (by
      dsimp
      rw [Category.id_comp, Category.assoc, Category.assoc, ← Functor.map_comp,
        ← dsimp% j'.hom.w, ← Functor.map_comp_assoc, dsimp% CostructuredArrow.w g₁,
        dsimp% j.hom.w, dsimp% CostructuredArrow.w g₂])
  exact ⟨j₂, a, by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
lemma J.exists_hom {j j' : J κ f} (g₁ : j.fst ⟶ j'.fst) (g₂ : j.snd ⟶ j'.snd) :
    ∃ (j'' : J κ f) (a : j ⟶ j'') (b : j' ⟶ j''),
      g₁.left.hom ≫ b.left.hom.left = a.left.hom.left ∧
      g₂.left.hom ≫ b.left.hom.right = a.left.hom.right := by
  obtain ⟨j₂, a, ha⟩ := J.exists_hom' g₁ g₂
  exact ⟨J.mk j'.fst j₂ (j'.left.obj.hom ≫ F₂.map a.left.hom)
    (by simp [← dsimp% (CostructuredArrow.w a)]), J.homMk g₁ (g₂ ≫ a) (by simpa),
    J.homMk (𝟙 _) a (by simp), by simp⟩

set_option backward.defeqAttrib.useBackward true in
lemma exists_of_j₁_of_j₂' (j₁ : J₁ κ f) (j₂ : J₂ κ f) :
    ∃ (j₂' : J₂ κ f) (_ : j₂ ⟶ j₂') (b : F₁.obj j₁.left.obj ⟶ F₂.obj j₂'.left.obj),
    F₁.map j₁.hom ≫ f.hom = b ≫ F₂.map j₂'.hom := by
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall F₂ κ
    (J₂ κ f)
  obtain ⟨k, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
    (F₁.map j₁.hom ≫ f.hom)
  dsimp at ha
  simp only [Category.id_comp] at ha
  obtain ⟨j₂', b, c, _⟩ := IsFilteredOrEmpty.cocone_objs j₂ k
  refine ⟨j₂', b, a ≫ F₂.map c.left.hom, ?_⟩
  simp [← ha, ← Functor.map_comp, dsimp% CostructuredArrow.w c]

set_option backward.defeqAttrib.useBackward true in
lemma exists_of_j₁_of_j₂ (j₁ : J₁ κ f) (j₂ : J₂ κ f) :
    ∃ (j : J κ f) (_ : j₁ ⟶ j.fst), Nonempty (j₂ ⟶ j.snd) := by
  obtain ⟨j₂', a, b, h⟩ := exists_of_j₁_of_j₂' j₁ j₂
  exact ⟨J.mk j₁ j₂' b h, 𝟙 _, ⟨a⟩⟩

lemma exists_of_j₁ (j₁ : J₁ κ f) :
    ∃ (j : J κ f), Nonempty (j₁ ⟶ j.fst) := by
  obtain ⟨j, a, _⟩ := exists_of_j₁_of_j₂ j₁ (Classical.arbitrary _)
  exact ⟨j, ⟨a⟩⟩

lemma exists_of_j₂ [IsCardinalAccessibleCategory C₁ κ] (j₂ : J₂ κ f) :
    ∃ (j : J κ f), Nonempty (j₂ ⟶ j.snd) := by
  obtain ⟨j, _, ⟨a⟩⟩ := exists_of_j₁_of_j₂ (Classical.arbitrary _) j₂
  exact ⟨j, ⟨a⟩⟩

end

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ] [LocallySmall.{w} D]

instance : PreservesColimitsOfShape (J₁ κ f) F₁ :=
  F₁.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

instance : PreservesColimitsOfShape (J₂ κ f) F₂ :=
  F₂.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

open IsCardinalFiltered in
set_option backward.defeqAttrib.useBackward true in
instance : IsCardinalFiltered (J κ f) κ := by
  rw [isCardinalFiltered_iff']
  refine ⟨fun ι j hι ↦ ?_, fun ι j k g hι hι' ↦ ?_⟩
  · obtain ⟨j₁, ⟨a₁⟩⟩ := IsCardinalFiltered.exists_max (fun i ↦ (j i).fst) hι
    obtain ⟨j₂, ⟨a₂⟩⟩ := IsCardinalFiltered.exists_max (fun i ↦ (j i).snd) hι
    obtain ⟨j₂', b, c, h₁⟩ := exists_of_j₁_of_j₂' j₁ j₂
    choose j₂'' d h₂ using
      fun i ↦ IsCardinalPresentable.exists_eq_of_isColimit' κ
        (isColimitOfPreserves F₂ ((isCardinalPresentable C₂ κ).ι.denseAt f.right))
          (F₁.map (a₁ i).left.hom ≫ c)
            ((j i).left.obj.hom ≫ F₂.map (a₂ i).left.hom ≫ F₂.map b.left.hom) (by
              dsimp
              rw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc,
                ← dsimp% h₁, ← F₁.map_comp_assoc, dsimp% CostructuredArrow.w (a₁ i),
                ← F₂.map_comp, dsimp% CostructuredArrow.w b, ← F₂.map_comp,
                dsimp% CostructuredArrow.w (a₂ i), dsimp% (j i).hom.w])
    dsimp at h₁ h₂
    simp only [Category.assoc] at h₂
    obtain ⟨l, e, g, fac⟩ := wideSpan d hι
    refine ⟨J.mk j₁ l (c ≫ F₂.map g.left.hom) ?_, fun i ↦ ⟨?_⟩⟩
    · dsimp
      rw [h₁, Category.assoc, ← Functor.map_comp, dsimp% CostructuredArrow.w g]
    · refine J.homMk (a₁ i) (a₂ i ≫ b ≫ g) (by simp [← fac i, reassoc_of% h₂])
  · let g₁ (i : ι) := (π₁ κ f).map (g i)
    let g₂ (i : ι) := (π₂ κ f).map (g i)
    obtain ⟨l, a, ⟨b⟩⟩ :=
      exists_of_j₁_of_j₂ (coeq g₁ hι) (coeq g₂ hι)
    obtain ⟨l', c, d, h₁, h₂⟩ := J.exists_hom (coeqHom g₁ hι ≫ a) (coeqHom g₂ hι ≫ b)
    refine ⟨l', c, J.homMk (toCoeq g₁ hι ≫ a ≫ (π₁ κ f).map d)
      (toCoeq g₂ hι ≫ b ≫ (π₂ κ f).map d) ?_, fun i ↦ ?_⟩
    · let i : ι := Classical.arbitrary _
      dsimp
      rw [← dsimp% coeq_condition g₁ hι i, ← dsimp% coeq_condition g₂ hι i]
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ h₂ ⊢
      rw [h₁, h₂]
      simp only [Functor.map_comp, Category.assoc, CommaMorphism.w]
      simp only [← Category.assoc]
      congr 1
      exact (g i).left.hom.w
    · ext
      · simp [← dsimp% [g₁] coeq_condition g₁ hι i, ← h₁, g₁]
      · simp [← dsimp% [g₂] coeq_condition g₂ hι i, ← h₂, g₂]

instance : PreservesColimitsOfShape (J κ f) F₁ :=
  F₁.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _

instance : IsFiltered (J κ f) :=
  isFiltered_of_isCardinalFiltered _ κ

set_option backward.defeqAttrib.useBackward true in
instance : (π₁ κ f).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨exists_of_j₁, fun {d e} g₁ g₂ ↦ ?_⟩
  obtain ⟨j₁, a, ha⟩ := IsFilteredOrEmpty.cocone_maps g₁ g₂
  obtain ⟨j, b, ⟨c⟩⟩ := exists_of_j₁_of_j₂ j₁ e.snd
  obtain ⟨j', g, h, h₁, h₂⟩ := J.exists_hom (a ≫ b) c
  refine ⟨j', g, ?_⟩
  ext
  simp [← h₁, reassoc_of% dsimp% (CostructuredArrow.proj _ _ ⋙
    ObjectProperty.ι _).congr_map ha]

set_option backward.defeqAttrib.useBackward true in
instance : (π₂ κ f).Final := by
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨exists_of_j₂, fun {d e} g₁ g₂ ↦ ?_⟩
  obtain ⟨j₂, a, ha⟩ := IsFilteredOrEmpty.cocone_maps g₁ g₂
  obtain ⟨j, b, ⟨c⟩⟩ := exists_of_j₁_of_j₂ e.fst j₂
  obtain ⟨j', g, h, h₁, h₂⟩ := J.exists_hom b (a ≫ c)
  refine ⟨j', g, ?_⟩
  ext
  simp [← h₂, reassoc_of% dsimp% (CostructuredArrow.proj _ _ ⋙
    ObjectProperty.ι _).congr_map ha]

variable (κ f) in
abbrev functor : J κ f ⥤ Comma F₁ F₂ :=
  CostructuredArrow.proj (Comma.isCardinalPresentable F₁ F₂ κ).ι f ⋙
    (Comma.isCardinalPresentable F₁ F₂ κ).ι

variable (κ f) in
abbrev cocone : Cocone (functor κ f) :=
  (Functor.LeftExtension.mk (𝟭 (Comma F₁ F₂))
    (Comma.isCardinalPresentable F₁ F₂ κ).ι.rightUnitor.inv).coconeAt f

variable (κ f) in
noncomputable def isColimitCocone : IsColimit (cocone κ f) := by
  refine Comma.fstSndJointlyReflectColimit ?_ ?_
  · exact (Functor.Final.isColimitWhiskerEquiv (π₁ κ f) _).2
      ((isCardinalPresentable C₁ κ).ι.denseAt f.left)
  · exact (Functor.Final.isColimitWhiskerEquiv (π₂ κ f) _).2
      ((isCardinalPresentable C₂ κ).ι.denseAt f.right)

instance : (Comma.isCardinalPresentable F₁ F₂ κ).ι.IsDense where
  isDenseAt f := ⟨isColimitCocone κ f⟩

end isCardinalAccessibleCategory

variable [IsCardinalAccessibleCategory C₁ κ] [IsCardinalAccessibleCategory C₂ κ]
  [F₁.IsCardinalAccessible κ] [F₂.IsCardinalAccessible κ]
  [F₁.PreservesCardinalPresentable κ] [LocallySmall.{w} D]

protected lemma isCardinalFilteredGenerator_isCardinalPresentable :
    (Comma.isCardinalPresentable F₁ F₂ κ).IsCardinalFilteredGenerator κ :=
  .mk' (isCardinalPresentable_le _ _ _)
    (fun f ↦ ⟨(CostructuredArrow (Comma.isCardinalPresentable F₁ F₂ κ).ι f), inferInstance,
      inferInstance, inferInstance,
      ⟨_, _, (Comma.isCardinalPresentable F₁ F₂ κ).ι.denseAt f⟩,
    fun g ↦ g.left.property⟩)

instance :
    IsCardinalAccessibleCategory (Comma F₁ F₂) κ where
  exists_generator :=
    ⟨_, inferInstance, Comma.isCardinalFilteredGenerator_isCardinalPresentable.{w} F₁ F₂ κ⟩

protected lemma isCardinalPresentable_eq :
    Comma.isCardinalPresentable F₁ F₂ κ = isCardinalPresentable (Comma F₁ F₂) κ := by
  rw [(Comma.isCardinalFilteredGenerator_isCardinalPresentable
      F₁ F₂ κ).isPresentable_eq_retractClosure,
    ObjectProperty.retractClosure_eq_self]

variable {F₁ F₂} in
protected lemma isCardinalPresentable_iff (f : Comma F₁ F₂) :
    IsCardinalPresentable f κ ↔
      IsCardinalPresentable f.left κ ∧ IsCardinalPresentable f.right κ := by
  change _ ↔ Comma.isCardinalPresentable F₁ F₂ κ f
  rw [Comma.isCardinalPresentable_eq]

instance : (Comma.fst F₁ F₂).PreservesCardinalPresentable κ where
  le_inverseImage_isCardinalPresentable f hf := by
    simp only [Comma.isCardinalPresentable_iff] at hf
    tauto

instance : (Comma.snd F₁ F₂).PreservesCardinalPresentable κ where
  le_inverseImage_isCardinalPresentable f hf := by
    simp only [Comma.isCardinalPresentable_iff] at hf
    tauto

end Comma

end CategoryTheory
