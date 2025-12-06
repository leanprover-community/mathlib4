/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Presheaves of types which preserves a limit

Let `F : J ⥤ Cᵒᵖ` be a functor. We show that a presheaf `P : Cᵒᵖ ⥤ Type w`
preserves the limit of `F` iff `P` is a local object with respect to a suitable
family of morphisms in `Cᵒᵖ ⥤ Type w` (this family contains `1` or `0` morphism
depending on whether the limit of `F` exists or not).

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace Presheaf

section

variable {C : Type u} [Category.{v} C]
  {J : Type u'} [Category.{v'} J] [LocallySmall.{w} C]
  {F : J ⥤ Cᵒᵖ} (c : Cone F) {c' : Cocone (F.leftOp ⋙ shrinkYoneda.{w})}
  (hc : IsLimit c) (hc' : IsColimit c') (P : Cᵒᵖ ⥤ Type w)

variable {P} in
@[simps -isSimp symm_apply apply_coe]
noncomputable def coconeCompShrinkYonedaHomEquiv :
    (c'.pt ⟶ P) ≃ (F ⋙ P).sections where
  toFun f :=
    { val j := shrinkYonedaEquiv (c'.ι.app (op j) ≫ f)
      property {X X'} g := by
        have h₁ := c'.w g.op
        dsimp at h₁ ⊢
        rw [← h₁, Category.assoc]
        conv_rhs => rw [shrinkYonedaEquiv_comp]
        erw [map_shrinkYonedaEquiv]
        rw [shrinkYonedaEquiv_shrinkYoneda_map]
        rfl }
  invFun s := hc'.desc (Cocone.mk _
    { app j := shrinkYonedaEquiv.symm (s.val j.unop)
      naturality j₁ j₂ f := by
        rw [← s.property f.unop]
        dsimp
        rw [shrinkYonedaEquiv_symm_map, Category.comp_id] })
  left_inv f := hc'.hom_ext (by simp)
  right_inv u := by ext; simp

noncomputable def coconePtToShrinkYoneda :
    c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop :=
  hc'.desc (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

variable {P} in
@[reassoc]
lemma coconePtToShrinkYoneda_comp (x : P.obj c.pt) :
    coconePtToShrinkYoneda c hc' ≫ shrinkYonedaEquiv.symm x =
      (coconeCompShrinkYonedaHomEquiv hc').symm
        (Types.sectionOfCone (P.mapCone c) x) := by
  refine hc'.hom_ext (fun j ↦ ?_)
  dsimp [coconePtToShrinkYoneda, coconeCompShrinkYonedaHomEquiv_symm_apply]
  rw [hc'.fac_assoc, hc'.fac]
  dsimp
  rw [shrinkYonedaEquiv_symm_map]

lemma nonempty_isLimit_mapCone_iff :
    Nonempty (IsLimit (P.mapCone c)) ↔
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal P := by
  -- this should be a separate lemma
  have h : (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal P ↔
      (Function.Bijective (fun (f : _ ⟶ P) ↦ coconePtToShrinkYoneda c hc' ≫ f)) :=
    ⟨fun h ↦ h _ ⟨⟨⟩⟩, fun h ↦ by rintro _ _ _ ⟨_⟩; exact h⟩
  rw [Types.isLimit_iff_bijective_sectionOfCone, h, ← Function.Bijective.of_comp_iff'
    (coconeCompShrinkYonedaHomEquiv hc').symm.bijective,
    ← Function.Bijective.of_comp_iff _ shrinkYonedaEquiv.bijective]
  convert Iff.rfl using 2
  ext : 1
  simp [← coconePtToShrinkYoneda_comp]

variable {c}

include hc in
lemma preservesLimit_eq_isLocal_single :
    ObjectProperty.preservesLimit F =
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal := by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c hc' P]
  exact ⟨fun _ ↦ ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ ↦ preservesLimit_of_preserves_limit_cone hc h⟩

variable (F)

variable [Small.{w} J]
noncomputable def preservesLimitHomFamilySrc :=
  colimit (F.leftOp ⋙ shrinkYoneda)

noncomputable def preservesLimitHomFamilyTgt (h : PLift (HasLimit F)) :=
  letI := h.down
  shrinkYoneda.obj (limit F).unop

noncomputable def preservesLimitHomFamily (h : PLift (HasLimit F)) :
    preservesLimitHomFamilySrc F ⟶ preservesLimitHomFamilyTgt F h :=
  letI := h.down
  coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)

lemma preservesLimit_eq_isLocal :
    ObjectProperty.preservesLimit F =
      (MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  ext G
  by_cases hF : HasLimit F
  · rw [preservesLimit_eq_isLocal_single (limit.isLimit F) (colimit.isColimit _)]
    convert Iff.rfl
    ext _ _ f
    exact ⟨fun ⟨_⟩ ↦ ⟨⟨⟩⟩, fun ⟨_⟩ ↦ ⟨⟨hF⟩⟩⟩
  · exact ⟨fun _ _ _ _ ⟨h⟩ ↦ (hF h.down).elim,
      fun _ ↦ ⟨fun hc ↦ (hF ⟨_, hc⟩).elim⟩⟩

lemma preservesLimitsOfShape_eq_isLocal :
    ObjectProperty.preservesLimitsOfShape J =
      (⨆ (F : J ⥤ Cᵒᵖ), MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  simp only [ObjectProperty.preservesLimitsOfShape_eq_iSup,
    MorphismProperty.isLocal_iSup, preservesLimit_eq_isLocal]

end

end Presheaf

end CategoryTheory
